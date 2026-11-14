open Harness

let callee_name : Core.callee -> string = function
  | Function { path; _ } -> Path.show path
  | Trait_method { trait; name; _ } -> Path.show trait.trait ^ "." ^ name
  | Capability_method { capability; name } -> Path.show capability ^ "." ^ name
  | Intrinsic { operation; _ } -> "intrinsic::" ^ Intrinsic.operation_name operation
  | Indirect _ -> "a function value"

(* The checks of types, of which code is a specification, and of what a
   lambda captures. *)

type context = {
  database : Query.context;
  wrong : 'a. ('a, unit, string, unit) format4 -> 'a;
  at : Core.origin option ref;  (** The origin of the node being checked, which [wrong] quotes. *)
  bounds : Interface.Impls.bounds;
}

(* A visitor that records the origin of each node in [at] before it checks
   the node. *)
let located at (visit : Core_walk.visit) : Core_walk.visit =
  {
    visit with
    expression =
      (fun (node : Core.expression) ->
        at := Some node.origin;
        visit.expression node);
    statement =
      (fun (node : Core.statement) ->
        at := Some node.origin;
        visit.statement node);
    pattern =
      (fun (node : Core.pattern) ->
        at := Some node.origin;
        visit.pattern node);
  }

(* The first line of a node's source text, cut to a length that fits in a
   message. *)
let excerpt text =
  let line =
    match String.index_opt text '\n' with Some stop -> String.sub text 0 stop | None -> text
  in
  let line = String.trim line in
  if String.length line > 60 then String.sub line 0 57 ^ "..." else line

let operand_type (operand : Core.operand) =
  match operand with Place place -> Core_walk.place_type place | Value value -> value.type_

let normal context ty = Interface.Impls.normalize context.database ~bounds:context.bounds ty

(* Whether a value of the type [found] fits where [expected] is: the types
   are equal once normalized, or [found] is [Never]. *)
let fits context ~expected ~found =
  match found with
  | Types.Never -> true
  | _ -> Types.equal (normal context expected) (normal context found)

let substitution context generics arguments ~subject =
  match Types.substitution_of generics arguments with
  | Some substitution -> substitution
  | None ->
      context.wrong "%s has %d type arguments for %d generic parameters" subject
        (List.length arguments) (List.length generics);
      []

(* The types of a callee's parameters, a method's receiver first, and its
   result, with the call's type arguments substituted. *)
let instantiated context (callee : Core.callee) =
  let subject = "a call of `" ^ callee_name callee ^ "`" in
  let of_signature ?(has_receiver = true) substitution (signature : Types.signature) =
    let signature = Types.substitute_signature substitution signature in
    let receiver =
      match signature.receiver with
      | Some ((Read | Mut | Own), receiver) when has_receiver -> [ receiver ]
      | _ -> []
    in
    Some
      ( receiver
        @ List.map (fun (parameter : Types.parameter_info) -> parameter.type_) signature.parameters,
        signature.output )
  in
  match callee with
  | Function { path; type_arguments } -> (
      match Interface.Impls.signature context.database path with
      | Some signature ->
          of_signature (substitution context signature.generics type_arguments ~subject) signature
      | None -> None)
  | Intrinsic { operation; type_arguments } ->
      let signature = Intrinsic_signatures.signature operation in
      of_signature (substitution context signature.generics type_arguments ~subject) signature
  | Trait_method { trait = reference; name; receiver; self_type; type_arguments; _ } -> (
      match
        ( Infer.Members.trait_method context.database reference.trait name receiver,
          Query.demand context.database Interface.Environment.trait_interface reference.trait )
      with
      | Some method_, Some interface ->
          let signature = method_.method_signature in
          of_signature
            (Interface.Properties.trait_substitution interface ~self:self_type reference
            @ substitution context signature.generics type_arguments ~subject)
            signature
      | _ -> None)
  | Capability_method { capability; name } -> (
      match Infer.Members.trait_methods context.database capability name with
      | [ method_ ] -> of_signature ~has_receiver:false [] method_.method_signature
      | _ -> None)
  | Indirect function_value -> (
      match operand_type function_value with
      | Function { inputs; output; _ } -> Some (List.map snd inputs, output)
      | _ -> None)

let call_types context (node : Core.expression) (call : Core.call) =
  let callee = callee_name call.callee in
  match instantiated context call.callee with
  | None -> ()
  | Some (parameters, output) ->
      if List.length parameters = List.length call.arguments then
        List.iteri
          (fun position (expected, (argument : Core.argument)) ->
            match argument with
            | Passed { value; _ } ->
                let found = operand_type value in
                if not (fits context ~expected ~found) then
                  context.wrong
                    "argument %d of a call of `%s` has the type `%s`, and its parameter `%s`"
                    position callee (Types.show found) (Types.show expected)
            | Default -> ())
          (List.combine parameters call.arguments);
      let result =
        match output with Returns result | Lends (_, result) -> Some result | Yields _ -> None
      in
      Option.iter
        (fun result ->
          if
            not
              (fits context ~expected:node.type_ ~found:result
              || fits context ~expected:result ~found:node.type_)
          then
            context.wrong "a call of `%s` has the type `%s`, and its callee returns `%s`" callee
              (Types.show node.type_) (Types.show result))
        result

let is_integer_trait path =
  List.exists
    (fun known -> Well_known.is known path)
    [ Fixed_width_integer; Signed_integer; Unsigned_integer ]

(* Whether a type is built in, or is a built-in integer for every
   instantiation: a parameter that an integer trait bounds, [Self] in an
   integer trait, or an associated type of one. *)
let is_built_in context (ty : Types.ty) =
  match ty with
  | Integer | Never -> true
  | Parameter ({ owner; name } as parameter) ->
      (name = "Self" && is_integer_trait owner)
      || List.exists
           (fun (bound : Types.trait_reference) -> is_integer_trait bound.trait)
           (context.bounds parameter)
  | Projection { trait; _ } -> is_integer_trait trait.trait
  | _ -> Option.is_some (Types.builtin_of ty)

let operator_types context (node : Core.expression) (operation : Intrinsic.operation) arguments =
  if not (is_built_in context node.type_) then
    context.wrong "an operator has the type `%s`, which is not built in" (Types.show node.type_);
  let operands =
    match (operation, arguments) with
    | ( ( Add | Subtract | Multiply | Divide | Remainder | Wrapping_add | Wrapping_subtract
        | Wrapping_multiply | Bit_and | Bit_or | Bit_xor ),
        [ left; right ] ) ->
        [ left; right ]
    | (Negate | Complement), [ operand ] -> [ operand ]
    | (Shift_left | Shift_right), [ shifted; _ ] -> [ shifted ]
    | _ -> []
  in
  List.iter
    (fun (operand : Core.expression) ->
      if not (fits context ~expected:node.type_ ~found:operand.type_) then
        context.wrong "an operand of `%s` has the type `%s`, and the operator `%s`"
          (Intrinsic.operation_name operation)
          (Types.show operand.type_) (Types.show node.type_))
    operands

let compare_types context (left : Core.expression) (right : Core.expression) =
  if
    not
      (fits context ~expected:left.type_ ~found:right.type_
      || fits context ~expected:right.type_ ~found:left.type_)
  then
    context.wrong "a comparison compares the type `%s` with `%s`" (Types.show left.type_)
      (Types.show right.type_)
  else if not (is_built_in context left.type_ && is_built_in context right.type_) then
    context.wrong "a `Compare` compares the type `%s`, which is not built in"
      (Types.show left.type_)

(* A construct lists each field of its record or variant once: the fields
   the code gives, each with the field's type, and then the omitted fields,
   each of which has a default. *)
let construct_fields context (node : Core.expression) variant fields =
  match node.type_ with
  | Named { path; arguments } -> (
      let declared =
        match variant with
        | None -> Infer.Members.fields context.database path arguments
        | Some name ->
            Option.map
              (fun (variant : Types.variant) -> Option.value ~default:[] variant.fields)
              (Option.bind
                 (Infer.Members.variants context.database path arguments)
                 (List.find_opt (fun (declared : Types.variant) -> declared.variant_name = name)))
      in
      let type_name = Types.show node.type_ in
      match declared with
      | None when fields = [] && Option.is_some (Types.builtin_of node.type_) -> ()
      | None -> context.wrong "a construct of `%s` names no record or variant" type_name
      | Some declared ->
          let names = List.map fst fields in
          if
            List.sort compare names
            <> List.sort compare (List.map (fun (field : Types.field) -> field.field_name) declared)
          then
            context.wrong "a construct of `%s` lists the fields %s" type_name
              (String.concat ", " names);
          let rec given_then_omitted = function
            | (_, None) :: (_, Some _) :: _ -> false
            | _ :: rest -> given_then_omitted rest
            | [] -> true
          in
          if not (given_then_omitted fields) then
            context.wrong "a construct of `%s` lists an omitted field before a given one" type_name;
          List.iter
            (fun (name, (operand : Core.operand option)) ->
              match
                ( List.find_opt (fun (field : Types.field) -> field.field_name = name) declared,
                  operand )
              with
              | Some field, Some operand ->
                  let found = operand_type operand in
                  if not (fits context ~expected:field.field_type ~found) then
                    context.wrong
                      "the field `%s` of a construct of `%s` has the type `%s`, and is declared \
                       `%s`"
                      name type_name (Types.show found) (Types.show field.field_type)
              | Some field, None ->
                  if not field.field_has_default then
                    context.wrong "a construct of `%s` omits `%s`, which has no default" type_name
                      name
              | None, _ -> ())
            fields)
  | _ ->
      context.wrong "a construct has the type `%s`, which is not a named type"
        (Types.show node.type_)

(* The locals of the enclosing function that a lambda reads, in order of
   first use: every local its body uses that the lambda does not bind. *)
let free_locals (parameters : Core.pattern list) (body : Core.block) =
  let bound = Hashtbl.create 8 and read = ref [] in
  let bind_pattern (pattern : Core.pattern) =
    match pattern.kind with Bind { local; _ } -> Hashtbl.replace bound local () | _ -> ()
  in
  let visit =
    {
      Core_walk.ignore_all with
      pattern = bind_pattern;
      statement =
        (fun (node : Core.statement) ->
          match node.kind with
          | Compound_assign { bound = local; _ } -> Hashtbl.replace bound local ()
          | _ -> ());
      expression =
        (fun (node : Core.expression) ->
          match node.kind with
          | Quantified { binder = Over_type { local; _ }; _ } -> Hashtbl.replace bound local ()
          | _ -> ());
    }
  in
  List.iter (fun pattern -> (Core_walk.deep visit).pattern pattern) parameters;
  Core_walk.block (Core_walk.deep visit) body;
  Core_walk.block
    (Core_walk.deep
       {
         Core_walk.ignore_all with
         place =
           (fun (place : Core.place) ->
             match place with
             | Local { local; _ } when not (Hashtbl.mem bound local || List.mem local !read) ->
                 read := local :: !read
             | _ -> ());
       })
    body;
  List.rev !read

(* Whether a condition can be evaluated at run time: it has no quantifier,
   no value of type [Integer], no [old] or [result], and no call of a
   specification-only function. *)
let is_executable context (condition : Core.expression) =
  not
    (Core_walk.expression_exists
       ~expression:(fun (node : Core.expression) ->
         Types.equal node.type_ Integer
         ||
         match node.kind with
         | Quantified _ | Old _ | Result | Specification_function _ | Method_time _ -> true
         | Call { callee = Function { path; _ }; _ } -> (
             match Interface.Impls.signature context.database path with
             | Some signature -> signature.specification_only
             | None -> false)
         | _ -> false)
       condition)

(* The ids of the expressions that only a specification holds: the
   contract, the type's invariants, the laws, [proof] blocks, assertions
   outside a test, and loop clauses. *)
let specification_expressions (definition : Core.definition) =
  let ids = Hashtbl.create 64 in
  let mark =
    Core_walk.deep
      {
        Core_walk.ignore_all with
        expression = (fun (node : Core.expression) -> Hashtbl.replace ids node.id ());
      }
  in
  let cost (spent : Core.cost) =
    match spent.bound with
    | Finite -> ()
    | Order_of bound | At_most bound | Exactly bound -> mark.expression bound
  in
  (match definition with
  | Function { parameters; contract; _ } ->
      List.iter
        (fun (parameter : Core.parameter) ->
          Option.iter
            (fun (contract : Core.callback_contract) -> List.iter mark.expression contract.requires)
            parameter.callback_contract)
        parameters;
      List.iter
        (fun (condition : Core.condition) -> mark.expression condition.value)
        contract.requires;
      List.iter mark.expression contract.ensures;
      List.iter mark.expression contract.decreases;
      List.iter cost contract.costs
  | Type { invariants; potential; _ } ->
      List.iter mark.expression invariants;
      Option.iter mark.expression potential
  | Trait laws ->
      List.iter
        (fun (law : Core.law) ->
          List.iter mark.expression law.requires;
          Core_walk.block mark law.body)
        laws
  | Constant _ | Test _ | Law_proof _ | Empty -> ());
  Core_walk.definition
    {
      Core_walk.ignore_all with
      statement =
        (fun (node : Core.statement) ->
          match node.kind with
          | Proof body -> Core_walk.block mark body
          | Assert { condition; _ } -> (
              (* A test runs its assertions. *)
              match definition with
              | Test _ -> ()
              | _ -> mark.expression condition.value)
          | For { clauses; _ } | While { clauses; _ } ->
              List.iter (Core_walk.loop_clause mark) clauses
          | _ -> ());
    }
    definition;
  ids

let check_semantics context (form : Core.t) =
  let in_specification = specification_expressions form.definition in
  let executable subject (condition : Core.condition) =
    if condition.executable <> is_executable context condition.value then
      context.wrong "%s is marked %sexecutable" subject
        (if condition.executable then "" else "not ")
  in
  (match form.definition with
  | Function { contract; _ } -> List.iter (executable "a `requires` clause") contract.requires
  | _ -> ());
  Core_walk.definition
    (located context.at
       {
         Core_walk.ignore_all with
         statement =
           (fun (node : Core.statement) ->
             match node.kind with
             | Assert { condition; _ } -> executable "an `assert`" condition
             | _ -> ());
         expression =
           (fun (node : Core.expression) ->
             match node.kind with
             | Call call -> (
                 call_types context node call;
                 match call.callee with
                 | Trait_method { trait; self_type; _ }
                   when List.exists
                          (fun known -> Well_known.is known trait.trait)
                          [ Add; Subtract; Multiply; Divide; Remainder; Negate ]
                        && Option.is_some (Types.builtin_of self_type) ->
                     context.wrong
                       "an arithmetic operator on `%s` is a call of `%s`, not an Operator"
                       (Types.show self_type) (callee_name call.callee)
                 | Trait_method { self_type = Any _; evidence = Impl _ | Bound; _ } ->
                     context.wrong "a call of `%s` on an `any` value is not dynamic"
                       (callee_name call.callee)
                 | Trait_method { self_type; evidence = Dynamic; _ }
                   when match self_type with Any _ -> false | _ -> true ->
                     context.wrong "a call of `%s` on `%s` is dynamic" (callee_name call.callee)
                       (Types.show self_type)
                 | _ -> ())
             | To_any { evidence = Dynamic; _ } ->
                 context.wrong "a conversion to `any` has dynamic evidence"
             | Operator { operation; arguments } -> operator_types context node operation arguments
             | Compare { left; right; _ } -> compare_types context left right
             | Construct { variant; fields } -> construct_fields context node variant fields
             | Lambda { parameters; captures; body; _ } ->
                 let free = free_locals parameters body in
                 if List.map (fun (capture : Core.capture) -> capture.local) captures <> free then
                   context.wrong
                     "a lambda captures %d locals, and its body reads %d of the enclosing \
                      function's"
                     (List.length captures) (List.length free)
             | Quantified { binder = Over_each _; _ } when Hashtbl.mem in_specification node.id ->
                 context.wrong "a quantifier in a specification runs as a loop (`Over_each`)"
             | Quantified { binder = Over_collection _; _ }
               when not (Hashtbl.mem in_specification node.id) ->
                 context.wrong "a quantifier in executable code is over a mathematical collection"
             | Slice { call = { kind = Call ({ arguments; _ } as call); _ } } ->
                 let name = callee_name call.callee in
                 let ends suffix =
                   String.length name >= String.length suffix
                   && String.sub name
                        (String.length name - String.length suffix)
                        (String.length suffix)
                      = suffix
                 in
                 if
                   not
                     (match List.length arguments with
                     | 3 -> ends ".slice_range"
                     | 2 -> ends ".slice_from"
                     | _ -> false)
                 then
                   context.wrong "a `Slice` with %d arguments calls `%s`" (List.length arguments)
                     name
             | _ -> ());
       })
    form.definition

let check database (key : Resolve.Names.key) (form : Core.t) =
  let module T = Types in
  let at = ref None in
  let source =
    lazy
      (match
         ( Query.demand database Resolve.Names.spans key,
           Query.demand database Resolve.Names.text key )
       with
      | Some spans, Some text -> Some (spans, text)
      | _ -> None)
  in
  let quoted () =
    match (!at, Lazy.force source) with
    | Some origin, Some (spans, text) when origin >= 0 && origin < Array.length spans ->
        let span : Syntax.span = spans.(origin) in
        Printf.sprintf ", in `%s`" (excerpt (String.sub text span.start (span.stop - span.start)))
    | _ -> ""
  in
  let wrong format =
    Printf.ksprintf
      (fun message -> fail "%s: %s%s" (Resolve.Names.show_key key) message (quoted ()))
      format
  in
  let own =
    let of_generics = List.map (fun (generic : T.generic) -> generic.generic) in
    let declared path =
      match Query.demand database Interface.Environment.interface path with
      | Some (Function_interface signature | Theorem_interface signature) ->
          of_generics signature.generics
      | Some (Type_interface interface) -> of_generics interface.type_generics
      | Some (Trait_interface interface) ->
          { T.owner = path; name = "Self" } :: of_generics interface.trait_generics
      | Some (Impl_interface interface) -> of_generics interface.impl_generics
      | Some (Law_proof_interface interface) -> of_generics interface.generics
      | _ -> []
    in
    declared key.path
    (* A derived method has no interface of its own: its signature gives
       the generics of the type and of the trait method. *)
    @ (match Interface.Impls.signature database key.path with
      | Some signature -> of_generics signature.generics
      | None -> [])
    @
    match Query.demand database Resolve.Names.container key with
    | Some container -> declared container.path
    | None -> []
  in
  let parameter subject (mentioned : T.parameter) =
    if not (List.mem mentioned own) then
      wrong "%s mentions `%s`, a generic parameter of `%s`" subject mentioned.name
        (Path.show mentioned.owner)
  in
  let rec capabilities subject (set : T.capability_set) =
    List.iter
      (function
        | T.Capability _ -> ()
        | T.Capability_parameter mentioned -> parameter subject mentioned
        | T.Capability_projection { base; trait = reference; name } ->
            (match base with
            | Parameter _ | Projection _ -> ()
            | _ -> wrong "%s contains `%s.%s`, which is not normalized" subject (T.show base) name);
            type_ subject base;
            trait subject reference
        | T.Capability_variable _ -> wrong "%s contains a capability inference variable" subject)
      (set :> T.capability list)
  and type_ subject (ty : T.ty) =
    match ty with
    | Named { arguments; _ } | Cursor { arguments; _ } -> List.iter (argument subject) arguments
    | Parameter named -> parameter subject named
    | Projection { base; trait = reference; _ } ->
        type_ subject base;
        trait subject reference
    | Function { inputs; output; uses; _ } ->
        List.iter (fun (_, input) -> type_ subject input) inputs;
        capabilities subject uses;
        type_ subject (Types.result_type output)
    | Any reference -> trait subject reference
    | Never | Integer -> ()
    | Variable _ | Literal _ | Hole | Error _ ->
        wrong "%s has the type `%s`, which is not fully inferred" subject (T.show ty)
  and argument subject = function
    | T.Type inner -> type_ subject inner
    | T.Value (Value_parameter named) -> parameter subject named
    | T.Value (Known _) -> ()
    | T.Value (Value_variable _) -> wrong "%s contains a value inference variable" subject
    | T.Capabilities set -> capabilities subject set
  and trait subject (reference : T.trait_reference) =
    List.iter (argument subject) reference.trait_arguments;
    List.iter (fun (_, inner) -> type_ subject inner) reference.associated
  in
  let seen = Hashtbl.create 64 in
  let unique id =
    if Hashtbl.mem seen id then wrong "the node id %d is used twice" id;
    Hashtbl.replace seen id ()
  in
  let callee (callee : Core.callee) =
    match callee with
    | Function { type_arguments; _ } -> List.iter (argument "a call's type argument") type_arguments
    | Trait_method { trait = reference; name; self_type; type_arguments; evidence; _ } -> (
        trait "a call's trait" reference;
        type_ "a call's `Self`" self_type;
        List.iter (argument "a call's type argument") type_arguments;
        match evidence with
        | Impl { impl; arguments } ->
            (* The [next] of a yielding method's cursor is a [Cursor_next]. *)
            if name = "next" && Option.is_some (Interface.Impls.cursor_of_impl impl) then
              wrong "the `next` of a yielding method's cursor is a call";
            List.iter (fun (_, inner) -> argument "an `impl`'s type argument" inner) arguments
        | Bound | Dynamic -> ())
    | Intrinsic { type_arguments; _ } ->
        List.iter (argument "an intrinsic's type argument") type_arguments
    | Capability_method _ | Indirect _ -> ()
  in
  (* Each parameter of a callee, a method's receiver first, with its mode
     and whether it has a default. [None] if the callee has no signature. *)
  let callee_parameters (callee : Core.callee) : (T.mode * bool) list option =
    let of_signature ~has_receiver (signature : T.signature) =
      let receiver =
        match signature.receiver with
        | Some (((Read | Mut | Own) as receiver), _) when has_receiver ->
            [ ((match receiver with Read -> T.Read | Mut -> Mut | Own | Static -> Own), false) ]
        | _ -> []
      in
      receiver
      @ List.map
          (fun (parameter : T.parameter_info) -> (parameter.mode, parameter.has_default))
          signature.parameters
    in
    match callee with
    | Function { path; _ } ->
        Option.map (of_signature ~has_receiver:true) (Interface.Impls.signature database path)
    | Trait_method { trait = reference; name; receiver; _ } ->
        Option.map
          (fun (method_ : T.trait_method) ->
            of_signature ~has_receiver:true method_.method_signature)
          (Infer.Members.trait_method database reference.trait name receiver)
    | Capability_method { capability; name } -> (
        (* A capability method's receiver is the capability, which no
           argument passes. *)
        match Infer.Members.trait_methods database capability name with
        | [ method_ ] -> Some (of_signature ~has_receiver:false method_.method_signature)
        | _ -> None)
    | Intrinsic { operation; _ } ->
        Some (of_signature ~has_receiver:true (Intrinsic_signatures.signature operation))
    | Indirect function_value -> (
        let function_type =
          match function_value with
          | Place core_place -> Core_walk.place_type core_place
          | Value value -> value.type_
        in
        match function_type with
        | Function { inputs; _ } -> Some (List.map (fun (mode, _) -> (mode, false)) inputs)
        | _ -> None)
  in
  let arguments_fit (call : Core.call) =
    let callee = callee_name call.callee in
    match callee_parameters call.callee with
    | None -> wrong "a call of `%s` has a callee with no signature" callee
    | Some parameters when List.length parameters <> List.length call.arguments ->
        wrong "a call of `%s` has %d arguments for %d parameters" callee
          (List.length call.arguments) (List.length parameters)
    | Some parameters ->
        List.iteri
          (fun position ((mode, has_default), (argument : Core.argument)) ->
            match argument with
            | Passed { mode = passed; _ } when passed <> mode ->
                wrong "argument %d of a call of `%s` has the mode `%s`, and its parameter `%s`"
                  position callee (T.show_mode passed) (T.show_mode mode)
            | Default when not has_default ->
                wrong "a call of `%s` omits argument %d, whose parameter has no default" callee
                  position
            | Passed _ | Default -> ())
          (List.combine parameters call.arguments)
  in
  let compound_assignments = ref 0 and current_targets = ref 0 in
  (* The calls that create a [Slice], whose bounds are passed as values. *)
  let slice_calls = Hashtbl.create 8 in
  let local_types : (Core.local, T.ty) Hashtbl.t = Hashtbl.create 16 in
  let parameters =
    List.iter (fun (parameter : Core.parameter) ->
        Hashtbl.replace local_types parameter.local parameter.type_)
  in
  (match form.definition with
  | Function { parameters = declared; _ } -> parameters declared
  | Trait laws -> List.iter (fun (law : Core.law) -> parameters law.parameters) laws
  | Type _ | Constant _ | Test _ | Law_proof _ | Empty -> ());
  Core_walk.definition
    (located at
       {
         Core_walk.ignore_all with
         expression =
           (fun (node : Core.expression) ->
             match node.kind with
             | Quantified { binder = Over_type { local; type_; _ }; _ } ->
                 Hashtbl.replace local_types local type_
             | _ -> ());
         pattern =
           (fun (node : Core.pattern) ->
             match node.kind with
             | Bind { local; _ } -> Hashtbl.replace local_types local node.type_
             | _ -> ());
       })
    form.definition;
  let rec place (core_place : Core.place) =
    match core_place with
    | Local { local; type_ = used; _ } -> (
        type_ "a local" used;
        match Hashtbl.find_opt local_types local with
        | Some bound when not (T.equal bound used) ->
            wrong "a local is used with the type `%s` and bound with the type `%s`" (T.show used)
              (T.show bound)
        | _ -> ())
    | Constant { type_ = constant; _ } -> type_ "a constant" constant
    | Lent { kind = Call { lends = Some _; _ }; _ } | Temporary _ -> ()
    | Lent _ -> wrong "a `Lent` place is not a call of a lending method"
    | Field { base; type_ = field; _ } ->
        type_ "a field" field;
        place base
  in
  let operand (core_operand : Core.operand) =
    match core_operand with Place core_place -> place core_place | Value _ -> ()
  in
  let rec mutable_place subject (core_place : Core.place) =
    place core_place;
    match core_place with
    | Local _ | Temporary _ -> ()
    | Constant { path; _ } -> wrong "%s mutates the constant `%s`" subject (Path.show path)
    | Field { base; _ } -> mutable_place subject base
    | Lent { kind = Call { lends = Some Mut; _ }; _ } -> ()
    | Lent _ -> wrong "%s mutates a place that is lent read-only" subject
  in
  (* The constructs that a [yield] yields: its operand, and each construct
     that is a field of one. Only they may have a field that is a place. A
     yielded construct that lends a place owns nothing, so every value that
     it takes has a [Plain] type. *)
  let yielded = Hashtbl.create 8 in
  let plain =
    let bounds parameter =
      match Query.demand database Interface.Environment.lowered_interface key with
      | Some lowered -> Option.value ~default:[] (List.assoc_opt parameter lowered.bounds)
      | None -> []
    in
    Interface.Impls.plain database ~bounds
  in
  let rec yielded_operand ~lends (mode : T.mode) (part : Core.operand) =
    match part with
    | Place core_place ->
        if mode = Mut then mutable_place "a `yield mut`" core_place else place core_place
    | Value ({ kind = Construct { fields; _ }; _ } as node) ->
        Hashtbl.replace yielded node.id ();
        List.iter (fun (_, field) -> Option.iter (yielded_operand ~lends mode) field) fields
    | Value value ->
        if lends && not (plain value.type_) then
          wrong "a yielded construct that lends a place takes a value of the type `%s`"
            (T.show value.type_)
  in
  Core_walk.definition
    (located at
       {
         Core_walk.ignore_all with
         statement =
           (fun (node : Core.statement) ->
             match node.kind with
             | Yield { mode; part = Value { kind = Construct _; _ } as part } ->
                 yielded_operand ~lends:(Core_walk.lent_places part <> []) mode part
             | Yield { mode; part } -> yielded_operand ~lends:false mode part
             | _ -> ());
       })
    form.definition;
  let rec bindings (pattern : Core.pattern) : (Core.local * T.ty * T.mode) list =
    match pattern.kind with
    | Bind { local; mode; _ } -> [ (local, pattern.type_, mode) ]
    | Variant { fields; _ } | Record fields ->
        List.concat_map (fun (_, inner) -> bindings inner) fields
    | Alternatives (first :: _) -> bindings first
    | Alternatives [] | Wildcard | Literal _ | Range _ | Equal_to _ -> []
  in
  let binds_own subject (value : Core.operand) (pattern : Core.pattern) =
    operand value;
    match value with
    | Value _ ->
        if List.exists (fun (_, _, mode) -> mode <> T.Own) (bindings pattern) then
          wrong "%s on a value binds a name that is not `own`" subject
    | Place _ -> ()
  in
  Core_walk.definition
    (located at
       {
         expression =
           (fun (node : Core.expression) ->
             unique node.id;
             type_ "an expression" node.type_;
             match node.kind with
             | Use core_place -> place core_place
             | Quantified { binder = Over_each { call; _ }; _ } -> (
                 match call.kind with
                 | Call { arguments = [ Passed { mode = Read; _ } ]; _ } -> ()
                 | _ -> wrong "an `Over_each` does not hold a read-only call with one argument")
             | Construct { fields; _ } ->
                 List.iter
                   (fun (_, (field : Core.operand option)) ->
                     match field with
                     | Some (Place _) when not (Hashtbl.mem yielded node.id) ->
                         wrong "a construct that no `yield` yields has a field that is a place"
                     | _ -> ())
                   fields
             | Cursor_next cursor -> mutable_place "a `Cursor_next`" cursor
             | Slice { call } -> (
                 Hashtbl.replace slice_calls call.id ();
                 match call.kind with
                 | Call
                     {
                       arguments =
                         Passed { value = Place base; _ } :: Passed { value = Value _; _ } :: rest;
                       _;
                     }
                   when List.length rest <= 1 ->
                     place base
                 | _ -> wrong "the call of a `Slice` does not take its base and then its bounds")
             | Matches { value; pattern } -> binds_own "an `is`" value pattern
             | Match { scrutinees; arms; _ } ->
                 List.iter
                   (fun (arm : Core.arm) ->
                     if List.length arm.patterns <> List.length scrutinees then
                       wrong "a `match` arm does not have one pattern per scrutinee";
                     List.iter2 (binds_own "a `match`") scrutinees arm.patterns)
                   arms
             | Function_value { type_arguments; _ } ->
                 List.iter (argument "a function value's type argument") type_arguments
             | Value_parameter named -> parameter "a value" named
             | Method_time method_ -> callee method_
             | Lambda { result; captures; _ } ->
                 type_ "a lambda's result" result;
                 List.iter
                   (fun ({ local; type_ } : Core.capture) ->
                     place (Local { local; type_; origin = node.origin }))
                   captures
             | To_any { trait = reference; _ } -> trait "a conversion to `any`" reference
             | Provide { implementations; _ } ->
                 List.iter
                   (fun (implementation : Core.implementation) ->
                     type_ "an implementation" implementation.type_;
                     match (implementation.mode, implementation.value) with
                     | Mut, Place core_place -> mutable_place "a `provide`" core_place
                     | _, value -> operand value)
                   implementations
             | Current_target -> incr current_targets
             | Call call ->
                 arguments_fit call;
                 callee call.callee;
                 capabilities "a call's `uses`" call.uses;
                 (match call.callee with
                 | Indirect function_value -> operand function_value
                 | _ -> ());
                 List.iter
                   (function
                     | Core.Passed
                         {
                           mode = Mut;
                           value =
                             Value
                               {
                                 kind =
                                   Slice
                                     {
                                       call =
                                         {
                                           kind =
                                             Call
                                               {
                                                 arguments = Passed { value = Place base; _ } :: _;
                                                 _;
                                               };
                                           _;
                                         };
                                     };
                                 _;
                               };
                           _;
                         } ->
                         mutable_place "a slice passed `mut`" base
                     | Core.Passed { mode = Mut; value = Value _; _ } ->
                         wrong "a `mut` parameter receives a value that is not a slice"
                     | Passed { mode = Mut; value = Place core_place; _ } ->
                         mutable_place "a `mut` argument" core_place
                     | Passed { mode = Own; value = Place _; _ } ->
                         wrong "an `own` parameter receives a place"
                     | Passed { mode = Read; value = Value { kind = Use _; _ }; _ }
                       when not (Hashtbl.mem slice_calls node.id) ->
                         wrong
                           "a read-only parameter of `%s` receives a `Use`, which moves or copies \
                            the place"
                           (callee_name call.callee)
                     | Passed { value; _ } -> operand value
                     | Default -> ())
                   call.arguments
             | _ -> ());
         statement =
           (fun (node : Core.statement) ->
             unique node.id;
             match node.kind with
             | Assign { target; _ } -> mutable_place "an assignment" target
             | Compound_assign { target; value; _ } -> (
                 mutable_place "an assignment" target;
                 incr compound_assignments;
                 match value.kind with
                 | Operator { arguments = { kind = Current_target; _ } :: _; _ }
                 | Call
                     {
                       arguments = Passed { value = Value { kind = Current_target; _ }; _ } :: _;
                       _;
                     } ->
                     ()
                 | _ ->
                     wrong
                       "a compound assignment's new value is not an operation on `Current_target`")
             | Let { pattern; value; _ } -> (
                 binds_own "a `let`" value pattern;
                 match (pattern.kind, value) with
                 | Bind { is_var = true; _ }, Place _ ->
                     wrong "a `let` that binds a mutable local receives a place"
                 | _ -> ())
             | For { iteration = Cursor { cursor; _ }; _ } -> mutable_place "a `for` loop" cursor
             | For { iteration = Yielding_call { kind = Call { callee; _ }; _ }; _ } -> (
                 let output =
                   match callee with
                   | Function { path; _ } ->
                       Option.map
                         (fun (signature : T.signature) -> signature.output)
                         (Interface.Impls.signature database path)
                   | Trait_method { trait = reference; name; receiver; _ } ->
                       Option.map
                         (fun (method_ : T.trait_method) -> method_.method_signature.output)
                         (Infer.Members.trait_method database reference.trait name receiver)
                   | Capability_method _ | Intrinsic _ | Indirect _ -> None
                 in
                 match output with
                 | Some (Yields _) -> ()
                 | _ -> wrong "a `Yielding_call` calls a method that does not yield")
             | For { iteration = Yielding_call _; _ } -> wrong "a `Yielding_call` is not a call"
             | _ -> ());
         pattern =
           (fun (node : Core.pattern) ->
             unique node.id;
             type_ "a pattern" node.type_;
             match node.kind with
             | Alternatives (first :: rest) ->
                 let bound alternative = List.sort compare (bindings alternative) in
                 let expected = bound first in
                 if List.exists (fun alternative -> bound alternative <> expected) rest then
                   wrong "the alternatives of a pattern do not bind the same locals"
             | _ -> ());
         callee;
         place = ignore;
       })
    form.definition;
  at := None;
  if !current_targets <> !compound_assignments then
    wrong "`Current_target` appears %d times in %d compound assignments" !current_targets
      !compound_assignments;
  let bounds parameter =
    let of_key key =
      match Query.demand database Interface.Environment.lowered_interface key with
      | Some lowered -> Option.value ~default:[] (List.assoc_opt parameter lowered.bounds)
      | None -> []
    in
    of_key key
    @ Option.fold ~none:[] ~some:of_key (Query.demand database Resolve.Names.container key)
  in
  at := None;
  check_semantics { database; wrong; at; bounds } form

let check_file database (file : Path.file) =
  List.fold_left
    (fun count (declaration : Resolve.Names.declaration) ->
      let key = Resolve.Names.key_of declaration in
      match Query.demand database Infer.core key with
      | Some form ->
          check database key form;
          count + 1
      | None -> count)
    0
    (Query.demand database Resolve.Names.declarations_in file)
