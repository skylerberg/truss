module Local_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Core.local
end))

let show_target : Core.operand Core.target -> string = function
  | Function { path; _ } -> Path.show path
  | Trait_method { trait; name; _ } -> Path.show trait.trait ^ "." ^ name
  | Capability_method { capability; name } -> Path.show capability ^ "." ^ name
  | Intrinsic { operation; _ } -> "intrinsic::" ^ Intrinsic.show_operation operation
  | Indirect _ -> "a function value"

let find_method_signature interface owner name receiver =
  Interface.Definition.find_declared_signature interface (Method { owner; name; receiver })

let find_declared_fields interface path arguments =
  Option.bind (Interface.Definition.find_type_interface interface path) (fun type_interface ->
      Types.instantiate_fields type_interface arguments)

let find_declared_variants interface path arguments =
  Option.bind (Interface.Definition.find_type_interface interface path) (fun type_interface ->
      Types.instantiate_variants type_interface arguments)

type context = {
  interface : Interface.Lookups.t;
  report : 'a. ('a, unit, string, unit) format4 -> 'a;
  at : Core.origin option ref;
  bounds : Interface.Impls.bounds;
}

let track_location at (visit : Core_walk.visit) : Core_walk.visit =
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

let excerpt text =
  let line = String.trim (String.take_first_while (fun character -> character <> '\n') text) in
  if String.length line > 60 then String.sub line 0 57 ^ "..." else line

let read_operand_type (operand : Core.operand) =
  match operand with
  | Place place -> Core_walk.compute_place_type place
  | Value value -> value.type_

let normalize_type context ty =
  Interface.Impls.normalize context.interface ~list_bounds:context.bounds ty

let fits context ~expected ~found =
  match found with
  | Types.Never -> true
  | _ -> Types.equal (normalize_type context expected) (normalize_type context found)

let make_substitution context generics arguments ~subject =
  if List.length generics = List.length arguments then Types.make_substitution generics arguments
  else begin
    context.report "%s has %d type arguments for %d generic parameters" subject
      (List.length arguments) (List.length generics);
    Types.no_substitution
  end

let make_capability_substitution context (signature : Types.signature) arguments ~subject =
  let parameters =
    List.sort compare
      (List.map
         (fun (parameter : Types.parameter) -> parameter.name)
         signature.capability_parameters)
  in
  if List.sort compare (List.map fst arguments) <> parameters then
    context.report "%s gives capability arguments for [%s], and its callee has [%s]" subject
      (String.concat ", " (List.map fst arguments))
      (String.concat ", " parameters);
  Types.make_capability_substitution signature.capability_parameters arguments

let instantiate context (target : Core.operand Core.target) =
  let subject = "a call of `" ^ show_target target ^ "`" in
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
  match target with
  | Function { path; instantiation } -> (
      match Interface.Impls.read_signature context.interface path with
      | Some signature ->
          of_signature
            (Types.combine_substitutions
               (make_substitution context signature.generics instantiation.type_arguments ~subject)
               (make_capability_substitution context signature instantiation.capability_arguments
                  ~subject))
            signature
      | None -> None)
  | Intrinsic { operation; type_arguments } ->
      let signature = Intrinsic_signatures.make_signature operation in
      of_signature (make_substitution context signature.generics type_arguments ~subject) signature
  | Trait_method { trait = reference; name; receiver; self_type; instantiation; _ } -> (
      match
        ( find_method_signature context.interface reference.trait name receiver,
          Interface.Definition.find_trait_interface context.interface reference.trait )
      with
      | Some signature, Some interface ->
          of_signature
            (Types.combine_substitutions
               (Types.make_trait_substitution interface.trait_generics ~self:self_type reference)
               (Types.combine_substitutions
                  (make_substitution context signature.generics instantiation.type_arguments
                     ~subject)
                  (make_capability_substitution context signature instantiation.capability_arguments
                     ~subject)))
            signature
      | _ -> None)
  | Capability_method { capability; name } -> (
      match find_method_signature context.interface capability name Static with
      | Some signature -> of_signature ~has_receiver:false Types.no_substitution signature
      | None -> None)
  | Indirect function_value -> (
      match read_operand_type function_value with
      | Function { inputs; output; _ } -> Some (List.map snd inputs, Types.Returns output)
      | _ -> None)

let check_call_types context (node : Core.expression) (call : Core.call) =
  let callee = show_target call.callee.target in
  match instantiate context call.callee.target with
  | None -> ()
  | Some (parameters, output) ->
      if List.length parameters = List.length call.arguments then
        List.iteri
          (fun position (expected, (argument : Core.argument)) ->
            match argument with
            | Passed { value; _ } ->
                let found = read_operand_type value in
                if not (fits context ~expected ~found) then
                  context.report
                    "argument %d of a call of `%s` has the type `%s`, and its parameter `%s`"
                    position callee (Types.show found) (Types.show expected)
            | Default -> ())
          (List.combine parameters call.arguments);
      let result = match output with Returns result | Lends (_, result) -> Some result in
      Option.iter
        (fun result ->
          if
            not
              (fits context ~expected:node.type_ ~found:result
              || fits context ~expected:result ~found:node.type_)
          then
            context.report "a call of `%s` has the type `%s`, and its callee returns `%s`" callee
              (Types.show node.type_) (Types.show result))
        result

let is_integer_trait path =
  List.exists
    (fun known -> Well_known.is known path)
    [ Fixed_width_integer; Signed_integer; Unsigned_integer ]

let is_built_in context (ty : Types.ty) =
  match ty with
  | Integer | Never -> true
  | Parameter ({ owner; _ } as parameter) ->
      (Types.is_self_parameter parameter && is_integer_trait owner)
      || List.exists
           (fun (bound : Types.trait_reference) -> is_integer_trait bound.trait)
           (context.bounds parameter)
  | Projection { trait; _ } -> is_integer_trait trait.trait
  | _ -> Option.is_some (Types.find_builtin ty)

let check_operator_types context (node : Core.expression) (operation : Intrinsic.scalar) arguments =
  if not (is_built_in context node.type_) then
    context.report "an operator has the type `%s`, which is not built in" (Types.show node.type_);
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
        context.report "an operand of `%s` has the type `%s`, and the operator `%s`"
          (Intrinsic.show_operation (Scalar operation))
          (Types.show operand.type_) (Types.show node.type_))
    operands

let compare_types context (left : Core.expression) (right : Core.expression) =
  if
    not
      (fits context ~expected:left.type_ ~found:right.type_
      || fits context ~expected:right.type_ ~found:left.type_)
  then
    context.report "a comparison compares the type `%s` with `%s`" (Types.show left.type_)
      (Types.show right.type_)
  else if not (is_built_in context left.type_ && is_built_in context right.type_) then
    context.report "a `Compare` compares the type `%s`, which is not built in"
      (Types.show left.type_)

let construct_fields context (node : Core.expression) variant fields =
  match node.type_ with
  | Named { path; arguments } -> (
      let declared =
        match variant with
        | None -> find_declared_fields context.interface path arguments
        | Some name ->
            Option.map
              (fun (variant : Types.variant) -> Option.value ~default:[] variant.fields)
              (Option.bind
                 (find_declared_variants context.interface path arguments)
                 (List.find_opt (fun (declared : Types.variant) -> declared.variant_name = name)))
      in
      let type_name = Types.show node.type_ in
      match declared with
      | None when fields = [] && Option.is_some (Types.find_builtin node.type_) -> ()
      | None -> context.report "a construct of `%s` names no record or variant" type_name
      | Some declared ->
          let names = List.map fst fields in
          if
            List.sort compare names
            <> List.sort compare (List.map (fun (field : Types.field) -> field.field_name) declared)
          then
            context.report "a construct of `%s` lists the fields %s" type_name
              (String.concat ", " names);
          let rec is_given_then_omitted = function
            | (_, None) :: (_, Some _) :: _ -> false
            | _ :: rest -> is_given_then_omitted rest
            | [] -> true
          in
          if not (is_given_then_omitted fields) then
            context.report "a construct of `%s` lists an omitted field before a given one" type_name;
          List.iter
            (fun (name, (operand : Core.operand option)) ->
              match
                ( List.find_opt (fun (field : Types.field) -> field.field_name = name) declared,
                  operand )
              with
              | Some field, Some operand ->
                  let found = read_operand_type operand in
                  if not (fits context ~expected:field.field_type ~found) then
                    context.report
                      "the field `%s` of a construct of `%s` has the type `%s`, and is declared \
                       `%s`"
                      name type_name (Types.show found) (Types.show field.field_type)
              | Some field, None ->
                  if not field.field_has_default then
                    context.report "a construct of `%s` omits `%s`, which has no default" type_name
                      name
              | None, _ -> ())
            fields)
  | _ ->
      context.report "a construct has the type `%s`, which is not a named type"
        (Types.show node.type_)

let list_free_locals (parameters : Core.pattern list) (body : Core.block) =
  let bound = Local_table.create 8 and read = ref [] in
  let bind_pattern (pattern : Core.pattern) =
    match pattern.kind with Bind { local; _ } -> Local_table.replace bound local () | _ -> ()
  in
  let visit =
    {
      Core_walk.ignore_all with
      pattern = bind_pattern;
      statement =
        (fun (node : Core.statement) ->
          match node.kind with
          | Compound_assign { bound = local; _ } -> Local_table.replace bound local ()
          | _ -> ());
      expression =
        (fun (node : Core.expression) ->
          match node.kind with
          | Quantified { binder = Over_type { local; _ }; _ } -> Local_table.replace bound local ()
          | _ -> ());
    }
  in
  List.iter (fun pattern -> (Core_walk.make_deep_visitor visit).pattern pattern) parameters;
  Core_walk.walk_block (Core_walk.make_deep_visitor visit) body;
  Core_walk.walk_block
    (Core_walk.make_deep_visitor
       {
         Core_walk.ignore_all with
         place =
           (fun (place : Core.place) ->
             match place with
             | Local { local; _ } when not (Local_table.mem bound local || List.mem local !read) ->
                 read := local :: !read
             | _ -> ());
       })
    body;
  List.rev !read

let check_semantics context (form : Core.t) =
  Core_walk.walk_definition
    (track_location context.at
       {
         Core_walk.ignore_all with
         expression =
           (fun (node : Core.expression) ->
             match node.kind with
             | Call call -> (
                 check_call_types context node call;
                 match call.callee.target with
                 | Trait_method { trait; self_type; _ }
                   when List.exists
                          (fun known -> Well_known.is known trait.trait)
                          [ Add; Subtract; Multiply; Divide; Remainder; Negate ]
                        && Option.is_some (Types.find_builtin self_type) ->
                     context.report
                       "an arithmetic operator on `%s` is a call of `%s`, not an Operator"
                       (Types.show self_type) (show_target call.callee.target)
                 | Trait_method { self_type = Any _; evidence = Impl _ | Bound; _ } ->
                     context.report "a call of `%s` on an `any` value is not dynamic"
                       (show_target call.callee.target)
                 | Trait_method { self_type; evidence = Dynamic; _ }
                   when match self_type with Any _ -> false | _ -> true ->
                     context.report "a call of `%s` on `%s` is dynamic"
                       (show_target call.callee.target) (Types.show self_type)
                 | _ -> ())
             | To_any { evidence = Dynamic; _ } ->
                 context.report "a conversion to `any` has dynamic evidence"
             | Operator { operation; arguments } ->
                 check_operator_types context node operation arguments
             | Compare { left; right; _ } -> compare_types context left right
             | Construct { variant; fields } -> construct_fields context node variant fields
             | Lambda { parameters; captures; body; _ } ->
                 let free = list_free_locals parameters body in
                 if List.map (fun (capture : Core.capture) -> capture.local) captures <> free then
                   context.report
                     "a lambda captures %d locals, and its body reads %d of the enclosing \
                      function's"
                     (List.length captures) (List.length free)
             | Slice { callee; bounds; _ } ->
                 let name = show_target callee.target in
                 let ends suffix =
                   String.length name >= String.length suffix
                   && String.sub name
                        (String.length name - String.length suffix)
                        (String.length suffix)
                      = suffix
                 in
                 if
                   not
                     (match List.length bounds with
                     | 2 -> ends ".slice_range"
                     | 1 -> ends ".slice_from"
                     | _ -> false)
                 then context.report "a `Slice` with %d bounds calls `%s`" (List.length bounds) name
             | _ -> ());
       })
    form.definition

let check_form (interface : Interface.Lookups.t) ~(path : Path.t) ~(key : Resolve.Names.key option)
    (form : Core.t) =
  let list_bounds parameter =
    let of_key key =
      Option.value ~default:[]
        (List.assoc_opt parameter (interface.read_elaborated_interface key).scope.bounds)
    in
    match key with
    | Some key ->
        of_key key @ Option.fold ~none:[] ~some:of_key (interface.names.find_container key)
    | None -> []
  in
  let normalize = Interface.Impls.normalize interface ~list_bounds in
  let at = ref None in
  let name = match key with Some key -> Resolve.Names.show_key key | None -> Path.show path in
  let source =
    lazy
      (Option.map (fun key -> (interface.names.read_spans key, interface.names.read_text key)) key)
  in
  let quote () =
    match (!at, Lazy.force source) with
    | Some origin, Some (spans, text) when origin >= 0 && origin < Array.length spans ->
        let span : Source.Definition_span.t = spans.(origin) in
        Printf.sprintf ", in `%s`" (excerpt (String.sub text span.start (span.stop - span.start)))
    | _ -> ""
  in
  let report format =
    Printf.ksprintf (fun message -> Harness.fail "%s: %s%s" name message (quote ())) format
  in
  let own =
    let of_generics = List.map (fun (generic : Types.generic) -> generic.generic) in
    let list_declared path =
      match Interface.Definition.find_interface interface path with
      | Some (Function_interface signature | Theorem_interface signature) ->
          of_generics signature.generics
      | Some (Type_interface interface) -> of_generics interface.type_generics
      | Some (Trait_interface interface) ->
          Types.make_self_parameter path :: of_generics interface.trait_generics
      | Some (Impl_interface interface) -> of_generics interface.impl_generics
      | Some (Law_proof_interface interface) -> of_generics interface.generics
      | _ -> []
    in
    list_declared path
    @ (match Interface.Impls.read_signature interface path with
      | Some signature -> of_generics signature.generics
      | None -> [])
    @
    match Option.bind key interface.names.find_container with
    | Some container -> list_declared container.path
    | None -> []
  in
  let own_capability_parameters =
    match Interface.Impls.read_signature interface path with
    | Some signature -> signature.capability_parameters
    | None -> []
  in
  let check_parameter subject (mentioned : Types.parameter) =
    if not (List.mem mentioned own) then
      report "%s mentions `%s`, a generic parameter of `%s`" subject mentioned.name
        (Path.show mentioned.owner)
  in
  let check_capability_parameter subject (mentioned : Types.parameter) =
    if not (List.mem mentioned own_capability_parameters) then
      report "%s mentions `generic %s`, a capability parameter of `%s`" subject mentioned.name
        (Path.show mentioned.owner)
  in
  let rec check_capabilities subject (set : Types.capability_set) =
    List.iter
      (function
        | Types.Capability _ -> ()
        | Types.Capability_parameter mentioned -> check_capability_parameter subject mentioned
        | Types.Capability_projection { base; trait = reference; name } ->
            (match base with
            | Parameter _ | Projection _ -> ()
            | _ ->
                report "%s contains `%s.%s`, which is not normalized" subject (Types.show base) name);
            check_type subject base;
            check_trait subject reference
        | Types.Capability_variable _ ->
            report "%s contains a capability inference variable" subject
        | Types.Capability_error _ -> report "%s contains a capability with an error" subject)
      (Types.list_capabilities set)
  and check_type subject (ty : Types.ty) =
    match ty with
    | Named { arguments; _ } -> List.iter (check_argument subject) arguments
    | Parameter named -> check_parameter subject named
    | Projection { base; trait = reference; _ } ->
        check_type subject base;
        check_trait subject reference
    | Function { inputs; output; uses; _ } ->
        List.iter (fun (_, input) -> check_type subject input) inputs;
        check_capabilities subject uses;
        check_type subject output
    | Any reference -> check_trait subject reference
    | Never | Integer -> ()
    | Variable _ | Literal _ | Hole | Error _ ->
        report "%s has the type `%s`, which is not fully inferred" subject (Types.show ty)
  and check_argument subject = function
    | Types.Type inner -> check_type subject inner
    | Types.Value (Value_parameter named) -> check_parameter subject named
    | Types.Value (Known _) -> ()
    | Types.Value (Value_variable _) -> report "%s contains a value inference variable" subject
  and check_trait subject (reference : Types.trait_reference) =
    List.iter (check_argument subject) reference.trait_arguments;
    List.iter (fun (_, inner) -> check_type subject inner) reference.associated
  in
  let seen = Hashtbl.create 64 in
  let check_unique id =
    if Hashtbl.mem seen id then report "the node id %d is used twice" id;
    Hashtbl.replace seen id ()
  in
  let task_origins = Hashtbl.create 4 in
  let check_unique_task_origin (node : Core.statement) =
    match node.kind with
    | Concurrent _ | For { mode = Concurrent_loop; _ } ->
        if Hashtbl.mem task_origins node.origin then
          report
            "two `concurrent` statements have the origin %d, so an early exit of a task of one \
             would end the tasks of the other"
            node.origin;
        Hashtbl.replace task_origins node.origin ()
    | _ -> ()
  in
  let check_instantiation subject (instantiation : Types.instantiation) =
    List.iter (check_argument (subject ^ "'s type argument")) instantiation.type_arguments;
    List.iter
      (fun (_, argument) -> check_capabilities (subject ^ "'s capability argument") argument)
      instantiation.capability_arguments
  in
  let check_target (target : Core.operand Core.target) =
    match target with
    | Function { instantiation; _ } -> check_instantiation "a call" instantiation
    | Trait_method { trait = reference; self_type; instantiation; evidence; _ } -> (
        check_trait "a call's trait" reference;
        check_type "a call's `Self`" self_type;
        check_instantiation "a call" instantiation;
        match evidence with
        | Impl { substitution; _ } ->
            List.iter
              (fun (_, inner) -> check_argument "an `impl`'s type argument" inner)
              (Types.For_testing.list_arguments substitution)
        | Bound | Dynamic -> ())
    | Intrinsic { type_arguments; _ } ->
        List.iter (check_argument "an intrinsic's type argument") type_arguments
    | Capability_method _ | Indirect _ -> ()
  in
  let find_parameters (target : Core.operand Core.target) : (Types.mode * bool) list option =
    let of_signature ~has_receiver (signature : Types.signature) =
      let receiver =
        match signature.receiver with
        | Some (((Read | Mut | Own) as receiver), _) when has_receiver ->
            [
              ((match receiver with Read -> Types.Read | Mut -> Mut | Own | Static -> Own), false);
            ]
        | _ -> []
      in
      receiver
      @ List.map
          (fun (parameter : Types.parameter_info) -> (parameter.mode, parameter.has_default))
          signature.parameters
    in
    match target with
    | Function { path; _ } ->
        Option.map (of_signature ~has_receiver:true) (Interface.Impls.read_signature interface path)
    | Trait_method { trait = reference; name; receiver; _ } ->
        Option.map (of_signature ~has_receiver:true)
          (find_method_signature interface reference.trait name receiver)
    | Capability_method { capability; name } ->
        Option.map
          (of_signature ~has_receiver:false)
          (find_method_signature interface capability name Static)
    | Intrinsic { operation; _ } ->
        Some (of_signature ~has_receiver:true (Intrinsic_signatures.make_signature operation))
    | Indirect function_value -> (
        let function_type =
          match function_value with
          | Place core_place -> Core_walk.compute_place_type core_place
          | Value value -> value.type_
        in
        match function_type with
        | Function { inputs; _ } -> Some (List.map (fun (mode, _) -> (mode, false)) inputs)
        | _ -> None)
  in
  let check_arguments_fit (call : Core.call) =
    let callee = show_target call.callee.target in
    match find_parameters call.callee.target with
    | None -> report "a call of `%s` has a callee with no signature" callee
    | Some parameters when List.length parameters <> List.length call.arguments ->
        report "a call of `%s` has %d arguments for %d parameters" callee
          (List.length call.arguments) (List.length parameters)
    | Some parameters ->
        List.iteri
          (fun position ((mode, has_default), (argument : Core.argument)) ->
            match argument with
            | Passed { mode = passed; _ } when passed <> mode ->
                report "argument %d of a call of `%s` has the mode `%s`, and its parameter `%s`"
                  position callee (Types.show_mode passed) (Types.show_mode mode)
            | Default when not has_default ->
                report "a call of `%s` omits argument %d, whose parameter has no default" callee
                  position
            | Passed _ | Default -> ())
          (List.combine parameters call.arguments)
  in
  let compound_assignments = ref 0 and current_targets = ref 0 in
  let local_types : Types.ty Local_table.t = Local_table.create 16 in
  let check_parameters =
    List.iter (fun (parameter : Core.parameter) ->
        Local_table.replace local_types parameter.local parameter.type_)
  in
  (match form.definition with
  | Function { parameters = declared; _ } -> check_parameters declared
  | Trait laws -> List.iter (fun (law : Core.law) -> check_parameters law.parameters) laws
  | Type _ | Constant _ | Test _ | Law_proof _ | Empty -> ());
  Core_walk.walk_definition
    (track_location at
       {
         Core_walk.ignore_all with
         expression =
           (fun (node : Core.expression) ->
             match node.kind with
             | Quantified { binder = Over_type { local; type_; _ }; _ } ->
                 Local_table.replace local_types local type_
             | _ -> ());
         pattern =
           (fun (node : Core.pattern) ->
             match node.kind with
             | Bind { local; _ } -> Local_table.replace local_types local node.type_
             | _ -> ());
       })
    form.definition;
  let rec check_place (core_place : Core.place) =
    match core_place with
    | Local { local; type_ = used; _ } -> (
        check_type "a local" used;
        match Local_table.find_opt local_types local with
        | Some bound when not (Types.equal (normalize bound) (normalize used)) ->
            report "a local is used with the type `%s` and bound with the type `%s`"
              (Types.show used) (Types.show bound)
        | _ -> ())
    | Constant { type_ = constant; _ } -> check_type "a constant" constant
    | Lent { kind = Call { lends = Some _; _ }; _ } | Temporary _ -> ()
    | Lent _ -> report "a `Lent` place is not a call of a lending method"
    | Field { base; type_ = field; _ } ->
        check_type "a field" field;
        check_place base
  in
  let check_operand (core_operand : Core.operand) =
    match core_operand with Place core_place -> check_place core_place | Value _ -> ()
  in
  let rec check_mutable_place subject (core_place : Core.place) =
    check_place core_place;
    match core_place with
    | Local _ | Temporary _ -> ()
    | Constant { path; _ } -> report "%s mutates the constant `%s`" subject (Path.show path)
    | Field { base; _ } -> check_mutable_place subject base
    | Lent { kind = Call { lends = Some Mut; _ }; _ } -> ()
    | Lent _ -> report "%s mutates a place that is lent read-only" subject
  in
  let yielded = Hashtbl.create 8 in
  let rec check_yielded_operand (mode : Types.mode) (part : Core.operand) =
    match part with
    | Place core_place ->
        if mode = Mut then check_mutable_place "a `Yield` with the mode `mut`" core_place
        else check_place core_place
    | Value ({ kind = Construct { fields; _ }; _ } as node) ->
        Hashtbl.replace yielded node.id ();
        List.iter (fun (_, field) -> Option.iter (check_yielded_operand mode) field) fields
    | Value _ -> ()
  in
  Core_walk.walk_definition
    (track_location at
       {
         Core_walk.ignore_all with
         statement =
           (fun (node : Core.statement) ->
             match node.kind with
             | Yield { mode; part } -> check_yielded_operand mode part
             | _ -> ());
       })
    form.definition;
  let rec list_bindings (pattern : Core.pattern) : (Core.local * Types.ty * Types.mode) list =
    match pattern.kind with
    | Bind { local; mode; _ } -> [ (local, pattern.type_, mode) ]
    | Variant { fields; _ } | Record fields ->
        List.concat_map (fun (_, inner) -> list_bindings inner) fields
    | Alternatives (first :: _) -> list_bindings first
    | Alternatives [] | Wildcard | Literal _ | Range _ | Equal_to _ -> []
  in
  let check_binds_own subject (value : Core.operand) (pattern : Core.pattern) =
    check_operand value;
    match value with
    | Value _ ->
        if List.exists (fun (_, _, mode) -> mode <> Types.Own) (list_bindings pattern) then
          report "%s on a value binds a name that is not `own`" subject
    | Place _ -> ()
  in
  Core_walk.walk_definition
    (track_location at
       {
         expression =
           (fun (node : Core.expression) ->
             check_unique node.id;
             check_type "an expression" node.type_;
             match node.kind with
             | Use core_place -> check_place core_place
             | Construct { fields; _ } ->
                 List.iter
                   (fun (_, (field : Core.operand option)) ->
                     match field with
                     | Some (Place _) when not (Hashtbl.mem yielded node.id) ->
                         report "a construct that no `Yield` lends has a field that is a place"
                     | _ -> ())
                   fields
             | Slice { base; callee; bounds } ->
                 check_place base;
                 check_arguments_fit
                   {
                     callee;
                     arguments = Passed { mode = Read; value = Place base } :: bounds;
                     lends = None;
                   }
             | Matches { value; pattern } -> check_binds_own "an `is`" value pattern
             | Match { scrutinees; arms; _ } ->
                 List.iter
                   (fun (arm : Core.arm) ->
                     if List.length arm.patterns <> List.length scrutinees then
                       report "a `match` arm does not have one pattern per scrutinee";
                     List.iter2 (check_binds_own "a `match`") scrutinees arm.patterns)
                   arms
             | Function_value { instantiation; _ } ->
                 check_instantiation "a function value" instantiation
             | Value_parameter named -> check_parameter "a value" named
             | Method_cost { method_; _ } -> check_target method_
             | Lambda { result; captures; _ } ->
                 check_type "a lambda's result" result;
                 List.iter
                   (fun ({ local; type_ } : Core.capture) ->
                     check_place (Local { local; type_; origin = node.origin }))
                   captures
             | To_any { trait = reference; _ } -> check_trait "a conversion to `any`" reference
             | Provide { implementations; _ } ->
                 List.iter
                   (fun (implementation : Core.implementation) ->
                     check_type "an implementation" implementation.type_;
                     match (implementation.mode, implementation.value) with
                     | Mut, Place core_place -> check_mutable_place "a `provide`" core_place
                     | _, value -> check_operand value)
                   implementations
             | Current_target -> incr current_targets
             | Call call ->
                 check_arguments_fit call;
                 (match call.callee.target with
                 | Indirect function_value -> check_operand function_value
                 | _ -> ());
                 List.iter
                   (function
                     | Core.Passed { mode = Mut; value = Value { kind = Slice { base; _ }; _ }; _ }
                       ->
                         check_mutable_place "a slice passed `mut`" base
                     | Core.Passed { mode = Mut; value = Value _; _ } ->
                         report "a `mut` parameter receives a value that is not a slice"
                     | Passed { mode = Mut; value = Place core_place; _ } ->
                         check_mutable_place "a `mut` argument" core_place
                     | Passed { mode = Own; value = Place _; _ } ->
                         report "an `own` parameter receives a place"
                     | Passed { mode = Read; value = Value { kind = Use _; _ }; _ } ->
                         report
                           "a read-only parameter of `%s` receives a `Use`, which moves or copies \
                            the place"
                           (show_target call.callee.target)
                     | Passed { value; _ } -> check_operand value
                     | Default -> ())
                   call.arguments
             | _ -> ());
         statement =
           (fun (node : Core.statement) ->
             check_unique node.id;
             check_unique_task_origin node;
             match node.kind with
             | Assign { target; _ } -> check_mutable_place "an assignment" target
             | Compound_assign { target; value; _ } -> (
                 check_mutable_place "an assignment" target;
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
                     report
                       "a compound assignment's new value is not an operation on `Current_target`")
             | Let { pattern; value; _ } -> (
                 check_binds_own "a `let`" value pattern;
                 match (pattern.kind, value) with
                 | Bind { is_var = true; _ }, Place _ ->
                     report "a `let` that binds a mutable local receives a place"
                 | _ -> ())
             | For { iteration = Cursor { cursor; _ }; _ } ->
                 check_mutable_place "a `for` loop" cursor
             | For { iteration = Elements { count; position; element }; _ } -> (
                 (match count.kind with
                 | Call _ -> ()
                 | _ -> report "the count of an `Elements` loop is not a call");
                 (match position.kind with
                 | Bind _ -> ()
                 | _ -> report "the position of an `Elements` loop is not a `Bind`");
                 match element with
                 | Lent { kind = Call _; _ } -> ()
                 | _ -> report "the element of an `Elements` loop is not the lent place of a call")
             | _ -> ());
         pattern =
           (fun (node : Core.pattern) ->
             check_unique node.id;
             check_type "a pattern" node.type_;
             match node.kind with
             | Alternatives (first :: rest) ->
                 let list_bound alternative = List.sort compare (list_bindings alternative) in
                 let expected = list_bound first in
                 if List.exists (fun alternative -> list_bound alternative <> expected) rest then
                   report "the alternatives of a pattern do not bind the same locals"
             | _ -> ());
         callee =
           (fun callee ->
             check_target callee.target;
             check_capabilities "a callee's `uses`" callee.uses);
         place = ignore;
       })
    form.definition;
  at := None;
  if !current_targets <> !compound_assignments then
    report "`Current_target` appears %d times in %d compound assignments" !current_targets
      !compound_assignments;
  at := None;
  check_semantics { interface; report; at; bounds = list_bounds } form

let check interface (key : Resolve.Names.key) form =
  check_form interface ~path:key.path ~key:(Some key) form

let check_derived interface path form = check_form interface ~path ~key:None form

let check_file (interface : Interface.Lookups.t) ~find_core (file : Path.file) =
  List.fold_left
    (fun count (declaration : Resolve.Names.declaration) ->
      let key = declaration.key in
      match find_core key with
      | Some form ->
          check interface key form;
          count + 1
      | None -> count)
    0
    (interface.names.list_declarations_in file)
