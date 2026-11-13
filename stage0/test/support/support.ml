open Harness

let module_of text : Path.module_ =
  match String.split_on_char ':' text |> List.filter (( <> ) "") with
  | name :: modules -> { package = { owner = None; name }; modules }
  | [] -> invalid_arg text

let top_key module_name name : Resolve.Names.key =
  let module_ = module_of module_name in
  { module_; path = Top { module_; name }; ordinal = 0 }

(* The standard library as a fixed base, shared by every test in a run, so
   that it is checked once. *)
let standard = lazy (Database.For_testing.standard_base ())

let setup files =
  let database = Engine.context (Engine.create ~log:true ~bases:[ Lazy.force standard ] ()) in
  let files = List.map (fun (name, text) -> (module_of name, text)) files in
  List.iter
    (fun package ->
      Database.load_package (Engine.of_context database) ~name:package ~dependencies:[]
        (List.filter (fun ((module_ : Path.module_), _) -> module_.package = package) files))
    (List.sort_uniq compare (List.map (fun ((module_ : Path.module_), _) -> module_.package) files));
  database

let parse_errors database module_ =
  List.map
    (fun (diagnostic : Diagnostic.t) -> diagnostic.message)
    (Query.demand database Workspace.file module_).diagnostics

let codes diagnostics =
  List.map (fun (diagnostic : Diagnostic.t) -> Diagnostic.Code.name diagnostic.code) diagnostics

let checked ~check database name =
  let module_ = module_of name in
  (match parse_errors database module_ with
  | [] -> ()
  | errors -> fail "the test input does not parse: %s" (String.concat " " errors));
  check database module_

(* Fails the test if a core form breaks one of the invariants every core
   form has:

   - node ids are unique;
   - no type contains an inference variable, a hole, or an error;
   - every generic parameter that appears is declared by the definition
     or by its enclosing type, trait, or impl, and never by a callee;
   - every associated capability set that appears is of a generic
     parameter or of an associated type of one;
   - the expression of a [Lent] place is a call of a lending method;
   - a [mut] parameter receives a place or a slice, and an [own] parameter
     receives a value;
   - a place that is assigned, passed [mut], or advanced as a cursor is
     mutable: it is not a constant, and every [Lent] place in it is lent
     [mut];
   - a [let], [match], or [is] on a value binds every name [own];
   - a [let] that binds a mutable local receives a value;
   - the alternatives of a pattern bind the same locals, with the same
     types and modes;
   - every use of a local has the type of the parameter or the pattern
     that binds it;
   - a [Yielding_call] is a call of a yielding method;
   - the call of a [Slice] takes the slice's base as its first argument. *)
let check_core_invariants database (key : Resolve.Names.key) (form : Core.t) =
  let module T = Types in
  let wrong format =
    Printf.ksprintf (fun message -> fail "%s: %s" (Resolve.Names.show_key key) message) format
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
    }
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
    {
      Core_walk.ignore_all with
      statement =
        (fun (node : Core.statement) ->
          match node.kind with
          | Yield { mode; part = Value { kind = Construct _; _ } as part } ->
              yielded_operand ~lends:(Core_walk.lent_places part <> []) mode part
          | Yield { mode; part } -> yielded_operand ~lends:false mode part
          | _ -> ());
    }
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
          | Call call ->
              callee call.callee;
              capabilities "a call's `uses`" call.uses;
              (match call.callee with Indirect function_value -> operand function_value | _ -> ());
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
                                            { arguments = Passed { value = Place base; _ } :: _; _ };
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
                  | Passed { value; _ } -> operand value
                  | Default -> ())
                call.arguments
          | _ -> ());
      statement =
        (fun (node : Core.statement) ->
          unique node.id;
          match node.kind with
          | Assign { target; _ } | Compound_assign { target; _ } ->
              mutable_place "an assignment" target
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
    }
    form.definition

(* Checks the core form of every definition in a module. Returns how many
   definitions had one. *)
let check_module_core_invariants database (module_ : Path.module_) =
  List.fold_left
    (fun count (declaration : Resolve.Names.declaration) ->
      let key = Resolve.Names.key_of declaration in
      match Query.demand database Infer.core key with
      | Some form ->
          check_core_invariants database key form;
          count + 1
      | None -> count)
    0
    (Query.demand database Resolve.Names.declarations module_)

type core_nodes = {
  expressions : Core.expression list;
  statements : Core.statement list;
  patterns : Core.pattern list;
}

let core_nodes database (key : Resolve.Names.key) : core_nodes =
  match Query.demand database Infer.core key with
  | None -> failwith (Printf.sprintf "%s has no core form" (Resolve.Names.show_key key))
  | Some form ->
      let expressions = ref [] and statements = ref [] and patterns = ref [] in
      Core_walk.definition
        {
          Core_walk.ignore_all with
          expression = (fun node -> expressions := node :: !expressions);
          statement = (fun node -> statements := node :: !statements);
          pattern = (fun node -> patterns := node :: !patterns);
        }
        form.definition;
      {
        expressions = List.rev !expressions;
        statements = List.rev !statements;
        patterns = List.rev !patterns;
      }

let first_core_nodes text =
  let database = setup [ ("app::main", text) ] in
  core_nodes database
    (Resolve.Names.key_of
       (List.hd (Query.demand database Resolve.Names.declarations (module_of "app::main"))))

(* Fails the test unless every file checks without a diagnostic and every
   core form satisfies [check_core_invariants]. *)
let no_diagnostics ~check files =
  let database = setup files in
  List.iter
    (fun (name, _) ->
      (match checked ~check database name with
      | [] -> ()
      | reported ->
          fail "%s: %s" name
            (String.concat "; "
               (List.map
                  (fun (diagnostic : Diagnostic.t) ->
                    Diagnostic.Code.name diagnostic.code ^ " " ^ diagnostic.message)
                  reported)));
      ignore (check_module_core_invariants database (module_of name)))
    files

let one_diagnostic ~check ?(setup = setup) ?(others = []) ?fixed ?says text code =
  let database = setup (("app::main", text) :: others) in
  match checked ~check database "app::main" with
  | [ (diagnostic : Diagnostic.t) ] -> (
      let actual = Diagnostic.Code.name diagnostic.code in
      if actual <> code then fail "expected %s, got %s: %s" code actual diagnostic.message;
      Option.iter
        (fun says ->
          if not (Substring.contains diagnostic.message says) then
            fail "expected a message that says %S, got: %s" says diagnostic.message)
        says;
      match (fixed, diagnostic.fixes) with
      | None, _ -> ()
      | Some _, [] -> fail "no fix"
      | Some expected, fix :: _ -> (
          let after = Diagnostic.apply_fix text fix in
          if after <> expected then fail "fixed to %S" after
          else
            let database = setup (("app::main", after) :: others) in
            match checked ~check database "app::main" with
            | [] -> ()
            | left -> fail "after the fix: %s" (String.concat "; " (codes left))))
  | reported ->
      fail "expected one %s, got [%s]" code
        (String.concat "; "
           (List.map
              (fun (diagnostic : Diagnostic.t) ->
                Diagnostic.Code.name diagnostic.code ^ " " ^ diagnostic.message)
              reported))

let record database responses =
  let engine = Engine.of_context database in
  List.iter (fun (key, response) -> Engine.set engine Prover.oracle_response key response) responses

let solver =
  lazy
    (match Solver.find () with
    | Ok solver -> solver
    | Error message ->
        prerr_endline message;
        exit 1)
