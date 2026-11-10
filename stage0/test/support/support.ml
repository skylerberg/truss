open Harness

let module_of text : Path.module_ =
  match String.split_on_char ':' text |> List.filter (( <> ) "") with
  | package :: modules -> { package; modules }
  | [] -> invalid_arg text

(* The standard library as a fixed base, shared by every test in a run, so
   that it is checked once. *)
let standard = lazy (Database.standard_base ())

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
    (fun (d : Diagnostic.t) -> d.message)
    (Query.demand database Workspace.file module_).diagnostics

let codes diagnostics = List.map (fun (d : Diagnostic.t) -> Diagnostic.Code.name d.code) diagnostics

let checked ~check database name =
  let module_ = module_of name in
  (match parse_errors database module_ with
  | [] -> ()
  | errors -> fail "the test input does not parse: %s" (String.concat " " errors));
  check database module_

(* Fails the test if a core form breaks one of the invariants every core
   form has:

   - node ids are unique and less than [node_count];
   - no type contains an inference variable, a hole, or an error;
   - every generic parameter that appears is declared by the definition
     or by its enclosing type, trait, or impl, and never by a callee;
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
      | _ -> []
    in
    declared key.path
    @
    match Query.demand database Resolve.Names.container key with
    | Some container -> declared container.path
    | None -> []
  in
  let parameter what (found : T.parameter) =
    if not (List.mem found own) then
      wrong "%s mentions `%s`, a generic parameter of `%s`" what found.name (Path.show found.owner)
  in
  let capabilities what =
    List.iter (function
      | T.Capability _ -> ()
      | T.Capability_parameter found -> parameter what found
      | T.Capability_variable _ -> wrong "%s contains a capability inference variable" what)
  in
  let rec type_ what (found : T.ty) =
    match found with
    | Named { arguments; _ } | Cursor { arguments; _ } -> List.iter (argument what) arguments
    | Parameter named -> parameter what named
    | Projection { base; trait = reference; _ } ->
        type_ what base;
        trait what reference
    | Function { inputs; output; uses; _ } -> (
        List.iter (fun (_, input) -> type_ what input) inputs;
        capabilities what uses;
        match output with Returns given | Yields (_, given) | Lends (_, given) -> type_ what given)
    | Any reference -> trait what reference
    | Never | Integer -> ()
    | Variable _ | Literal _ | Hole | Error _ ->
        wrong "%s has the type `%s`, which is not fully inferred" what (T.show found)
  and argument what = function
    | T.Type given -> type_ what given
    | T.Value (Value_parameter named) -> parameter what named
    | T.Value (Known _) -> ()
    | T.Value (Value_variable _) -> wrong "%s contains a value inference variable" what
    | T.Capabilities set -> capabilities what set
  and trait what (reference : T.trait_reference) =
    List.iter (argument what) reference.trait_arguments;
    List.iter (fun (_, given) -> type_ what given) reference.associated
  in
  let seen = Hashtbl.create 64 in
  let unique id =
    if id < 0 || id >= form.node_count then wrong "the node id %d is out of range" id;
    if Hashtbl.mem seen id then wrong "the node id %d is used twice" id;
    Hashtbl.replace seen id ()
  in
  let callee (callee : Core.callee) =
    match callee with
    | Function { type_arguments; _ } -> List.iter (argument "a call's type argument") type_arguments
    | Trait_method { trait = reference; self_type; type_arguments; evidence; _ } -> (
        trait "a call's trait" reference;
        type_ "a call's `Self`" self_type;
        List.iter (argument "a call's type argument") type_arguments;
        match evidence with
        | Impl { arguments; _ } ->
            List.iter (fun (_, given) -> argument "an `impl`'s type argument" given) arguments
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
  let rec place (found : Core.place) =
    match found with
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
  let operand (found : Core.operand) =
    match found with Place found -> place found | Value _ -> ()
  in
  let rec mutable_place what (found : Core.place) =
    place found;
    match found with
    | Local _ | Temporary _ -> ()
    | Constant { path; _ } -> wrong "%s mutates the constant `%s`" what (Path.show path)
    | Field { base; _ } -> mutable_place what base
    | Lent { kind = Call { lends = Some Mut; _ }; _ } -> ()
    | Lent _ -> wrong "%s mutates a place that is lent read-only" what
  in
  (* The constructs that a [yield] yields: its operand, and each construct
     that is a field of one. Only they may have a field that is a place. A
     yielded construct that lends a place owns nothing, so every value that
     it takes has a [Plain] type. *)
  let yielded = Hashtbl.create 8 in
  let plain =
    let bounds parameter =
      match Query.demand database Interface.Environment.lowered key with
      | Some lowered -> Option.value ~default:[] (List.assoc_opt parameter lowered.bounds)
      | None -> []
    in
    Interface.Impls.plain database ~bounds
  in
  let rec yielded_operand ~lends (mode : T.mode) (part : Core.operand) =
    match part with
    | Place found -> if mode = Mut then mutable_place "a `yield mut`" found else place found
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
  let binds_own what (value : Core.operand) (pattern : Core.pattern) =
    operand value;
    match value with
    | Value _ ->
        if List.exists (fun (_, _, mode) -> mode <> T.Own) (bindings pattern) then
          wrong "%s on a value binds a name that is not `own`" what
    | Place _ -> ()
  in
  Core_walk.definition
    {
      expression =
        (fun (node : Core.expression) ->
          unique node.id;
          type_ "an expression" node.type_;
          match node.kind with
          | Use found -> place found
          | Construct { fields; _ } ->
              List.iter
                (fun (_, (field : Core.operand option)) ->
                  match field with
                  | Some (Place _) when not (Hashtbl.mem yielded node.id) ->
                      wrong "a construct that no `yield` yields has a field that is a place"
                  | _ -> ())
                fields
          | Cursor_next cursor -> mutable_place "a `Cursor_next`" cursor
          | Slice { base; call } -> (
              place base;
              match call.kind with
              | Call { arguments = Passed { value = Place first; _ } :: _; _ } when first == base ->
                  ()
              | _ -> wrong "the call of a `Slice` does not take the base as its first argument")
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
                  | Mut, Place found -> mutable_place "a `provide`" found
                  | _, value -> operand value)
                implementations
          | Call call ->
              callee call.callee;
              capabilities "a call's `uses`" call.uses;
              (match call.callee with Indirect function_value -> operand function_value | _ -> ());
              List.iter
                (function
                  | Core.Passed { mode = Mut; value = Value { kind = Slice { base; _ }; _ } } ->
                      mutable_place "a slice passed `mut`" base
                  | Core.Passed { mode = Mut; value = Value _ } ->
                      wrong "a `mut` parameter receives a value that is not a slice"
                  | Passed { mode = Mut; value = Place found } ->
                      mutable_place "a `mut` argument" found
                  | Passed { mode = Own; value = Place _ } ->
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
              | Bind { mutable_ = true; _ }, Place _ ->
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

(* Fails the test unless every file checks without a diagnostic and every
   core form satisfies [check_core_invariants]. *)
let no_diagnostics ~check files =
  let database = setup files in
  List.iter
    (fun (name, _) ->
      (match checked ~check database name with
      | [] -> ()
      | found ->
          fail "%s: %s" name
            (String.concat "; "
               (List.map
                  (fun (d : Diagnostic.t) -> Diagnostic.Code.name d.code ^ " " ^ d.message)
                  found)));
      ignore (check_module_core_invariants database (module_of name)))
    files

let one_diagnostic ~check ?(others = []) ?fixed text code =
  let database = setup (("app::main", text) :: others) in
  match checked ~check database "app::main" with
  | [ (diagnostic : Diagnostic.t) ] -> (
      let actual = Diagnostic.Code.name diagnostic.code in
      if actual <> code then fail "expected %s, got %s: %s" code actual diagnostic.message;
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
  | found ->
      fail "expected one %s, got [%s]" code
        (String.concat "; "
           (List.map
              (fun (d : Diagnostic.t) -> Diagnostic.Code.name d.code ^ " " ^ d.message)
              found))
