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

(* What every core form holds to, so that a stage that reads one looks
   nothing up again and meets nothing the checker left undone:

   - each node has an id of its own, within the form's count;
   - every type is decided, with no unknown type and no unknown set of
     capabilities;
   - a generic parameter named anywhere is the definition's own, or one of
     what the definition is written inside: never the parameter of what is
     called, which a call replaces;
   - a place that is a lent part is a call that lends;
   - a parameter that changes its argument is given a place, or the slice
     through which part of one is changed, and one that takes its argument
     is given a value. *)
let form_holds database (key : Resolve.Names.key) (form : Core.t) =
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
      wrong "%s names `%s` of `%s`, a parameter of another definition" what found.name
        (Path.show found.owner)
  in
  let capabilities what =
    List.iter (function
      | T.Capability _ -> ()
      | T.Capability_parameter found -> parameter what found
      | T.Capability_variable _ -> wrong "%s holds an unknown set of capabilities" what)
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
        wrong "%s has the type `%s`, which is not decided" what (T.show found)
  and argument what = function
    | T.Type given -> type_ what given
    | T.Value (Value_parameter named) -> parameter what named
    | T.Value (Known _) -> ()
    | T.Value (Value_variable _) -> wrong "%s has a value that is not decided" what
    | T.Capabilities set -> capabilities what set
  and trait what (reference : T.trait_reference) =
    List.iter (argument what) reference.trait_arguments;
    List.iter (fun (_, given) -> type_ what given) reference.associated
  in
  let seen = Hashtbl.create 64 in
  let once id =
    if id < 0 || id >= form.nodes then wrong "the id %d is out of range" id;
    if Hashtbl.mem seen id then wrong "the id %d is used twice" id;
    Hashtbl.replace seen id ()
  in
  let callee (called : Core.callee) =
    match called with
    | Function { type_arguments; _ } -> List.iter (argument "a call's type argument") type_arguments
    | Trait_method { trait = reference; self_type; type_arguments; evidence; _ } -> (
        trait "a call's trait" reference;
        type_ "a call's `Self`" self_type;
        List.iter (argument "a call's type argument") type_arguments;
        match evidence with
        | Impl { arguments; _ } ->
            List.iter (fun (_, given) -> argument "what an `impl` is found with" given) arguments
        | Bound | Dynamic -> ())
    | Intrinsic { type_arguments; _ } ->
        List.iter (argument "an intrinsic's type argument") type_arguments
    | Capability_method _ | Value _ -> ()
  in
  let rec place (found : Core.place) =
    match found with
    | Lent { kind = Call { lends = Some _; _ }; _ } | Local _ | Temporary _ -> ()
    | Lent _ -> wrong "a lent part is not a call that lends"
    | Field { base; type_ = field; _ } ->
        type_ "a field" field;
        place base
  in
  Core_walk.parts
    {
      expression =
        (fun (node : Core.expression) ->
          once node.id;
          type_ "an expression" node.type_;
          match node.kind with
          | Use found | Next found -> place found
          | Function_value { type_arguments; _ } ->
              List.iter (argument "a function value's type argument") type_arguments
          | Generic_value named -> parameter "a value" named
          | Lambda { result; _ } -> type_ "what a lambda gives" result
          | Any { trait = reference; _ } -> trait "an `any`" reference
          | Provide { implementations; _ } ->
              List.iter
                (fun (implementation : Core.implementation) ->
                  type_ "an implementation" implementation.type_)
                implementations
          | Call { callee = called; arguments; uses; _ } ->
              callee called;
              capabilities "what a call needs" uses;
              List.iter
                (function
                  | Core.Passed { mode = Mut; value = Value { kind = Slice _; _ } } -> ()
                  | Core.Passed { mode = Mut; value = Value _ } ->
                      wrong "a value is passed where a place is changed"
                  | Passed { mode = Own; value = Place _ } ->
                      wrong "a place is passed where a value is taken"
                  | _ -> ())
                arguments
          | _ -> ());
      statement =
        (fun (node : Core.statement) ->
          once node.id;
          match node.kind with
          | Assign { target; _ } | Update { target; _ } -> place target
          | _ -> ());
      pattern =
        (fun (node : Core.pattern) ->
          once node.id;
          type_ "a pattern" node.type_);
      callee;
    }
    form.parts

(* Every core form a module's definitions have holds to what a form
   promises. *)
let forms_hold database (module_ : Path.module_) =
  List.fold_left
    (fun count (declaration : Resolve.Names.declaration) ->
      let key = Resolve.Names.key_of declaration in
      match Query.demand database Infer.core key with
      | Some form ->
          form_holds database key form;
          count + 1
      | None -> count)
    0
    (Query.demand database Resolve.Names.declarations module_)

(* A program a test accepts has no diagnostics, and each form its
   definitions have holds to what a form promises. *)
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
      ignore (forms_hold database (module_of name)))
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
