module Names = Names
module Parts = Parts
module Prelude = Prelude

type specification_function = Walk.specification_function = Log | Power | Time | Calls

type target = Walk.target =
  | Binding
  | Local of Syntax.id
  | Law_parameter of int
  | Type_parameter of Types.parameter
  | Capability_parameter of Types.parameter
  | Value_parameter of Types.parameter
  | Definition of Names.named * Path.t
  | Variant of Path.t * string
  | Module of Path.module_
  | Field of string
  | Result_value
  | Old
  | Identical
  | Yielded
  | Finished
  | Specification_function of specification_function
  | Unknown of Diagnostic.reported

type bracket = Walk.bracket = Index | Type_arguments | Method_bracket

type value = Walk.value =
  | Value_local of Syntax.id
  | Value_generic of Types.parameter
  | Value_field of string
  | Value_law_parameter of int

type resolved = {
  names : target option array;
  brackets : bracket option array;
  holes : (Syntax.id * (string * value) list) list;
  used_imports : string list;
  diagnostics : Syntax.diagnostic list;
}

type head = {
  name : Syntax.name;
  target : target;
  type_arguments : Syntax.bracket_item list option;
}

let rec head resolved (value : Syntax.expression) =
  match value.kind with
  | Name path ->
      Option.map
        (fun target -> { name = path.last; target; type_arguments = None })
        resolved.names.(path.last.id)
  | Parenthesized inner -> head resolved inner
  | Bracket (base, items) when resolved.brackets.(value.id) = Some Type_arguments ->
      Option.map
        (fun resolved_head -> { resolved_head with type_arguments = Some items })
        (head resolved base)
  | _ -> None

(* The name a definition declares, for reporting a duplicate. *)
let declared_name (definition : Syntax.definition) : Syntax.name option =
  match definition.kind with
  | Function { signature = { name = Plain_name name | Member_name (_, name); _ }; _ }
  | Method_declaration { name = Plain_name name | Member_name (_, name); _ }
  | Constant { name = Plain_name name | Member_name (_, name); _ }
  | Type_definition { name; _ }
  | Trait { name; _ }
  | Capability { name; _ }
  | Theorem { name; _ }
  | Law_proof { law = name; _ } ->
      Some name
  | Impl _ | Test _ | Definition_error _ -> None

let resolved =
  Query.query ~name:"resolved" ~phase:Phases.resolution ~show:Names.show_key ~saved:true
    ~about:(fun (key : Names.key) -> Some { path = key.path; part = Some "resolved" })
    (fun database (key : Names.key) ->
      match
        (Query.demand database Names.definition key, Query.demand database Names.file_of key)
      with
      | Some definition, Some file ->
          let module_ = key.module_ in
          let size = definition.id + 1 in
          let state : Walk.state =
            {
              database;
              file;
              names = Array.make size None;
              brackets = Array.make size None;
              diagnostics = [];
              holes = [];
              used_imports = [];
            }
          in
          let container =
            Option.bind (Query.demand database Names.container key) (fun (container : Names.key) ->
                Option.map
                  (fun definition -> (container.path, definition))
                  (Query.demand database Names.definition container))
          in
          (* No member of a definition whose own header did not parse is
             resolved, because its enclosing declaration is unknown. *)
          (match container with
          | Some (_, enclosing) when Parts.broken enclosing Header -> ()
          | _ -> Walk.definition state ~path:key.path ?container definition);
          (* The prelude is the same everywhere, so no definition outside the
             module that defines a prelude name may take it. *)
          (match key.path with
          | Top { name; _ } when List.mem name Prelude.names -> (
              let defines_it =
                match Prelude.find_type name with
                | Some prelude_module -> prelude_module = module_
                | None -> false
              in
              match declared_name definition with
              | Some declared when not defines_it ->
                  Walk.report state Hides_name declared.span
                    (Printf.sprintf
                       "`%s` is a name in the prelude, and a name cannot hide another. Choose \
                        another name."
                       name)
              | _ -> ())
          | _ -> ());
          if key.ordinal > 0 then begin
            let span =
              match declared_name definition with
              | Some name -> name.span
              | None -> Syntax.Span.make definition.span.start definition.span.start
            in
            let first =
              match Query.demand database Names.file_of { key with ordinal = 0 } with
              | Some first when first <> file -> Path.show_file first
              | _ -> "this file"
            in
            Walk.report state Duplicate_definition span
              (Printf.sprintf "%s is already defined in %s, so this definition is never used."
                 (Path.show key.path) first)
          end;
          Some
            {
              names = state.names;
              brackets = state.brackets;
              holes = List.rev state.holes;
              used_imports = List.sort compare state.used_imports;
              diagnostics =
                List.sort
                  (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
                    compare left.span right.span)
                  state.diagnostics;
            }
      | _ -> None)

(* The errors of a file's [use] lines, in the file's offsets: a module that
   does not exist, two imports with one last name, [standard::intrinsic]
   outside the standard library, and an import that no definition's module
   path begins with, with a fix that deletes it. A file where the parser
   recovered reports no unused import: resolution skips the broken parts,
   which may be what uses it. *)
let file_diagnostics =
  Query.query ~name:"file_diagnostics" ~phase:Phases.resolution ~show:Path.show_file ~saved:true
    (fun database (path : Path.file) ->
      let module_ = path.module_ in
      let file = Query.demand database Workspace.file path in
      let is_recovered (item : Syntax.definition Syntax.item) =
        match item.value with
        | { kind = Definition_error _; _ } -> true
        | { recovered; _ } -> recovered <> []
      in
      let has_recovery = List.exists is_recovered file.definitions in
      let used =
        List.concat_map
          (fun declaration ->
            match Query.demand database resolved (Names.key_of declaration) with
            | Some resolved -> resolved.used_imports
            | None -> [])
          (Query.demand database Names.declarations_in path)
      in
      let text = Source.text file.source in
      let diagnostics = ref [] in
      let report ?fixes code span message =
        diagnostics := Diagnostic.make ?fixes ~code:(Resolve code) span message :: !diagnostics
      in
      ignore
        (List.fold_left
           (fun seen (item : Syntax.path Syntax.item) ->
             let span = Source.span item.base (item.base + String.length item.text) in
             let used_module = Names.used_module database ~from:module_ item.value in
             let last = Names.last_name used_module in
             if used_module = Intrinsic.module_ && module_.package <> Path.standard_package then
               report Intrinsic_import span
                 "Only the `standard` package can use `standard::intrinsic`."
             else if not (Names.module_exists database used_module) then
               report Unknown_module span
                 (Printf.sprintf "No module `%s` exists." (Path.show_module used_module))
             else if List.mem last seen then
               report Duplicate_import span
                 (Printf.sprintf
                    "Another `use` already imports a module named `%s`. Write one of them by its \
                     full path instead."
                    last)
             else if (not has_recovery) && not (List.mem last used) then begin
               let stop = span.stop in
               let stop =
                 if stop < String.length text && text.[stop] = '\n' then stop + 1 else stop
               in
               report Unused_import span
                 ~fixes:
                   [
                     Diagnostic.fix "Delete the `use`."
                       [ Diagnostic.delete (Source.span item.base stop) ];
                   ]
                 (Printf.sprintf "Nothing in this file uses `%s`." (Path.show_module used_module))
             end;
             last :: seen)
           [] file.uses);
      List.rev !diagnostics)

let diagnostics database file =
  List.sort
    (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
      compare (left.span, left.code) (right.span, right.code))
    (Query.demand database file_diagnostics file
    @ Names.per_definition database file (fun key ->
        match Query.demand database resolved key with
        | Some resolved -> resolved.diagnostics
        | None -> []))
