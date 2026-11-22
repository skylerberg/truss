module Names = Names
module Namespace = Namespace
module Parts = Parts
module Prelude = Prelude

type specification_function = Walk.specification_function =
  | Log
  | Power
  | Call_cost of Language.Metric.t
  | Calls

type module_path = Walk.module_path = {
  module_ : Path.module_;
  imported : Path.module_ option;
  last_name : Syntax.name;
}

type target = Walk.target =
  | Binding
  | Local of Syntax.id
  | Law_parameter of int
  | Type_parameter of Types.parameter
  | Capability_parameter of Types.parameter
  | Value_parameter of Types.parameter
  | Definition of Names.named * Path.t
  | Variant of Path.t * string
  | Module of module_path
  | Field of string
  | Result_value
  | Old
  | Identical
  | Visited
  | Final
  | Specification_function of specification_function
  | Unknown of Diagnostic.reported

type bracket = Walk.bracket = Index | Type_arguments | Method_bracket
type section = Walk.section = Interface | Contract | Body

type value = Walk.value =
  | Value_local of Syntax.id
  | Value_generic of Types.parameter
  | Value_field of string
  | Value_law_parameter of int

type resolved = {
  names : target option array;
  brackets : bracket option array;
  holes : (Syntax.id * (string * value) list) list;
}

type resolution = { resolved : resolved; used_imports : string list }

let sections = [ Interface; Contract; Body ]

let merge = function
  | [] -> { names = [||]; brackets = [||]; holes = [] }
  | first :: _ as parts ->
      let pick select index = List.find_map (fun part -> (select part).(index)) parts in
      {
        names = Array.init (Array.length first.names) (pick (fun part -> part.names));
        brackets = Array.init (Array.length first.brackets) (pick (fun part -> part.brackets));
        holes = List.concat_map (fun part -> part.holes) parts;
      }

let list_referenced_definitions resolved =
  List.sort_uniq Path.compare
    (List.filter_map
       (function Some (Definition (_, path) | Variant (path, _)) -> Some path | _ -> None)
       (Array.to_list resolved.names))

type head = {
  name : Syntax.name;
  target : target;
  type_arguments : Syntax.bracket_item list option;
}

let rec find_head resolved (value : Syntax.expression) =
  match value.kind with
  | Name name | Member (_, name) ->
      Option.map (fun target -> { name; target; type_arguments = None }) resolved.names.(name.id)
  | Parenthesized inner -> find_head resolved inner
  | Bracket (base, items) when resolved.brackets.(value.id) = Some Type_arguments ->
      Option.map
        (fun resolved_head -> { resolved_head with type_arguments = Some items })
        (find_head resolved base)
  | _ -> None

let find_declared_name (definition : Syntax.definition) : Syntax.name option =
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

let find_value_name (definition : Syntax.definition) : Syntax.name option =
  match definition.kind with
  | Function { signature = { name = Plain_name name; _ }; _ }
  | Method_declaration { name = Plain_name name; _ }
  | Constant { name = Plain_name name; _ }
  | Theorem { name; _ } ->
      Some name
  | _ -> None

let resolve (lookups : Names.lookups) (key : Names.key) =
  let definition = lookups.read_definition key
  and spans = lookups.read_spans key
  and syntax_errors = lookups.list_syntax_errors key in
  let is_broken part =
    Option.is_some (Parts.find_syntax_error ~spans ~syntax_errors definition part)
  in
  let module_ = key.module_ in
  let state = Walk.create lookups key ~spans ~syntax_errors in
  let container_key = lookups.find_container key in
  let container =
    Option.map
      (fun (container : Names.key) -> (container.path, lookups.read_definition container))
      container_key
  in
  let is_walked =
    (not (is_broken Header))
    &&
    match container_key with
    | Some container -> not (Names.is_broken lookups container Header)
    | None -> true
  in
  if is_walked then Walk.resolve_definition state ~path:key.path ?container definition;
  (match key.path with
  | Top { name; _ } when List.mem name Prelude.names -> (
      let defines_it =
        match Prelude.find_type name with
        | Some prelude_module -> prelude_module = module_
        | None -> false
      in
      match find_declared_name definition with
      | Some declared when not defines_it ->
          Walk.report state Shadowed_name spans.(declared.id)
            (Printf.sprintf
               "`%s` is a name in the prelude, and a name cannot shadow another. Choose another \
                name."
               name)
      | _ -> ())
  | _ -> ());
  if key.ordinal > 0 && Path.is_resolved key.path then begin
    let span =
      match find_declared_name definition with
      | Some name -> spans.(name.id)
      | None -> Source.Definition_span.make_zero_width spans.(definition.id).start
    in
    let first = lookups.read_place { key with ordinal = 0 } in
    let first =
      if first.file <> (lookups.read_place key).file then Path.show_file first.file else "this file"
    in
    Walk.report state Duplicate_definition span
      (Printf.sprintf "%s is already defined in %s, so this definition is never used."
         (Path.show key.path) first)
  end;
  (match find_value_name definition with
  | Some name when key.ordinal = 0 ->
      let submodule : Path.module_ = { module_ with modules = module_.modules @ [ name.text ] } in
      if lookups.module_exists submodule then
        Walk.report state Duplicate_definition spans.(name.id)
          (Printf.sprintf
             "`%s` is a module, so no definition of `%s` can be named `%s`: `%s.x` would name \
              either."
             (Path.show_module submodule) (Path.show_module module_) name.text
             (Path.show_module submodule))
  | Some _ | None -> ());
  let compute_outcome section =
    let walked = Walk.lookup_section_names state section in
    let resolved =
      { names = walked.names; brackets = walked.brackets; holes = List.rev walked.holes }
    in
    match walked.diagnostics with
    | [] -> Ok { resolved; used_imports = List.sort compare walked.used_imports }
    | diagnostics ->
        Error
          (List.sort
             (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
               compare left.span right.span)
             diagnostics)
  in
  List.map
    (fun section ->
      let is_parsed =
        match section with
        | Interface | Contract -> is_walked
        | Body -> is_walked && not (is_broken Body)
      in
      ( section,
        if is_parsed || (Walk.lookup_section_names state section).diagnostics <> [] then
          Some (compute_outcome section)
        else None ))
    sections

let list_file_diagnostics (lookups : Names.lookups) (path : Path.file) (file : Syntax.file) ~text
    ~(used : string list option) =
  let module_ = path.module_ in
  let has_syntax_error (item : Syntax.definition Syntax.item) =
    match item.value.kind with
    | Definition_error _ -> true
    | _ -> item.positions.syntax_errors <> []
  in
  let used =
    if
      List.exists
        (fun (top_level : Syntax.top_level) ->
          has_syntax_error top_level.definition || List.exists has_syntax_error top_level.methods)
        file.definitions
    then None
    else used
  in
  let diagnostics = ref [] in
  let report ?fixes code span message =
    diagnostics := Diagnostic.make ?fixes ~code:(Resolve code) span message :: !diagnostics
  in
  ignore
    (List.fold_left
       (fun seen (item : Syntax.path Syntax.item) ->
         let span = Source.make_span item.base item.stop in
         let used_module = Names.resolve_used_module lookups ~from:module_ item.value in
         let last = Names.Scope.extract_last_name used_module in
         if Names.Scope.is_restricted_module ~from:module_ used_module then
           report Intrinsic_import span Names.Scope.restricted_module_message
         else if not (Names.is_visible_module lookups ~from:module_ used_module) then
           let missing = Printf.sprintf "No module `%s` exists." (Path.show_module used_module) in
           report Unknown_module span
             (if Names.is_visible_package lookups ~from:module_ used_module.package then missing
              else missing ^ " " ^ Names.Scope.describe_path_start module_)
         else if List.mem last seen then
           report Duplicate_import span
             (Printf.sprintf
                "Another `use` already imports a module named `%s`. Write one of them by its full \
                 path instead."
                last)
         else if
           match lookups.find module_ last with
           | Some entry -> Names.Scope.is_value_kind entry.kind
           | None -> false
         then
           report Duplicate_import span
             (Printf.sprintf
                "`%s` is a definition of `%s`, so this file cannot import a module named `%s`: \
                 `%s.x` would name either. Rename the definition, or write the module's full path."
                last (Path.show_module module_) last last)
         else
           begin match used with
           | Some used when not (List.mem last used) ->
               let stop = span.stop in
               let stop =
                 if stop < String.length text && text.[stop] = '\n' then stop + 1 else stop
               in
               report Unused_import span
                 ~fixes:
                   [
                     Diagnostic.fix "Delete the `use`."
                       [ Diagnostic.delete (Source.make_span item.base stop) ];
                   ]
                 (Printf.sprintf "Nothing in this file uses `%s`." (Path.show_module used_module))
           | Some _ | None -> ()
           end;
         last :: seen)
       [] file.uses);
  List.rev !diagnostics

type trait_header = {
  associated : string list;
  capabilities : string list;
  required : Path.t list;
  laws : string list;
}

let make_trait_header (definition : Syntax.definition) (resolved : resolved) =
  match definition.kind with
  | Trait { requires; members; _ } ->
      let list_member_names select =
        List.filter_map (fun (line : Syntax.trait_member Syntax.node) -> select line.kind) members
      in
      Some
        {
          associated =
            list_member_names (function Associated_type (name, _) -> Some name.text | _ -> None);
          capabilities =
            list_member_names (function Associated_capability name -> Some name.text | _ -> None);
          required =
            List.filter_map
              (fun (bound : Syntax.path_type) ->
                match resolved.names.(bound.path.last.id) with
                | Some (Definition (_, path)) -> Some path
                | _ -> None)
              requires;
          laws = list_member_names (function Law law -> Some law.name.text | _ -> None);
        }
  | _ -> None
