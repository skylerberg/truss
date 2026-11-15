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
  used_imports : string list;
}

let sections = [ Interface; Contract; Body ]

let merge = function
  | [] -> { names = [||]; brackets = [||]; holes = []; used_imports = [] }
  | first :: _ as parts ->
      let pick select index = List.find_map (fun part -> (select part).(index)) parts in
      {
        names = Array.init (Array.length first.names) (pick (fun part -> part.names));
        brackets = Array.init (Array.length first.brackets) (pick (fun part -> part.brackets));
        holes = List.concat_map (fun part -> part.holes) parts;
        used_imports =
          List.sort_uniq compare (List.concat_map (fun part -> part.used_imports) parts);
      }

let whole ?(sections = sections) read key =
  match List.map (fun section -> read section key) sections with
  | parts when List.for_all Option.is_some parts -> Some (merge (List.filter_map Fun.id parts))
  | _ -> None

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

let resolve (lookups : Names.lookups) (key : Names.key) section =
  match lookups.definition key with
  | Some definition ->
      let module_ = key.module_ in
      let state = Walk.create lookups key ~size:(definition.id + 1) ~walked:section in
      let container =
        Option.bind (lookups.container key) (fun (container : Names.key) ->
            Option.map
              (fun definition -> (container.path, definition))
              (lookups.definition container))
      in
      let is_walked =
        (not (Parts.broken definition Header))
        &&
        match container with
        | Some (_, enclosing) -> not (Parts.broken enclosing Header)
        | None -> true
      in
      if is_walked then Walk.definition state ~path:key.path ?container definition;
      (match key.path with
      | Top { name; _ } when List.mem name Prelude.names -> (
          let defines_it =
            match Prelude.find_type name with
            | Some prelude_module -> prelude_module = module_
            | None -> false
          in
          match declared_name definition with
          | Some declared when not defines_it ->
              Walk.report state Shadowed_name declared.span
                (Printf.sprintf
                   "`%s` is a name in the prelude, and a name cannot shadow another. Choose \
                    another name."
                   name)
          | _ -> ())
      | _ -> ());
      if key.ordinal > 0 then begin
        let span =
          match declared_name definition with
          | Some name -> name.span
          | None -> Source.Definition_span.make definition.span.start definition.span.start
        in
        let first =
          match (lookups.place { key with ordinal = 0 }, lookups.place key) with
          | Some first, Some place when first.file <> place.file -> Path.show_file first.file
          | _ -> "this file"
        in
        Walk.report state Duplicate_definition span
          (Printf.sprintf "%s is already defined in %s, so this definition is never used."
             (Path.show key.path) first)
      end;
      let outcome () =
        let walked = Walk.names_of state section in
        let resolved =
          {
            names = walked.names;
            brackets = walked.brackets;
            holes = List.rev walked.holes;
            used_imports = List.sort compare walked.used_imports;
          }
        in
        match walked.diagnostics with
        | [] -> Ok resolved
        | diagnostics ->
            Error
              (List.sort
                 (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
                   compare left.span right.span)
                 diagnostics)
      in
      let is_parsed =
        match section with
        | Interface | Contract -> is_walked
        | Body -> is_walked && not (Parts.broken definition Body)
      in
      if is_parsed || (Walk.names_of state section).diagnostics <> [] then Some (outcome ())
      else None
  | None -> None

let file_diagnostics (lookups : Names.lookups) (path : Path.file) (file : Syntax.file) ~text
    ~(used : string list option) =
  let module_ = path.module_ in
  let is_recovered (item : Syntax.definition Syntax.item) =
    match item.value with
    | { kind = Definition_error _; _ } -> true
    | { recovered; _ } -> recovered <> []
  in
  let used = if List.exists is_recovered file.definitions then None else used in
  let diagnostics = ref [] in
  let report ?fixes code span message =
    diagnostics := Diagnostic.make ?fixes ~code:(Resolve code) span message :: !diagnostics
  in
  ignore
    (List.fold_left
       (fun seen (item : Syntax.path Syntax.item) ->
         let span = Source.span item.base (item.base + String.length item.text) in
         let used_module = Names.used_module lookups ~from:module_ item.value in
         let last = Names.last_name used_module in
         if used_module = Intrinsic.module_ && module_.package <> Path.standard_package then
           report Intrinsic_import span "Only the `standard` package can use `standard::intrinsic`."
         else if not (Names.is_visible_module lookups ~from:module_ used_module) then
           report Unknown_module span
             (Printf.sprintf "No module `%s` exists." (Path.show_module used_module))
         else if List.mem last seen then
           report Duplicate_import span
             (Printf.sprintf
                "Another `use` already imports a module named `%s`. Write one of them by its full \
                 path instead."
                last)
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
                       [ Diagnostic.delete (Source.span item.base stop) ];
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

let trait_header (definition : Syntax.definition) (resolved : resolved) =
  match definition.kind with
  | Trait { requires; members; _ } ->
      let member_names select =
        List.filter_map (fun (line : Syntax.trait_member Syntax.line) -> select line.kind) members
      in
      Some
        {
          associated =
            member_names (function Associated_type (name, _) -> Some name.text | _ -> None);
          capabilities =
            member_names (function Associated_capability name -> Some name.text | _ -> None);
          required =
            List.filter_map
              (fun (bound : Syntax.path_type) ->
                match resolved.names.(bound.path.last.id) with
                | Some (Definition (_, path)) -> Some path
                | _ -> None)
              requires;
          laws = member_names (function Law law -> Some law.name.text | _ -> None);
        }
  | _ -> None
