module Names = Names
module Parts = Parts
module Prelude = Prelude

type cost_function = Walk.cost_function = Log | Power | Time | Calls

type target = Walk.target =
  | Binding
  | Local of Syntax.id
  | Generic of Syntax.id
  | Definition of Path.t
  | Variant of Path.t * string
  | Module of Path.module_
  | Field of string
  | Result_value
  | Old
  | Cost_function of cost_function
  | Unknown

type bracket = Walk.bracket = Index | Type_arguments | Method_bracket

type value = Walk.value =
  | Value_local of Syntax.id
  | Value_generic of Syntax.id
  | Value_field of string

type resolved = {
  names : target option array;
  brackets : bracket option array;
  holes : (Syntax.id * (string * value) list) list;
  diagnostics : Diagnostic.t list;
}

(* The name a definition declares, for reporting a duplicate. *)
let declared_name (definition : Syntax.definition) : Syntax.name option =
  match definition.kind with
  | Function { signature = { name = Plain_name name | Member_name (_, name); _ }; _ }
  | Constant { name = Plain_name name | Member_name (_, name); _ }
  | Type_definition { name; _ }
  | Trait { name; _ }
  | Capability { name; _ }
  | Theorem { name; _ }
  | Law_proof { law = name; _ } ->
      Some name
  | Impl _ | Test _ | Definition_error _ -> None

let resolved =
  Query.query ~name:"resolved" ~show:Names.show_key ~saved:true
    ~about:(fun (key : Names.key) -> Some { path = key.path; part = Some "resolved" })
    (fun database (key : Names.key) ->
      match Query.demand database Names.definition key with
      | Some definition ->
          let module_ = key.module_ in
          let size = definition.id + 1 in
          let state : Walk.state =
            {
              database;
              module_;
              names = Array.make size None;
              brackets = Array.make size None;
              diagnostics = [];
              holes = [];
            }
          in
          Walk.definition state definition;
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
            Walk.report state Duplicate_definition span
              (Printf.sprintf
                 "%s is already defined in this file, so this definition is never used."
                 (Path.show key.path))
          end;
          Some
            {
              names = state.names;
              brackets = state.brackets;
              holes = List.rev state.holes;
              diagnostics =
                List.sort
                  (fun (left : Diagnostic.t) (right : Diagnostic.t) -> compare left.span right.span)
                  state.diagnostics;
            }
      | None -> None)

let file_diagnostics =
  Query.query ~name:"file_diagnostics" ~show:Path.show_module ~saved:true (fun database module_ ->
      let file = Query.demand database Workspace.file module_ in
      (* An import is used when a name followed by [::] spells it anywhere
         outside the [use] lines, read from the tokens, so a use inside a part
         the parser could not read counts too, as does one in an
         interpolation. *)
      let in_use_line (span : Source.span) =
        List.exists
          (fun (item : Syntax.path Syntax.item) ->
            item.base <= span.start && span.start < item.base + String.length item.text)
          file.uses
      in
      let rec module_names (tokens : Token.t array) =
        List.concat
          (List.mapi
             (fun index (token : Token.t) ->
               match token.kind with
               | Lower name
                 when index + 1 < Array.length tokens
                      && tokens.(index + 1).kind = Punctuation Colon_colon
                      && not (in_use_line token.span) ->
                   [ name ]
               | String literal ->
                   List.concat_map
                     (fun (interpolation : Token.interpolation) ->
                       module_names interpolation.tokens)
                     (Array.to_list (Token.interpolations literal))
               | _ -> [])
             (Array.to_list tokens))
      in
      let used = module_names file.tokens in
      let text = Source.text file.source in
      let diagnostics = ref [] in
      let report ?fixes code span message =
        diagnostics := Diagnostic.make ?fixes ~code:(Resolve code) span message :: !diagnostics
      in
      ignore
        (List.fold_left
           (fun seen (item : Syntax.path Syntax.item) ->
             let span = Source.span item.base (item.base + String.length item.text) in
             let used_module = Names.used_module item.value in
             let last = Names.last_name used_module in
             if used_module = Intrinsic.module_ && module_.package <> Prelude.standard then
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
             else if not (List.mem last used) then begin
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

let diagnostics database module_ =
  List.sort
    (fun (left : Diagnostic.t) (right : Diagnostic.t) ->
      compare (left.span, left.code) (right.span, right.code))
    (Query.demand database file_diagnostics module_
    @ Names.per_definition database module_ (fun key ->
        match Query.demand database resolved key with
        | Some resolved -> resolved.diagnostics
        | None -> []))

let closest = Walk.closest
