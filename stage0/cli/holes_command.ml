(* [truss holes]: every [todo], with the type it must have, the names in
   scope there, and what it blocks. See CLI.md, "truss holes", and
   DESIGN.md, "Unfinished code". *)

module Names = Resolve.Names

type hole = {
  definition : Path.t;
  file : string;
  line : int;
  column : int;
  type_ : string option;  (** [None] for a type defined as [todo] *)
  in_scope : (string * string option) list;  (** Each name, with its type when known *)
  mutable blocks : string list;
}

(* The span, relative to its definition, of the expression with that id. *)
let expression_span (definition : Syntax.definition) id =
  let found = ref None in
  let rec visit (expression : Syntax.expression) =
    if expression.id = id then found := Some expression.span
    else Syntax_walk.children visit expression
  in
  Syntax_walk.definition visit definition;
  !found

(* A type, or that it is not decided yet, for a [todo] whose type nothing
   fixes, such as one that is interpolated. The checked form holds no
   unsolved type, so such a [todo]'s type is the error type there. *)
let show_type (ty : Types.ty) =
  match ty with Hole | Error -> "not decided yet" | ty -> Types.show ty

(* The holes of one definition, in order. *)
let of_definition (project : Project.t) source (declaration : Names.declaration) =
  let database = project.database in
  let key = Names.key_of declaration in
  match
    ( Query.demand database Names.definition key,
      Query.demand database Resolve.resolved key,
      Query.demand database Names.base key )
  with
  | Some definition, Some resolved, Some (_, base) -> (
      let position offset = Source.position source (base + offset) in
      let checked =
        Option.map (fun (r : Infer.result) -> r.checked) (Query.demand database Infer.checked key)
      in
      let at table id =
        match checked with
        | Some checked when id < Array.length (table checked) -> (table checked).(id)
        | _ -> None
      in
      let expressions =
        List.filter_map
          (fun (id, scope) ->
            match expression_span definition id with
            | None -> None
            | Some span ->
                let line, column = position span.start in
                Some
                  {
                    definition = declaration.path;
                    file = Source.path source;
                    line;
                    column;
                    type_ =
                      Some
                        (match at (fun c -> c.Checked.types) id with
                        | Some ty -> show_type ty
                        | None -> "not decided yet");
                    in_scope =
                      List.map
                        (fun (name, (value : Resolve.value)) ->
                          ( name,
                            match value with
                            | Value_local binding ->
                                Option.map show_type (at (fun c -> c.Checked.local_types) binding)
                            | Value_generic _ -> Some "USize"
                            | Value_field _ -> None ))
                        scope;
                    blocks = [];
                  })
          resolved.holes
      in
      match definition.kind with
      | Type_definition { name; body = Type_todo; _ } ->
          let line, column = position name.span.start in
          {
            definition = declaration.path;
            file = Source.path source;
            line;
            column;
            type_ = None;
            in_scope = [];
            blocks = [];
          }
          :: expressions
      | _ -> expressions)
  | _ -> []

let gather (project : Project.t) paths =
  List.concat_map
    (fun module_ ->
      let source = Project.source project module_ in
      List.concat_map
        (fun (declaration : Names.declaration) ->
          if declaration.ordinal = 0 then of_definition project source declaration else [])
        (Query.demand project.database Names.declarations module_))
    (Project.selected project paths)

(* What each hole blocks: [main], if the program can reach it, and every
   test that can. This lowers the code, so it is worked out only for a
   package without errors. *)
let fill_blocks (project : Project.t) holes =
  let compile = Compiler.lowering_only project in
  let roots =
    (match Program_command.mains project with
      | [ main ] -> [ ("main", Compile.main_root main) ]
      | _ -> [])
    @ List.map
        (fun (test : Test_command.test) ->
          ("test " ^ Test_command.label test, Compile.test_root test.path))
        (Test_command.select project ~paths:[] ~match_:None)
  in
  List.iter
    (fun (label, root) ->
      match Compiler.reached compile root with
      | None -> ()
      | Some reached ->
          List.iter
            (fun hole ->
              if List.exists (Path.equal hole.definition) reached then
                hole.blocks <- hole.blocks @ [ label ])
            holes)
    roots

let to_json hole =
  Json.Object
    [
      ("definition", Json.String (Path.show hole.definition));
      ("file", Json.String hole.file);
      ("line", Json.Int hole.line);
      ("column", Json.Int hole.column);
      ("kind", Json.String (if hole.type_ = None then "type" else "value"));
      ("type", Json.option (fun t -> Json.String t) hole.type_);
      ( "in_scope",
        Json.List
          (List.map
             (fun (name, ty) ->
               Json.Object
                 [ ("name", Json.String name); ("type", Json.option (fun t -> Json.String t) ty) ])
             hole.in_scope) );
      ("blocks", Json.List (List.map (fun b -> Json.String b) hole.blocks));
    ]

let print hole =
  (match hole.type_ with
  | Some ty -> Printf.printf "%s:%d:%d: hole of type %s\n" hole.file hole.line hole.column ty
  | None ->
      Printf.printf "%s:%d:%d: the type %s is defined as todo\n" hole.file hole.line hole.column
        (Path.show hole.definition));
  if hole.in_scope <> [] then
    Printf.printf "    in scope: %s\n"
      (String.concat ", "
         (List.map
            (fun (name, ty) -> match ty with Some ty -> name ^ ": " ^ ty | None -> name)
            hole.in_scope));
  if hole.blocks <> [] then Printf.printf "    blocks: %s\n" (String.concat "; " hole.blocks)

let run ~directory ~paths ~json =
  let project = Project.load directory in
  let files = Report.gather project in
  let holes = gather project paths in
  if files = [] then fill_blocks project holes;
  if json then
    Json.print
      (Json.document ~diagnostics:(Report.to_json files)
         [ ("holes", Json.List (List.map to_json holes)) ])
  else begin
    Report.print files;
    List.iter print holes;
    if holes = [] then print_endline "No holes."
  end;
  if files = [] then 0 else 1
