(* [truss holes]: every [todo], with its expected type, the bindings in
   scope, and the tests and [main] that reach it. *)

module Names = Resolve.Names

type hole = {
  definition : Path.t;
  file : string;
  line : int;
  column : int;
  type_ : string option;  (** [None] for a type defined as [todo] *)
  in_scope : (string * string) list;  (** Each binding in scope, with its type *)
  mutable blocks : string list;
}

let of_definition (project : Project.t) source (declaration : Names.declaration) =
  let context = project.context in
  let key = Names.key_of declaration in
  match
    ( Query.demand context Names.definition key,
      Query.demand context Resolve.resolved key,
      Query.demand context Infer.type_check_result key,
      Query.demand context Names.base key )
  with
  | Some definition, Some resolved, Some { tables; _ }, Some (_, base) ->
      List.map
        (fun (hole : Inspect.hole) ->
          let line, column = Source.position source (base + hole.offset) in
          {
            definition = declaration.path;
            file = Source.path source;
            line;
            column;
            type_ = hole.expected;
            in_scope = hole.scope;
            blocks = [];
          })
        (Inspect.holes definition resolved tables)
  | _ -> []

let gather (project : Project.t) paths =
  List.concat_map
    (fun module_ ->
      let source = Project.source project module_ in
      List.concat_map
        (fun (declaration : Names.declaration) ->
          if declaration.ordinal = 0 then of_definition project source declaration else [])
        (Query.demand project.context Names.declarations module_))
    (Project.selected project paths)

(* The blocked roots of each hole: [main] and every test that reaches the
   hole's definition transitively. *)
let fill_blocks (project : Project.t) holes =
  if holes <> [] then begin
    let dependencies = Database.dependencies project.session in
    let roots =
      (match Program_command.mains project with [ main ] -> [ ("main", main) ] | _ -> [])
      @ List.map
          (fun (test : Test_command.test) -> ("test " ^ Test_command.label test, test.path))
          (Test_command.select project ~paths:[] ~match_:None)
    in
    List.iter
      (fun (label, root) ->
        let seen = Project.reachable dependencies root in
        List.iter
          (fun hole ->
            if Hashtbl.mem seen hole.definition then hole.blocks <- hole.blocks @ [ label ])
          holes)
      roots
  end

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
               Json.Object [ ("name", Json.String name); ("type", Json.String ty) ])
             hole.in_scope) );
      ("blocks", Json.List (List.map (fun b -> Json.String b) hole.blocks));
    ]

let print hole =
  (match hole.type_ with
  | Some ty -> Output.printf "%s:%d:%d: hole of type %s\n" hole.file hole.line hole.column ty
  | None ->
      Output.printf "%s:%d:%d: the type %s is defined as todo\n" hole.file hole.line hole.column
        (Path.show hole.definition));
  if hole.in_scope <> [] then
    Output.printf "    in scope: %s\n"
      (String.concat ", " (List.map (fun (name, ty) -> name ^ ": " ^ ty) hole.in_scope));
  if hole.blocks <> [] then Output.printf "    blocks: %s\n" (String.concat "; " hole.blocks)

let run ~directory ~paths ~json =
  let project = Project.load directory in
  let report = Report.gather project in
  let holes = gather project paths in
  fill_blocks project holes;
  if json then Json.print (Report.document report [ ("holes", Json.List (List.map to_json holes)) ])
  else begin
    Report.print report;
    List.iter print holes;
    if holes = [] then Output.print_line "No holes."
  end;
  if Report.clean report then 0 else 1
