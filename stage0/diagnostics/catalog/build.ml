let node origin : Nodes.node = Node origin

let cover ({ covering } : Core.origin Description.range) =
  { Description.covering = List.map node covering }

let at origin = Description.At (node origin)
let over range = Description.Over (cover range)
let quote origin = Description.Quote (node origin)
let quote_over range = Description.Quote_over (cover range)
let after origin = Description.After (node origin)
let replace origin pieces = Description.Replace (node origin, pieces)
let insert_before origin pieces = Description.Insert_before (node origin, pieces)
let insert_after origin pieces = Description.Insert_after (node origin, pieces)

let map_boundary : Core.origin Description.boundary -> Nodes.node Description.boundary = function
  | Start origin -> Start (node origin)
  | Stop origin -> Stop (node origin)

let delete start stop = Description.Delete (map_boundary start, map_boundary stop)

let remove_entry entry (siblings : Core.origin Description.siblings) =
  Description.Remove_entry
    {
      entry = cover entry;
      siblings =
        (match siblings with
        | Next range -> Next (cover range)
        | Previous range -> Previous (cover range)
        | Alone { clause; is_only_clause } -> Alone { clause = node clause; is_only_clause });
    }

let remove_lines range = Description.Remove_lines (cover range)
let add_lines_after origin lines = Description.Add_lines_after (node origin, lines)

let list_spelling_fixes origin ~written candidates =
  match Diagnostic.find_closest written candidates with
  | Some candidate ->
      [
        {
          Description.title = [ Text (Printf.sprintf "Write `%s`." candidate) ];
          edits = [ replace origin [ Text candidate ] ];
        };
      ]
  | None -> []

let write_hidden path (visibility : Language.Visibility.t) =
  Printf.sprintf "`%s` is %s, so it cannot be used here." (Path.show path)
    (match visibility with
    | Private -> "private to its module"
    | Internal -> "internal to its package"
    | Public | Public_opaque ->
        Compiler_bug.raise_bug ~stage:"Catalog" "%s is public, so it is not hidden" (Path.show path))

let rec show_callee (path : Path.t) =
  match path with
  | Top { name; _ } -> name
  | Method { owner = Impl { for_type; _ } | Derived { type_ = for_type; _ }; name; _ }
  | Method { owner = for_type; name; _ }
  | Member_constant { owner = for_type; name } ->
      show_callee for_type ^ "." ^ name
  | Default _ | Impl _ | Derived _ | Test _ | Law_proof _ | Unresolved _ -> Path.show path

let name_call callee =
  match callee with
  | Some callee -> Printf.sprintf "call to `%s`" (show_callee callee)
  | None -> "call"

let describe_call ?callee (origin : Core.origin) =
  let call = name_call callee in
  match origin with
  | Written _ -> [ Description.Text ("this " ^ call) ]
  | Desugared { desugaring; _ } ->
      let maker =
        match desugaring with
        | For_loop -> [ Description.Text "this `for` loop" ]
        | Quantifier -> [ Text "this quantifier" ]
        | Derived -> [ Text "the derived `"; quote origin; Text "`" ]
        | Rewrite | Try -> [ Text "`"; quote origin; Text "`" ]
      in
      (Description.Text ("the " ^ call ^ " that ") :: maker) @ [ Text " makes" ]

let show_field_path parameter fields = String.concat "." (parameter :: fields)
