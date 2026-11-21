type site =
  | Call
  | Construction of string
  | Tuple_construction of string
  | Pattern of { owner : string; is_tuple_type : bool }

type entry = { label : Syntax.name option; punned : string option; span : Source.Definition_span.t }

let find_owner = function
  | Call -> None
  | Construction owner | Tuple_construction owner | Pattern { owner; _ } -> Some owner

let show_names names = String.concat ", " (List.map (fun name -> "`" ^ name ^ "`") names)
let find_index names name = List.find_index (String.equal name) names

let make_label_fix field (entry : entry) =
  State.fix (Printf.sprintf "Label it `%s`." field) [ State.insert entry.span.start (field ^ ": ") ]

let list_claims ~parameter_names entries =
  let has_one_field = List.length parameter_names = 1 in
  List.mapi
    (fun position entry ->
      match entry.label with
      | Some (label : Syntax.name) -> find_index parameter_names label.text
      | None -> (
          match Option.bind entry.punned (find_index parameter_names) with
          | Some index -> Some index
          | None -> if position = 0 && has_one_field then Some 0 else None))
    entries

let list_fix_labels ~parameter_names entries claims =
  let is_unclaimed =
    List.map2 (fun entry claim -> Option.is_none entry.label && Option.is_none claim) entries claims
  in
  let unclaimed_count = List.length (List.filter Fun.id is_unclaimed) in
  if unclaimed_count = 0 then List.map (fun _ -> None) entries
  else
    let is_complete_positional_list =
      unclaimed_count = List.length entries && unclaimed_count = List.length parameter_names
    in
    let open_fields =
      List.filteri (fun index _ -> not (List.mem (Some index) claims)) parameter_names
    in
    List.mapi
      (fun position is_unclaimed ->
        if not is_unclaimed then None
        else if is_complete_positional_list then List.nth_opt parameter_names position
        else match open_fields with [ field ] when unclaimed_count = 1 -> Some field | _ -> None)
      is_unclaimed

let find_labeled_form state ~parameter_names entries =
  let claims = list_claims ~parameter_names entries in
  let fix_labels = list_fix_labels ~parameter_names entries claims in
  let fields =
    List.filter_map Fun.id
      (List.map2
         (fun claim fix_label ->
           match claim with
           | Some index -> Some (List.nth parameter_names index)
           | None -> fix_label)
         claims fix_labels)
  in
  if
    List.length fields = List.length entries
    && List.length (List.sort_uniq String.compare fields) = List.length fields
  then
    Some
      ("("
      ^ String.concat ", "
          (List.map2
             (fun entry fix_label ->
               let written = State.quote_span state entry.span in
               match fix_label with Some field -> field ^ ": " ^ written | None -> written)
             entries fix_labels)
      ^ ")")
  else None

let list_indexes state site ~parameter_names entries =
  let reject ?fixes code span message =
    Error (State.make_error_type state ?fixes code span message)
  in
  let find_labeled_index (label : Syntax.name) =
    match find_index parameter_names label.text with
    | Some index -> Ok index
    | None ->
        let span = State.read_span state label.id in
        reject Unknown_label span
          ~fixes:(Diagnostic.list_spelling_fixes span ~written:label.text parameter_names)
          (match find_owner site with
          | None -> Printf.sprintf "No parameter is named `%s`." label.text
          | Some owner -> Printf.sprintf "`%s` has no field `%s`." owner label.text)
  in
  let find_punned_index entry = Option.bind entry.punned (find_index parameter_names) in
  let list_positional_indexes ~tuple_owner =
    let labeled_indexes =
      List.filter_map
        (fun entry ->
          Option.bind entry.label (fun (label : Syntax.name) ->
              find_index parameter_names label.text))
        entries
    in
    let rec list_from position ~follows_label ~is_aligned = function
      | [] -> []
      | entry :: rest -> (
          match entry.label with
          | Some label ->
              let index = find_labeled_index label in
              let is_at_position =
                match index with Ok index -> index = position | Error _ -> false
              in
              index
              :: list_from (position + 1) ~follows_label:true
                   ~is_aligned:(is_aligned && is_at_position) rest
          | None when follows_label ->
              let fixes =
                match List.nth_opt parameter_names position with
                | Some name
                  when is_aligned
                       && (not (List.mem position labeled_indexes))
                       && Option.fold ~none:true ~some:(Int.equal position)
                            (find_punned_index entry) ->
                    [ make_label_fix name entry ]
                | _ -> []
              in
              let index =
                reject Positional_after_labeled entry.span ~fixes
                  "A positional argument cannot follow a labeled argument. Label it, or move it \
                   before the labeled arguments."
              in
              index :: list_from (position + 1) ~follows_label ~is_aligned:(fixes <> []) rest
          | None -> (
              match (tuple_owner, find_punned_index entry) with
              | Some owner, Some named when named <> position ->
                  let field = List.nth parameter_names named in
                  let index =
                    reject Out_of_order entry.span
                      ~fixes:[ make_label_fix field entry ]
                      (Printf.sprintf
                         "`%s` is a tuple type, built by position, so `%s` here fills the field \
                          `%s`. Label it, or move it to the position of `%s`."
                         owner
                         (State.quote_span state entry.span)
                         (List.nth parameter_names position)
                         field)
                  in
                  index :: list_from (position + 1) ~follows_label ~is_aligned:false rest
              | _ -> Ok position :: list_from (position + 1) ~follows_label ~is_aligned rest))
    in
    list_from 0 ~follows_label:false ~is_aligned:true entries
  in
  let list_named_indexes () =
    let describe_bare_value () =
      let names = parameter_names in
      match site with
      | Pattern { owner; is_tuple_type; _ } ->
          Printf.sprintf
            "A bare pattern must name a field, since `%s` has %d fields: %s. In parentheses, \
             fields match by name.%s"
            owner (List.length names) (show_names names)
            (if is_tuple_type then
               " A list of patterns without parentheses, after `let`, `var`, or `for`, matches the \
                fields of this tuple type by position."
             else "")
      | Construction owner ->
          Printf.sprintf
            "`%s` has %d fields: %s. Fields have no order, so every argument needs a label, or a \
             variable with its field's name."
            owner (List.length names) (show_names names)
      | Call | Tuple_construction _ ->
          State.raise_bug "arguments matched by position were matched by name"
    in
    let claims = list_claims ~parameter_names entries in
    let fix_labels = list_fix_labels ~parameter_names entries claims in
    List.map2
      (fun (entry, claim) fix_label ->
        match (entry.label, claim) with
        | _, Some index -> Ok index
        | Some label, None -> find_labeled_index label
        | None, None ->
            reject Missing_label entry.span
              ~fixes:
                (Option.to_list (Option.map (fun field -> make_label_fix field entry) fix_label))
              (describe_bare_value ()))
      (List.combine entries claims) fix_labels
  in
  let indexes =
    match site with
    | Call -> list_positional_indexes ~tuple_owner:None
    | Tuple_construction owner -> list_positional_indexes ~tuple_owner:(Some owner)
    | Construction _ | Pattern _ -> list_named_indexes ()
  in
  let assigned = Hashtbl.create 8 in
  List.map2
    (fun entry index ->
      match index with
      | Ok index when Hashtbl.mem assigned index ->
          reject Repeated_argument
            (match entry.label with
            | Some (label : Syntax.name) -> State.read_span state label.id
            | None -> entry.span)
            (Printf.sprintf "`%s` is %s more than once." (List.nth parameter_names index)
               (match site with
               | Pattern _ -> "matched"
               | Call | Construction _ | Tuple_construction _ -> "given"))
      | Ok index ->
          Hashtbl.replace assigned index ();
          Ok index
      | Error _ as error -> error)
    entries indexes
