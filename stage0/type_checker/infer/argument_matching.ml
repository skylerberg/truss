type owner = Catalog.Inference.owner

type site =
  | Call
  | Construction of owner
  | Tuple_construction of owner
  | Pattern of { owner : owner; is_tuple_type : bool }

type entry = { label : Syntax.name option; punned : string option; origin : Core.origin }

let find_owner = function
  | Call -> None
  | Construction owner | Tuple_construction owner | Pattern { owner; _ } -> Some owner

let find_index names name = List.find_index (String.equal name) names

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

let find_labeled_form ~parameter_names entries =
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
  then Some (List.map2 (fun entry fix_label -> (fix_label, entry.origin)) entries fix_labels)
  else None

let list_indexes state site ~parameter_names entries =
  let reject diagnostic = Error (State.make_error_type state diagnostic) in
  let find_labeled_index (label : Syntax.name) =
    match find_index parameter_names label.text with
    | Some index -> Ok index
    | None ->
        reject
          (Unknown_label
             {
               label = Written label.id;
               written = label.text;
               owner = find_owner site;
               candidates = parameter_names;
             })
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
              let label =
                match List.nth_opt parameter_names position with
                | Some name
                  when is_aligned
                       && (not (List.mem position labeled_indexes))
                       && Option.fold ~none:true ~some:(Int.equal position)
                            (find_punned_index entry) ->
                    Some name
                | _ -> None
              in
              let index = reject (Positional_after_labeled { argument = entry.origin; label }) in
              index
              :: list_from (position + 1) ~follows_label ~is_aligned:(Option.is_some label) rest
          | None -> (
              match (tuple_owner, find_punned_index entry) with
              | Some owner, Some named when named <> position ->
                  let field = List.nth parameter_names named in
                  let index =
                    reject
                      (Tuple_argument_out_of_order
                         {
                           argument = entry.origin;
                           owner;
                           filled = List.nth parameter_names position;
                           field;
                         })
                  in
                  index :: list_from (position + 1) ~follows_label ~is_aligned:false rest
              | _ -> Ok position :: list_from (position + 1) ~follows_label ~is_aligned rest))
    in
    list_from 0 ~follows_label:false ~is_aligned:true entries
  in
  let list_named_indexes () =
    let bare_owner : Catalog.Inference.bare_owner =
      match site with
      | Pattern { owner; is_tuple_type } -> Pattern_owner { owner; is_tuple_type }
      | Construction owner -> Construction_owner owner
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
            reject
              (Bare_value
                 {
                   argument = entry.origin;
                   owner = bare_owner;
                   fields = parameter_names;
                   label = fix_label;
                 }))
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
          reject
            (Repeated_argument
               {
                 at =
                   (match entry.label with
                   | Some (label : Syntax.name) -> Written label.id
                   | None -> entry.origin);
                 name = List.nth parameter_names index;
                 is_pattern = (match site with Pattern _ -> true | _ -> false);
               })
      | Ok index ->
          Hashtbl.replace assigned index ();
          Ok index
      | Error _ as error -> error)
    entries indexes
