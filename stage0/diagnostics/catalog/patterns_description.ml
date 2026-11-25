let make ?(fixes = []) code location message : Nodes.description =
  { code = Patterns code; severity = Error; location; message; notes = []; fixes }

let unreachable = "Earlier arms already match everything this arm matches, so it is never reached."
let is_any (field : Patterns.field_witness) = field.witness = Any

let rec show_witness : Patterns.witness -> string = function
  | Any -> "_"
  | Boolean value -> if value then "true" else "false"
  | Integers { low; high } ->
      if Z.equal low high then Z.to_string low
      else Printf.sprintf "%s..=%s" (Z.to_string low) (Z.to_string high)
  | Variant { variant; fields = [] } -> variant
  | Record [] -> "()"
  | Variant { variant; fields = [ { witness = Any; _ } ] } -> variant ^ "(_)"
  | Variant { variant; fields } when List.for_all is_any fields -> variant ^ "(..)"
  | Record fields when List.for_all is_any fields -> "_"
  | Variant { variant; fields = [ only ] } ->
      Printf.sprintf "%s(%s)" variant (show_witness only.witness)
  | Record [ only ] -> Printf.sprintf "(%s)" (show_witness only.witness)
  | Variant { variant; fields } -> Printf.sprintf "%s(%s)" variant (show_fields fields)
  | Record fields -> Printf.sprintf "(%s)" (show_fields fields)

and show_fields fields =
  String.concat ", "
    (List.map
       (fun (field : Patterns.field_witness) -> field.field ^ ": " ^ show_witness field.witness)
       fields)

let show_row row = String.concat ", " (List.map show_witness row)

let describe : Patterns.t -> Nodes.description = function
  | Shadowing_arm { arm; name; constant; bindings } ->
      let written = Path.show constant in
      make Unreachable_arm (Build.at arm)
        ~fixes:
          [
            {
              title = [ Text (Printf.sprintf "Write `%s`." written) ];
              edits = List.map (fun binding -> Build.replace binding [ Text written ]) bindings;
            };
          ]
        [
          Text
            (Printf.sprintf
               "%s `%s` in an earlier arm binds a variable, which matches every value. To match \
                the constant, write `%s`."
               unreachable name written);
        ]
  | Unreachable_arm { arm } ->
      make Unreachable_arm (Build.at arm)
        ~fixes:
          [
            {
              title = [ Text "Delete the arm." ];
              edits = [ Build.remove_lines { covering = [ arm ] } ];
            };
          ]
        [ Text unreachable ]
  | Unreachable_alternative { alternative; previous; next; is_after_alternatives } ->
      let deletion =
        match (previous, next) with
        | Some previous, _ ->
            Build.remove_entry { covering = [ alternative ] } (Previous { covering = [ previous ] })
        | None, Some next ->
            Build.remove_entry { covering = [ alternative ] } (Next { covering = [ next ] })
        | None, None -> Build.delete (Start alternative) (Stop alternative)
      in
      make Unreachable_alternative (Build.at alternative)
        ~fixes:[ { title = [ Text "Delete the alternative." ]; edits = [ deletion ] } ]
        [
          Text
            (if is_after_alternatives then
               "The alternatives before this one already match everything it matches."
             else "Earlier arms already match everything this alternative matches.");
        ]
  | Not_covered { match_; last_arm; witness; other_witnesses; may_have_more } ->
      make Not_covered (Build.at match_)
        ~fixes:
          (match last_arm with
          | Some last_arm ->
              [
                {
                  title = [ Text "Add an arm for each missing case." ];
                  edits =
                    [
                      Build.add_lines_after last_arm
                        (List.map
                           (fun row -> [ Description.Text (show_row row ^ " => todo") ])
                           (witness :: other_witnesses));
                    ];
                };
              ]
          | None -> [])
        [
          Text
            (Printf.sprintf "This `match` does not cover every case: `%s` is not covered%s."
               (show_row witness)
               (match (other_witnesses, may_have_more) with
               | [], _ -> ""
               | _, true -> ", nor others"
               | [ _ ], false -> ", nor 1 other"
               | others, false -> Printf.sprintf ", nor %d others" (List.length others)));
        ]
  | Refutable { pattern; witness } ->
      make Refutable (Build.at pattern)
        [
          Text
            (Printf.sprintf
               "This pattern can fail: it does not match `%s`. Use `match`, an `is` test, or `let \
                ... else`."
               (show_witness witness));
        ]
