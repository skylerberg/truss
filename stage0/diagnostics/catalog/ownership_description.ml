let make ?(notes = []) ?(fixes = []) code location message : Nodes.description =
  { code = Ownership code; severity = Error; location; message; notes; fixes }

let show_root = function
  | Ownership.Self -> [ Description.Text "self" ]
  | Named name -> [ Text name ]
  | Unnamed origin -> [ Build.quote origin ]
  | Temporary -> [ Text "temporary" ]
  | Constant (Top { name; _ } | Member_constant { name; _ }) -> [ Text name ]
  | Constant path -> [ Text (Path.show path) ]
  | Environment -> [ Text "the lambda's captured variables" ]

let show_place place =
  show_root place.Ownership.root
  @ List.map
      (function Ownership.Field name -> Description.Text ("." ^ name) | Indexed -> Text "[...]")
      place.steps

let code_of pieces = (Description.Text "`" :: pieces) @ [ Text "`" ]

let show_verb = function
  | Ownership.Be_used -> "be used"
  | Be_passed_mut -> "be passed `mut`"
  | Be_assigned -> "be assigned"
  | Be_moved -> "be moved"

let show_lender = function
  | Ownership.Loop -> [ Description.Text "the loop" ]
  | Provide_block -> [ Text "the `provide` block" ]
  | Rest_of_statement -> [ Text "a lending call until this statement ends" ]
  | Earlier_operand -> [ Text "an earlier operand of this expression" ]
  | Alias root ->
      (Description.Text "a lending call until " :: code_of (show_root root))
      @ [ Text " goes out of scope" ]

let describe_loan loan =
  let through =
    match loan.Ownership.through with
    | Some borrowed ->
        (Description.Text " through " :: code_of (show_place borrowed))
        @ [ Text ", which views it" ]
    | None -> []
  in
  if loan.is_mut then
    code_of (show_place loan.place)
    @ (Description.Text " is lent `mut` to " :: show_lender loan.lender)
    @ through
    @ [ Text ", so it cannot be used here." ]
  else
    code_of (show_place loan.place)
    @ Description.Text (Printf.sprintf " cannot %s while it is lent to " (show_verb loan.verb))
      :: show_lender loan.lender
    @ through @ [ Text "." ]

let copy_fix title = function
  | Some { Ownership.moved; own_keyword } ->
      [
        {
          Description.title = [ Text title ];
          edits =
            (match own_keyword with
              | Some (written, operand) -> [ Build.delete (Start written) (Start operand) ]
              | None -> [])
            @ [ Build.insert_after moved [ Text ".copy()" ] ];
        };
      ]
  | None -> []

let show_schedule : Language.Loop_mode.t -> string = function
  | Parallel -> "parallel"
  | Concurrent -> "concurrent"
  | Sequential -> "for"

let show_holder = function
  | Some name -> Printf.sprintf "`%s`" name
  | None -> "the value built here"

let describe_act = function
  | Ownership.Is -> ([ Description.Text "is" ], "A constant is a view only of another constant.")
  | Returns -> ([ Text "returns" ], "A function returns a view only of its parameters.")
  | Stores_in root ->
      ( (Description.Text "stores in " :: code_of (show_root root))
        @ [ Text ", which outlives this function," ],
        "A `mut` parameter stores only views that the function receives." )
  | Lends -> ([ Text "lends" ], "A method lends a view only of its parameters.")

let scrutinee_fix scrutinee =
  {
    Description.title =
      (Description.Text "Move " :: code_of (show_root scrutinee.Ownership.scrutinee))
      @ [ Text " with `own`." ];
    edits = [ Build.insert_before scrutinee.written [ Text "own " ] ];
  }

let show_scrutinee_view scrutinee =
  (if scrutinee.Ownership.is_part then [ Description.Text "part of " ] else [])
  @ code_of (show_root scrutinee.scrutinee)

let describe : Ownership.t -> Nodes.description = function
  | Conflicting_loan loan -> make Conflicting_loan (Build.at loan.at) (describe_loan loan)
  | Mutated_while_lent loan -> make Mutated_while_viewed (Build.at loan.at) (describe_loan loan)
  | Mutated_while_viewed { at = origin; place; verb; holder } ->
      make Mutated_while_viewed (Build.at origin)
        (code_of (show_place place)
        @ Description.Text (Printf.sprintf " cannot %s while " (show_verb verb))
          :: code_of (show_root holder)
        @ [ Text ", which views it, is still live." ])
  | Moved_out_of_lent { at = origin; copy } ->
      make Not_owned (Build.at origin) ~fixes:(copy_fix "Copy it." copy)
        [
          Text
            "This part is lent, so it cannot be moved: the loan ends when the statement ends. Copy \
             it instead.";
        ]
  | Arguments_overlap { at = range; exclusive; also; call; is_yielded } ->
      make Conflicting_loan (Build.over range)
        (if is_yielded then
           code_of (show_place exclusive)
           @ Description.Text " is lent `mut` to the yielded value, so "
             :: code_of (show_place also)
           @ [ Text " cannot be lent to it too." ]
         else
           code_of (show_place exclusive)
           @ (Description.Text " is passed `mut` to " :: Build.describe_call call)
           @ (Description.Text ", so the call cannot also use " :: code_of (show_place also))
           @ [ Text "." ])
  | View_argument_overlap { at = range; passed; call } ->
      make Conflicting_loan (Build.over range)
        (code_of (show_place passed)
        @ (Description.Text " is passed `mut` to " :: Build.describe_call call)
        @ [ Text ", so the call cannot also take a view of it." ])
  | Temporary_dropped_while_viewed { at = origin; holder } ->
      make Views_temporary (Build.at origin)
        [
          Text
            (Printf.sprintf
               "This temporary is dropped while %s may still store a view of it, which would \
                dangle. Bind the temporary to a name with `let`%s, so that it outlives the view."
               (show_holder holder)
               (match holder with
               | Some name -> Printf.sprintf " in the block that declares `%s`" name
               | None -> ""));
        ]
  | Dropped_while_viewed { at = origin; owner; holder } ->
      make View_escapes (Build.at origin)
        (code_of (show_root owner)
        @ [
            Text
              (Printf.sprintf
                 " is dropped at the end of its scope while %s may still store a view of it, which \
                  would dangle."
                 (show_holder holder));
          ])
  | Lent_part_bound { at = origin; copy } ->
      make Lent_part_escapes (Build.at origin)
        ~fixes:(copy_fix "Copy the scrutinee." copy)
        [
          Text
            "This part is lent only until the statement ends, so it cannot be bound to a name. Use \
             it in this statement, or copy it.";
        ]
  | Capturing_lambda_stored { at = origin } ->
      make View_escapes (Build.at origin)
        [
          Text
            "This lambda captures local variables, and the callee may store a function that it \
             takes through an `own` parameter, so the lambda could outlive them. Pass a function \
             that captures nothing.";
        ]
  | Unowned_function_stored { at = origin; viewed } ->
      make View_escapes (Build.at origin)
        (code_of (show_place viewed)
        @ [
            Text
              " is not owned here, so it may be a capturing lambda, and the callee may store a \
               function that it takes through an `own` parameter. Pass a function that captures \
               nothing.";
          ])
  | Dangling_view { at = origin; act; viewed; is_constant } ->
      let act, fix = describe_act act in
      make View_escapes (Build.at origin)
        ((Description.Text "This " :: act)
        @
        match viewed with
        | Captured_variables ->
            [
              Text
                (" a capturing lambda. A lambda's captured variables live in this function's stack \
                  frame, so the lambda would dangle. " ^ fix);
            ]
        | Temporary_view ->
            [
              Text
                (Printf.sprintf
                   " a view of a temporary, which is dropped before %s, so the view would dangle. \
                    %s"
                   (if is_constant then "its evaluation ends" else "the function returns")
                   fix);
            ]
        | View_of root ->
            (Description.Text " a view of " :: code_of (show_root root))
            @ [
                Text
                  (", which is dropped when the function returns, so the view would dangle. " ^ fix);
              ])
  | Returned_view_of_implementation { at = origin } ->
      make View_crosses_capability (Build.at origin)
        [
          Text
            "This returns a view of the capability implementation's own state. The caller cannot \
             see the implementation, so nothing stops the next call from mutating that state while \
             the view is in use. Return a copy.";
        ]
  | Stored_view_in_implementation { at = origin; viewed } ->
      make View_crosses_capability (Build.at origin)
        ((Description.Text "This stores a view of " :: code_of (show_root viewed))
        @ [
            Text
              " in a capability implementation. The caller cannot see the implementation, so it \
               could mutate or drop the view's original while the implementation still stores the \
               view. Store a copy.";
          ])
  | Self_referential_store { at = origin; root } ->
      make Self_referential (Build.at origin)
        ((Description.Text "This stores a view of a part of " :: code_of (show_root root))
        @ (Description.Text " in " :: code_of (show_root root))
        @ [
            Text
              " itself, which makes it self-referential. The caller does not know about the view, \
               so it could mutate that part and invalidate the view.";
          ])
  | Stored_view_of_borrowed { at = origin; parameter; holder; declaration } ->
      let shown_parameter = code_of (show_root parameter) in
      let fixes, advice =
        match declaration with
        | Some { type_node; view_type } ->
            ( [
                {
                  Description.title = [ Text "Declare it `view`." ];
                  edits = [ Build.insert_before type_node [ Text "view " ] ];
                };
              ],
              (Description.Text "Declare " :: shown_parameter)
              @ (Description.Text " as a view, as in `" :: show_root parameter)
              @ [
                  Text
                    (Printf.sprintf ": %s`, so that each caller keeps its argument borrowed."
                       (Types.show view_type));
                ] )
        | None ->
            ( [],
              (Description.Text "Take the stored part of " :: shown_parameter)
              @ [
                  Text
                    " as a view, such as a `view List` or a `view String`, so that each caller \
                     keeps its argument borrowed.";
                ] )
      in
      make View_escapes (Build.at origin) ~fixes
        ((Description.Text "This stores a view of " :: shown_parameter)
        @ (Description.Text " in " :: code_of (show_root holder))
        @ (Description.Text ", which outlives this function, but " :: shown_parameter)
        @ [
            Description.Text
              " is only borrowed for the call, and the caller does not expect it to stay borrowed \
               afterwards. ";
          ]
        @ advice)
  | Lent_owned_part { at = origin; part } ->
      make View_escapes (Build.at origin)
        (Description.Text "This lends a part of "
         ::
         (match part with
         | Temporary -> [ Text "a temporary" ]
         | root -> code_of (show_root root))
        @ [
            Text
              ", which the method owns and drops when it returns, so the part would dangle. Lend \
               the whole value, move the part out of it and lend that, or return the part.";
          ])
  | Lent_other_parameter { at = origin; root } ->
      let root = code_of (show_root root) in
      make Lends_other_parameter (Build.at origin)
        ((Description.Text "This lends a part of " :: root)
        @ [
            Description.Text
              ", which is not the method's first parameter. A caller keeps only the first argument \
               lent, so it could mutate or drop ";
          ]
        @ root
        @ [
            Text
              " while the part is lent. A method lends a part of its first parameter, a copy of a \
               `Plain` value, or a whole value that it made.";
          ])
  | Branch_data_race { at = origin; schedule; place } ->
      make Data_race (Build.at origin)
        (Description.Text
           (Printf.sprintf "Data race: one branch of this `%s` block mutates "
              (show_schedule schedule))
         :: code_of (show_place place)
        @ [ Text ", and another branch uses it." ])
  | Iteration_data_race { at = origin; schedule } ->
      make Data_race (Build.at origin)
        [
          Text
            (Printf.sprintf
               "Data race: the iterations of a `%s for` run at the same time, so the body can \
                mutate only its own element and its own locals."
               (show_schedule schedule));
        ]
  | Lent_element_race { at = origin; schedule; collection } ->
      make Data_race (Build.at origin)
        [
          Text
            (Printf.sprintf
               "Data race: the iterations of a `%s for` run at the same time, and each is lent an \
                element of %s to mutate. Only a `List` or an `Array` lends its elements to \
                iterations that run at the same time: its elements at different positions are \
                different places. Loop over a `mut` range of the collection's list, or use a `for` \
                loop."
               (show_schedule schedule)
               (match collection with
               | Some collection -> Printf.sprintf "`%s`" (Types.show collection)
               | None -> "the collection"));
        ]
  | Pulled_view { at = origin; element } ->
      make Task_outlives_view (Build.at origin)
        [
          Text
            (Printf.sprintf
               "Each iteration of a `concurrent for` runs as a task that outlives the pull that \
                started it. The element type `%s` is a view, and the next pull could mutate or \
                drop the value that it views, which would leave the task with a dangling view. Use \
                a `for` loop, or pull owned values."
               (Types.show element));
        ]
  | Lent_mut_in_variant { at = range; variant } ->
      make Lent_mut_in_variant (Build.over range)
        [
          Text
            (Printf.sprintf
               "This place is lent `mut` inside the variant `%s`. The caller could replace the \
                variant, and the place would be left without a value. Lend the place itself, and \
                give the caller another method that says whether the place is there."
               variant);
        ]
  | Needs_lent_mut { at = origin; place; copy } ->
      make Needs_lent_mut (Build.at origin)
        ~fixes:
          ({
             title = [ Text "Lend it `mut`." ];
             edits = [ Build.insert_before origin [ Text "mut " ] ];
           }
          :: copy_fix "Pass a copy." copy)
        (code_of (show_place place)
        @ [
            Text
              " is a place in a value that is lent `mut`, so the place is lent `mut` too. Pass it \
               `mut`, or pass a copy.";
          ])
  | Returned_view_of_scrutinee { at = origin; place; scrutinee; copy } ->
      make Needs_owned (Build.at origin)
        ~fixes:(scrutinee_fix scrutinee :: copy_fix "Return a copy." copy)
        ((Description.Text "A returned value must be owned, and " :: code_of (show_place place))
        @ (Description.Text " views " :: show_scrutinee_view scrutinee)
        @ (Description.Text ". Move " :: code_of (show_root scrutinee.scrutinee))
        @ (Description.Text " with `own` where " :: code_of (show_root place.root))
        @ [ Text " is bound, or return a copy." ])
  | Returned_unowned { at = origin; place; views_literal; copy } ->
      make Needs_owned (Build.at origin) ~fixes:(copy_fix "Return a copy." copy)
        ((Description.Text "A returned value must be owned, and " :: code_of (show_place place))
        @ [
            Text
              (Printf.sprintf " %s. Return a copy."
                 (if views_literal then "views a string literal" else "is not owned here"));
          ])
  | Moved_element { at = origin; place; copy } ->
      make Not_owned (Build.at origin) ~fixes:(copy_fix "Copy it." copy)
        (code_of (show_place place)
        @ [
            Text
              (Printf.sprintf
                 " is %s, which cannot be moved out of its collection. Copy it, or take it out \
                  with a method such as `remove`."
                 (match List.rev place.steps with
                 | Indexed :: _ -> "an element"
                 | Field _ :: _ | [] -> "part of an element"));
          ])
  | Moved_range { at = origin; place; copy; view_type } ->
      make Not_owned (Build.at origin) ~fixes:(copy_fix "Copy it." copy)
        (code_of (show_place place)
        @ [
            Text
              (Printf.sprintf
                 " is a range of a collection, and elements cannot be moved out of their \
                  collection. Copy it, or keep a view of it in a place of type `%s`."
                 (Types.show view_type));
          ])
  | Moved_constant { at = origin; place; copy } ->
      make Not_owned (Build.at origin) ~fixes:(copy_fix "Copy it." copy)
        (code_of (show_place place)
        @ [
            Text
              (Printf.sprintf " is %s, so it cannot be moved. Copy it instead."
                 (if place.steps = [] then "a constant" else "part of a constant"));
          ])
  | Moved_literal_view { at = origin; place; copy } ->
      make Not_owned (Build.at origin) ~fixes:(copy_fix "Copy it." copy)
        (code_of (show_place place)
        @ [
            Text
              " views a string literal, so it cannot be moved: its new owner would free the \
               literal's static buffer. Copy it instead.";
          ])
  | Moved_view_of_scrutinee { at = origin; place; scrutinee; copy } ->
      make Not_owned (Build.at origin)
        ~fixes:(scrutinee_fix scrutinee :: copy_fix "Copy it." copy)
        (code_of (show_place place)
        @ (Description.Text " views " :: show_scrutinee_view scrutinee)
        @ Description.Text ", so it cannot be moved. Move "
          :: code_of (show_root scrutinee.scrutinee)
        @ (Description.Text " with `own` where " :: code_of (show_root place.root))
        @ (Description.Text " is bound, or copy " :: code_of (show_place place))
        @ [ Text "." ])
  | Moved_view { at = origin; place; copy } ->
      make Not_owned (Build.at origin) ~fixes:(copy_fix "Copy it." copy)
        (code_of (show_place place)
        @ [
            Text
              (Printf.sprintf " is %s, so it cannot be moved. Copy it instead."
                 (if place.steps = [] then "a view" else "part of a view"));
          ])
  | Needs_own_keyword { at = origin; place; copy } ->
      make Needs_owned (Build.at origin)
        ~fixes:
          ({
             title = [ Text "Move it with `own`." ];
             edits = [ Build.insert_before origin [ Text "own " ] ];
           }
          :: copy_fix "Copy it." copy)
        ((Description.Text "An owned value is needed here, and " :: code_of (show_place place))
        @ [ Text " is a place. Pass it `own` to move it, or copy it." ])
  | Use_after_move { at = origin; place; moved; copy } ->
      make Use_after_move (Build.at origin)
        ~notes:[ (Build.at moved, code_of (show_place place) @ [ Text " is moved here." ]) ]
        ~fixes:(copy_fix "Pass a copy at the move instead." copy)
        (code_of (show_place place) @ [ Text " is used after it was moved." ])
  | Not_reinitialized_at_return { at = origin; moved; place } ->
      make Not_reinitialized (Build.at origin)
        ~notes:[ (Build.at moved, [ Text "It is moved out here." ]) ]
        (code_of (show_place place)
        @ [
            Text
              " is moved out and not reinitialized. The caller owns it, so assign it a value \
               before the function returns.";
          ])
  | Not_reinitialized_at_scope_end { moved; place } ->
      make Not_reinitialized (Build.at moved)
        (code_of (show_place place)
        @ Description.Text " is moved out here and not reinitialized. "
          :: code_of (show_root place.root)
        @ [
            Text
              " is lent `mut`, so every part of it must be initialized when its loop iteration, \
               its `match` arm, or its lambda ends.";
          ])
  | Not_reinitialized_in_branch { moved; place } ->
      make Not_reinitialized (Build.at moved)
        (code_of (show_place place)
        @ [
            Text
              " is moved out in this branch and not reinitialized in it. If another branch exits \
               the `concurrent` block early, the code after the block does not run, so each branch \
               must reinitialize each place lent `mut` that it moves out of.";
          ])
  | Resized_range { at = origin; call } ->
      make Resized_range (Build.at origin)
        ((Description.Text "This range is passed `mut` to " :: Build.describe_call call)
        @ [
            Text
              ", which may change the length of its argument, and a range has a fixed length. Pass \
               the whole list, or declare that the function changes only elements, with `modifies` \
               and `[..]`.";
          ])
  | Undeclared_change
      { at = origin; function_; parameter; part; last_entry; replaced_entry; removed_entries } ->
      let shown = Types.show_modified_part ~root:parameter part in
      let is_whole = part.field_path = [] && not part.is_elements in
      make Undeclared_change (Build.at origin)
        ~fixes:
          (match (replaced_entry, last_entry) with
          | _ when is_whole -> []
          | Some replaced, _ ->
              [
                {
                  title =
                    [
                      Text
                        (Printf.sprintf "Name `%s` in the `modifies` clause, in place of its parts."
                           shown);
                    ];
                  edits =
                    Build.replace replaced [ Text shown ]
                    :: List.map
                         (fun (entry, siblings) ->
                           Build.remove_entry { covering = [ entry ] } siblings)
                         removed_entries;
                };
              ]
          | None, Some last ->
              [
                {
                  title = [ Text (Printf.sprintf "Add `%s` to the `modifies` clause." shown) ];
                  edits = [ Build.insert_after last [ Text (", " ^ shown) ] ];
                };
              ]
          | None, None -> [])
        [
          Text
            (Printf.sprintf
               "%s changes here, and the `modifies` clause of `%s` does not name it. The proofs of \
                its callers take every part of `%s` that the clause does not name to keep its \
                value."
               (if is_whole then Printf.sprintf "All of `%s`" shown else Printf.sprintf "`%s`" shown)
               (Build.show_callee function_) parameter);
        ]
