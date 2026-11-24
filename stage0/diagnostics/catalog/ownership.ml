type root =
  | Self
  | Named of string
  | Unnamed of Core.origin
  | Temporary
  | Constant of Path.t
  | Environment

type step = Field of string | Indexed
type place = { root : root; steps : step list }
type verb = Be_used | Be_passed_mut | Be_assigned | Be_moved
type lender = Loop | Provide_block | Rest_of_statement | Earlier_operand | Alias of root

type loan = {
  at : Core.origin;
  place : place;
  is_mut : bool;
  lender : lender;
  through : place option;
  verb : verb;
}

type copy = { moved : Core.origin; own_keyword : (Core.origin * Core.origin) option }
type dangling_act = Is | Returns | Stores_in of root | Lends
type dangling_view = Captured_variables | Temporary_view | View_of of root
type scrutinee = { scrutinee : root; written : Core.origin; is_part : bool }

type t =
  | Conflicting_loan of loan
  | Mutated_while_lent of loan
  | Mutated_while_viewed of { at : Core.origin; place : place; verb : verb; holder : root }
  | Moved_out_of_lent of { at : Core.origin; copy : copy option }
  | Arguments_overlap of {
      at : Core.origin Description.range;
      exclusive : place;
      also : place;
      call : Core.origin;
      is_yielded : bool;
    }
  | View_argument_overlap of {
      at : Core.origin Description.range;
      passed : place;
      call : Core.origin;
    }
  | Temporary_dropped_while_viewed of { at : Core.origin; holder : string option }
  | Dropped_while_viewed of { at : Core.origin; owner : root; holder : string option }
  | Lent_part_bound of { at : Core.origin; copy : copy option }
  | Capturing_lambda_stored of { at : Core.origin }
  | Unowned_function_stored of { at : Core.origin; viewed : place }
  | Dangling_view of {
      at : Core.origin;
      act : dangling_act;
      viewed : dangling_view;
      is_constant : bool;
    }
  | Returned_view_of_implementation of { at : Core.origin }
  | Stored_view_in_implementation of { at : Core.origin; viewed : root }
  | Self_referential_store of { at : Core.origin; root : root }
  | Stored_view_of_borrowed of { at : Core.origin; parameter : root; holder : root }
  | Lent_owned_part of { at : Core.origin; part : root }
  | Lent_other_parameter of { at : Core.origin; root : root }
  | Branch_data_race of { at : Core.origin; schedule : Language.Loop_mode.t; place : place }
  | Iteration_data_race of { at : Core.origin; schedule : Language.Loop_mode.t }
  | Lent_element_race of {
      at : Core.origin;
      schedule : Language.Loop_mode.t;
      collection : Types.ty option;
    }
  | Pulled_view of { at : Core.origin; element : Types.ty }
  | Lent_mut_in_variant of { at : Core.origin Description.range; variant : string }
  | Needs_lent_mut of { at : Core.origin; place : place; copy : copy option }
  | Returned_view_of_scrutinee of {
      at : Core.origin;
      place : place;
      scrutinee : scrutinee;
      copy : copy option;
    }
  | Returned_unowned of {
      at : Core.origin;
      place : place;
      views_literal : bool;
      copy : copy option;
    }
  | Moved_element of { at : Core.origin; place : place; copy : copy option }
  | Moved_constant of { at : Core.origin; place : place; copy : copy option }
  | Moved_literal_view of { at : Core.origin; place : place; copy : copy option }
  | Moved_view_of_scrutinee of {
      at : Core.origin;
      place : place;
      scrutinee : scrutinee;
      copy : copy option;
    }
  | Moved_view of { at : Core.origin; place : place; copy : copy option }
  | Needs_own_keyword of { at : Core.origin; place : place; copy : copy option }
  | Use_after_move of { at : Core.origin; place : place; moved : Core.origin; copy : copy option }
  | Not_reinitialized_at_return of { at : Core.origin; moved : Core.origin; place : place }
  | Not_reinitialized_at_scope_end of { moved : Core.origin; place : place }
  | Not_reinitialized_in_branch of { moved : Core.origin; place : place }
  | Undeclared_change of {
      at : Core.origin;
      function_ : Path.t;
      parameter : string;
      fields : string list;
      last_entry : Core.origin option;
    }

let make ?(notes = []) ?(fixes = []) code location message : Nodes.description =
  { code = Ownership code; severity = Error; location; message; notes; fixes }

let show_root = function
  | Self -> [ Description.Text "self" ]
  | Named name -> [ Text name ]
  | Unnamed origin -> [ Build.quote origin ]
  | Temporary -> [ Text "temporary" ]
  | Constant (Top { name; _ } | Member_constant { name; _ }) -> [ Text name ]
  | Constant path -> [ Text (Path.show path) ]
  | Environment -> [ Text "the lambda's captured variables" ]

let show_place place =
  show_root place.root
  @ List.map
      (function Field name -> Description.Text ("." ^ name) | Indexed -> Text "[...]")
      place.steps

let code_of pieces = (Description.Text "`" :: pieces) @ [ Text "`" ]

let show_verb = function
  | Be_used -> "be used"
  | Be_passed_mut -> "be passed `mut`"
  | Be_assigned -> "be assigned"
  | Be_moved -> "be moved"

let show_lender = function
  | Loop -> [ Description.Text "the loop" ]
  | Provide_block -> [ Text "the `provide` block" ]
  | Rest_of_statement -> [ Text "a lending call until this statement ends" ]
  | Earlier_operand -> [ Text "an earlier operand of this expression" ]
  | Alias root ->
      (Description.Text "a lending call until " :: code_of (show_root root))
      @ [ Text " goes out of scope" ]

let describe_loan loan =
  let through =
    match loan.through with
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
  | Some { moved; own_keyword } ->
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
  | Is -> ([ Description.Text "is" ], "A constant is a view only of another constant.")
  | Returns -> ([ Text "returns" ], "A function returns a view only of its parameters.")
  | Stores_in root ->
      ( (Description.Text "stores in " :: code_of (show_root root))
        @ [ Text ", which outlives this function," ],
        "A `mut` parameter stores only views that the function receives." )
  | Lends -> ([ Text "lends" ], "A method lends a view only of its parameters.")

let scrutinee_fix scrutinee =
  {
    Description.title =
      (Description.Text "Move " :: code_of (show_root scrutinee.scrutinee))
      @ [ Text " with `own`." ];
    edits = [ Build.insert_before scrutinee.written [ Text "own " ] ];
  }

let show_scrutinee_view scrutinee =
  (if scrutinee.is_part then [ Description.Text "part of " ] else [])
  @ code_of (show_root scrutinee.scrutinee)

let describe = function
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
  | Stored_view_of_borrowed { at = origin; parameter; holder } ->
      let parameter = code_of (show_root parameter) in
      make View_escapes (Build.at origin)
        ((Description.Text "This stores a view of " :: parameter)
        @ (Description.Text " in " :: code_of (show_root holder))
        @ (Description.Text ", which outlives this function, but " :: parameter)
        @ [
            Description.Text
              " is only borrowed for the call, and the caller does not expect it to stay borrowed \
               afterwards. Take ";
          ]
        @ parameter
        @ [ Text " as a view type, such as a `Slice`, to store a view of it." ])
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
                element of %s to mutate. Only a `List`, a `Slice`, or an `Array` lends its \
                elements to iterations that run at the same time: its elements at different \
                positions are different places. Loop over a `mut Slice` of the collection's \
                storage, or use a `for` loop."
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
  | Undeclared_change { at = origin; function_; parameter; fields; last_entry } ->
      let shown = Build.show_field_path parameter fields in
      make Undeclared_change (Build.at origin)
        ~fixes:
          (match (fields, last_entry) with
          | _ :: _, Some last ->
              [
                {
                  title = [ Text (Printf.sprintf "Add `%s` to the `modifies` clause." shown) ];
                  edits = [ Build.insert_after last [ Text (", " ^ shown) ] ];
                };
              ]
          | [], _ | _, None -> [])
        [
          Text
            (Printf.sprintf
               "%s changes here, and the `modifies` clause of `%s` does not name it. The proofs of \
                its callers take every part of `%s` that the clause does not name to keep its \
                value."
               (match fields with
               | [] -> Printf.sprintf "All of `%s`" shown
               | _ :: _ -> Printf.sprintf "`%s`" shown)
               (Build.show_function_name function_)
               parameter);
        ]

let origin = Build.example "origin"
let other = Build.example "other"
let count = { root = Named "count"; steps = [] }
let items = { root = Named "items"; steps = [ Field "first" ] }
let copy = Some { moved = origin; own_keyword = None }
let range = { Description.covering = [ origin; other ] }

let loan verb =
  { at = origin; place = items; is_mut = false; lender = Rest_of_statement; through = None; verb }

let scrutinee = { scrutinee = Named "pair"; written = other; is_part = true }

let list_examples : Diagnostic.Code.ownership -> t list = function
  | Conflicting_loan ->
      [
        Conflicting_loan { (loan Be_used) with is_mut = true };
        Arguments_overlap
          { at = range; exclusive = count; also = items; call = origin; is_yielded = false };
        Arguments_overlap
          { at = range; exclusive = count; also = items; call = origin; is_yielded = true };
        View_argument_overlap { at = range; passed = count; call = origin };
      ]
  | Mutated_while_viewed ->
      [
        Mutated_while_lent
          { (loan Be_assigned) with through = Some count; lender = Alias (Named "view") };
        Mutated_while_viewed
          { at = origin; place = items; verb = Be_passed_mut; holder = Named "view" };
      ]
  | Not_owned ->
      [
        Moved_out_of_lent { at = origin; copy };
        Moved_element { at = origin; place = { root = Named "items"; steps = [ Indexed ] }; copy };
        Moved_constant
          {
            at = origin;
            place = { root = Constant (Path.make_standard_path [ "math" ] "pi"); steps = [] };
            copy;
          };
        Moved_literal_view { at = origin; place = count; copy };
        Moved_view_of_scrutinee { at = origin; place = count; scrutinee; copy };
        Moved_view { at = origin; place = items; copy };
      ]
  | Views_temporary -> [ Temporary_dropped_while_viewed { at = origin; holder = Some "view" } ]
  | View_escapes ->
      [
        Dropped_while_viewed { at = origin; owner = Named "items"; holder = None };
        Capturing_lambda_stored { at = origin };
        Unowned_function_stored { at = origin; viewed = count };
        Dangling_view
          { at = origin; act = Returns; viewed = Captured_variables; is_constant = false };
        Dangling_view
          { at = origin; act = Stores_in Self; viewed = Temporary_view; is_constant = false };
        Dangling_view
          { at = origin; act = Lends; viewed = View_of (Named "items"); is_constant = false };
        Stored_view_of_borrowed { at = origin; parameter = Named "text"; holder = Self };
        Lent_owned_part { at = origin; part = Temporary };
      ]
  | Lent_part_escapes -> [ Lent_part_bound { at = origin; copy } ]
  | View_crosses_capability ->
      [
        Returned_view_of_implementation { at = origin };
        Stored_view_in_implementation { at = origin; viewed = Named "text" };
      ]
  | Self_referential -> [ Self_referential_store { at = origin; root = Self } ]
  | Lends_other_parameter -> [ Lent_other_parameter { at = origin; root = Named "other" } ]
  | Data_race ->
      [
        Branch_data_race { at = origin; schedule = Parallel; place = count };
        Iteration_data_race { at = origin; schedule = Concurrent };
        Lent_element_race { at = origin; schedule = Parallel; collection = None };
      ]
  | Task_outlives_view -> [ Pulled_view { at = origin; element = Types.make_builtin Int64 } ]
  | Lent_mut_in_variant -> [ Lent_mut_in_variant { at = range; variant = "Some" } ]
  | Needs_lent_mut -> [ Needs_lent_mut { at = origin; place = items; copy } ]
  | Needs_owned ->
      [
        Returned_view_of_scrutinee { at = origin; place = count; scrutinee; copy };
        Returned_unowned { at = origin; place = count; views_literal = false; copy };
        Needs_own_keyword { at = origin; place = count; copy };
      ]
  | Use_after_move -> [ Use_after_move { at = origin; place = count; moved = other; copy } ]
  | Not_reinitialized ->
      [
        Not_reinitialized_at_return { at = origin; moved = other; place = items };
        Not_reinitialized_at_scope_end { moved = other; place = items };
        Not_reinitialized_in_branch { moved = other; place = items };
      ]
  | Undeclared_change ->
      [
        Undeclared_change
          {
            at = origin;
            function_ = Build.example_path;
            parameter = "scanner";
            fields = [ "position" ];
            last_entry = Some other;
          };
        Undeclared_change
          {
            at = origin;
            function_ = Build.example_path;
            parameter = "scanner";
            fields = [];
            last_entry = None;
          };
      ]
