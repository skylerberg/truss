type removal =
  | Wildcard
  | Field_wildcard
  | Field_deletion of { field : Core.origin; next : Core.origin }

type occurrence = { binding : Core.origin; removal : removal }

type t =
  | Unread_variable of { binding : Core.origin; name : string }
  | Unused_variable of {
      name : string;
      binding : occurrence;
      alternatives : occurrence list;
      constant : Path.t option;
    }
  | Unreachable_code of { first : Core.origin; last : Core.origin }
  | Self_comparison of {
      comparison : Core.origin;
      operand : Core.origin;
      operator : Language.Comparison.t;
      is_float : bool;
    }
  | Unused_run_forever of {
      function_ : Path.t;
      entry : Core.origin Description.range;
      siblings : Core.origin Description.siblings;
    }
  | Unmodified_part of {
      entry : Core.origin;
      function_ : Path.t;
      parameter : string;
      fields : string list;
      change : part_change;
    }
  | Unused_definition of {
      name : Core.origin;
      definition : Path.t;
      kind : definition_kind;
      visibility : visibility;
      is_used_by_unused : bool;
    }

and part_change =
  | Named_part_changed of Core.origin Description.siblings
  | Unnamed_part_changed
  | Parameter_unchanged

and definition_kind = Function | Constant
and visibility = Internal | Private

let make ?(severity = Diagnostic.Error) ?(fixes = []) code location message : Nodes.description =
  { code = Usage code; severity; location; message; notes = []; fixes }

let describe_removal name = function
  | Wildcard -> ("Replace it with `_`.", "Write `_`.")
  | Field_wildcard ->
      (Printf.sprintf "Match its field with `%s: _`." name, Printf.sprintf "Write `%s: _`." name)
  | Field_deletion _ ->
      ("Delete it, since `..` matches its field.", Printf.sprintf "Delete `%s`." name)

let make_removal_edit name (occurrence : occurrence) =
  match occurrence.removal with
  | Wildcard -> Build.replace occurrence.binding [ Text "_" ]
  | Field_wildcard -> Build.replace occurrence.binding [ Text (name ^ ": _") ]
  | Field_deletion { field; next } -> Build.delete (Start field) (Start next)

let show_comparison : Language.Comparison.t -> string * bool = function
  | Equal -> ("==", true)
  | Not_equal -> ("!=", false)
  | Less -> ("<", false)
  | Less_equal -> ("<=", true)
  | Greater -> (">", false)
  | Greater_equal -> (">=", true)

let describe_unused_definition ~name ~definition ~kind ~visibility ~is_used_by_unused =
  let code, noun =
    match kind with
    | Constant -> (Diagnostic.Code.Unused_constant, "constant")
    | Function -> (Unused_function, "function")
  and shown_visibility, severity =
    match visibility with
    | Internal -> ("internal", Diagnostic.Error)
    | Private -> ("private", Warning)
  in
  make code (Build.at name) ~severity
    [
      Text
        (if is_used_by_unused then
           Printf.sprintf "Only unused definitions use the %s %s `%s`. Delete it with them."
             shown_visibility noun (Path.show definition)
         else
           Printf.sprintf "Nothing in `%s` uses the %s %s `%s`. Delete it."
             (Path.show_package (Path.locate_package definition))
             shown_visibility noun (Path.show definition));
    ]

let describe = function
  | Unused_definition { name; definition; kind; visibility; is_used_by_unused } ->
      describe_unused_definition ~name ~definition ~kind ~visibility ~is_used_by_unused
  | Unread_variable { binding; name } ->
      make Unused_variable (Build.at binding)
        [
          Text
            (Printf.sprintf
               "`%s` is assigned but never read. Delete it and its assignments, or read it." name);
        ]
  | Unused_variable { name; binding; alternatives; constant } -> (
      let occurrences = binding :: alternatives in
      let instruction, title =
        match alternatives with
        | [] -> describe_removal name binding.removal
        | _ :: _ ->
            ( "Remove it from every alternative of the pattern.",
              Printf.sprintf "Remove `%s` from every alternative." name )
      in
      let removal =
        {
          Description.title = [ Text title ];
          edits = List.map (make_removal_edit name) occurrences;
        }
      in
      match constant with
      | Some constant ->
          let written = Path.show constant in
          let qualification =
            {
              Description.title = [ Text (Printf.sprintf "Write `%s`." written) ];
              edits =
                List.map
                  (fun (occurrence : occurrence) ->
                    Build.replace occurrence.binding [ Text written ])
                  occurrences;
            }
          in
          make Unused_variable (Build.at binding.binding) ~fixes:[ qualification; removal ]
            [
              Text
                (Printf.sprintf
                   "`%s` is never used. A bare name in a pattern binds a variable, which matches \
                    every value. To match the constant, write `%s`."
                   name written);
            ]
      | None ->
          make Unused_variable (Build.at binding.binding) ~fixes:[ removal ]
            [ Text (Printf.sprintf "`%s` is never used. %s" name instruction) ])
  | Unreachable_code { first; last } ->
      make Unreachable_code (Build.at first)
        ~fixes:
          [
            {
              title = [ Text "Delete the unreachable code." ];
              edits = [ Build.remove_lines { covering = [ first; last ] } ];
            };
          ]
        [ Text "This code is unreachable: the statement before it diverges." ]
  | Self_comparison { comparison; operand; operator; is_float } -> (
      let shown, is_always_true = show_comparison operator in
      let outcome =
        [
          Description.Text "`";
          Build.quote operand;
          Text (" " ^ shown ^ " ");
          Build.quote operand;
          Text (Printf.sprintf "` compares a value with itself, so it is always %b." is_always_true);
        ]
      in
      match operator with
      | (Equal | Not_equal) when is_float ->
          let test = [ Build.quote operand; Text ".is_nan()" ] in
          let replacement = if operator = Equal then Description.Text "!" :: test else test in
          make Self_comparison (Build.at comparison)
            ~fixes:
              [
                {
                  title = (Description.Text "Write `" :: replacement) @ [ Text "`." ];
                  edits = [ Build.replace comparison replacement ];
                };
              ]
            (outcome
            @ Description.Text
                " `==` treats every NaN as equal to itself, so a test for NaN calls `" :: test
            @ [ Text "`." ])
      | _ -> make Self_comparison (Build.at comparison) outcome)
  | Unused_run_forever { function_; entry; siblings } ->
      make Unused_run_forever (Build.over entry) ~severity:Warning
        ~fixes:
          [
            {
              title = [ Text "Remove `RunForever`" ];
              edits = [ Build.remove_entry entry siblings ];
            };
          ]
        [
          Text
            (Printf.sprintf
               "Nothing in `%s` may run forever, so its `RunForever` is unused. Remove it."
               (Path.show function_));
        ]
  | Unmodified_part { entry; function_; parameter; fields; change } ->
      let shown = Build.show_field_path parameter fields in
      let function_name = Build.show_function_name function_ in
      make Unmodified_part (Build.at entry) ~severity:Warning
        ~fixes:
          (match change with
          | Named_part_changed siblings ->
              [
                {
                  title = [ Text (Printf.sprintf "Remove `%s` from the `modifies` clause." shown) ];
                  edits = [ Build.remove_entry { covering = [ entry ] } siblings ];
                };
              ]
          | Unnamed_part_changed | Parameter_unchanged -> [])
        [
          Text
            (match change with
            | Named_part_changed _ | Unnamed_part_changed ->
                Printf.sprintf
                  "`%s` never changes `%s`, so the proofs of its callers do not learn that `%s` \
                   keeps its value. Remove it from `modifies`."
                  function_name shown shown
            | Parameter_unchanged ->
                Printf.sprintf
                  "`%s` changes no part of `%s` that its `modifies` clause names, nor any other: \
                   `%s` need not be `mut`."
                  function_name parameter parameter);
        ]

let binding = Build.example "binding"
and later = Build.example "later"
and next = Build.example "next"

and example_path =
  Path.Top
    { module_ = { package = { owner = None; name = "app" }; modules = [ "main" ] }; name = "f" }

let list_examples : Diagnostic.Code.usage -> t list = function
  | Unused_variable ->
      [
        Unread_variable { binding; name = "count" };
        Unused_variable
          {
            name = "count";
            binding = { binding; removal = Wildcard };
            alternatives = [];
            constant = None;
          };
        Unused_variable
          {
            name = "count";
            binding = { binding; removal = Field_wildcard };
            alternatives = [];
            constant = None;
          };
        Unused_variable
          {
            name = "count";
            binding = { binding; removal = Field_deletion { field = binding; next } };
            alternatives = [];
            constant = None;
          };
        Unused_variable
          {
            name = "count";
            binding = { binding; removal = Wildcard };
            alternatives = [ { binding = later; removal = Wildcard } ];
            constant = None;
          };
        Unused_variable
          {
            name = "lucky";
            binding = { binding; removal = Wildcard };
            alternatives = [];
            constant = Some example_path;
          };
      ]
  | Unreachable_code -> [ Unreachable_code { first = binding; last = later } ]
  | Self_comparison ->
      [
        Self_comparison { comparison = binding; operand = later; operator = Less; is_float = false };
        Self_comparison { comparison = binding; operand = later; operator = Equal; is_float = true };
      ]
  | Unused_run_forever ->
      [
        Unused_run_forever
          {
            function_ = example_path;
            entry = { covering = [ binding ] };
            siblings = Alone { clause = later; is_only_clause = true };
          };
      ]
  | Unused_function ->
      [
        Unused_definition
          {
            name = binding;
            definition = example_path;
            kind = Function;
            visibility = Private;
            is_used_by_unused = false;
          };
        Unused_definition
          {
            name = binding;
            definition = example_path;
            kind = Function;
            visibility = Internal;
            is_used_by_unused = true;
          };
      ]
  | Unmodified_part ->
      List.map
        (fun change ->
          Unmodified_part
            {
              entry = binding;
              function_ = example_path;
              parameter = "scanner";
              fields = [ "position" ];
              change;
            })
        [
          Named_part_changed (Next { covering = [ later ] });
          Unnamed_part_changed;
          Parameter_unchanged;
        ]
  | Unused_constant ->
      [
        Unused_definition
          {
            name = binding;
            definition = example_path;
            kind = Constant;
            visibility = Private;
            is_used_by_unused = false;
          };
      ]
