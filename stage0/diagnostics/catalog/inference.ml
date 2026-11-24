type shown = Some_integer | Some_float | Exactly of Types.ty
type decision_site = Use | Statement_end | Actual_head | Method_call
type mutation = Assignment | Passed_mut
type side = Left | Right

type decision = {
  name : Core.origin;
  decided : Types.ty;
  site : decision_site;
  decided_at : Core.origin;
  declares : bool;
}

type copy_edit =
  | Rename_copy of Core.origin
  | Append_copy of Core.origin
  | Wrap_copy of Core.origin

type view_copy = { copy_method : string; edit : copy_edit }
type widening = { side : side; operand : Core.origin; target : Types.ty }
type impl_need = { needing : Types.ty; condition : Types.trait_reference }

type unmet_bound =
  | Does_not_hold
  | Slice_lacks_mut_self
  | Associated_differs of { name : string; found : Types.ty }

type mismatch =
  | Expected of { expected : shown; actual : shown; copy : view_copy option }
  | Loop_element of { element : shown; annotated : shown }
  | Mismatched_integers of { left : Types.ty; right : Types.ty; widening : widening option }
  | Unsatisfied_bound of {
      of_type : Types.ty option;
      subject : Types.ty;
      bound : Types.trait_reference;
      unmet : unmet_bound;
      impl_need : impl_need option;
    }

type integer_subject = Potential | Decreases_measure | Cost_bound | Log_argument | Power_argument
type range_owner = Range_of_loop | Range_of_quantifier

type formula_construct =
  | Unreachable_expression
  | Break_expression
  | Continue_expression
  | Return_expression
  | Try_expression
  | Var_binding
  | For_statement
  | While_statement
  | Concurrent_block
  | Parallel_block

type owner = Variant_name of string | Type_named of Types.ty
type counted_callee = Fields_of of owner | Method_besides_self | Plain_function

type bare_owner =
  | Pattern_owner of { owner : owner; is_tuple_type : bool }
  | Construction_owner of owner

type method_owner =
  | Type_owner of { type_ : Types.ty; view : Types.ty option }
  | Named_owner of string
  | Path_owner of Path.t

type cost_callee =
  | Function_parameter of string
  | Bound_method of { self_type : Types.ty; method_ : string }
  | Unknown_callee

type cost_operand = { cost_function : Language.Metric.t; callee : cost_callee }

type not_callee =
  | Operand_is_neither
  | Local_of_type of { name : string; type_ : Types.ty }
  | Name_is_neither of string

type not_data = Function_type | Handle | Shared_state
type empty_literal = Empty_list | Empty_map
type stored_slice = Held_by of string | In_field | In_element | Lent_by_a_call
type integer_operator = Bitwise | Shift | Complement
type joined_piece = Fragment of Core.origin | Interpolated of Core.origin
type specification_call = Theorem_call | Mentions of Types.ty | Specification_function_call
type lambda_remedy = Bracket_arguments of { declared_on : Path.t; is_type : bool } | Typed_let
type specification_subject = Binding_subject of Core.origin | Value_subject

type undetermined =
  | Binding_type
  | Generic_argument of { parameter : string; is_type : bool; declared_on : Path.t }
  | List_element
  | Map_entries

type t =
  | Mismatch of { at : Core.origin; mismatch : mismatch; decision : decision option }
  | Integer_for_float of { at : Core.origin; wanted : shown; literals : (Core.origin * Z.t) list }
  | Decided_in_specification of { at : Core.origin; local : Core.origin option }
  | Operator_output of {
      at : Core.origin;
      found : Types.ty;
      wanted : Types.ty;
      impl_need : impl_need option;
    }
  | Operator_not_implemented of {
      at : Core.origin;
      subject : Types.ty;
      trait : Types.trait_reference;
      impl_need : impl_need option;
    }
  | Not_implemented of {
      at : Core.origin;
      subject : Types.ty;
      trait : Types.trait_reference;
      is_iteration : bool;
      impl_need : impl_need option;
    }
  | Body_ends_without_value of { body : Core.origin; output : Types.ty }
  | Last_statement_without_value of { statement : Core.origin; output : Types.ty }
  | Not_bit_vector of { at : Core.origin; type_ : Types.ty }
  | Unchecked_invariant of { at : Core.origin }
  | Argument_count of { at : Core.origin; callee : counted_callee; expected : int; given : int }
  | Label_in_indirect_call of { label : Core.origin; value : Core.origin }
  | Not_callable of { at : Core.origin; callee : shown }
  | Missing_parameter of { at : Core.origin; parameter : string }
  | Unknown_variant of {
      at : Core.origin;
      type_ : Types.ty;
      variant : string;
      candidates : string list;
    }
  | Variant_without_fields of { at : Core.origin; variant : string }
  | Not_a_record_construction of { at : Core.origin; type_ : Types.ty }
  | Opaque_construction of { at : Core.origin; type_ : Types.ty }
  | Mut_base_of_with of { at : Core.origin }
  | Unknown_label of {
      label : Core.origin;
      written : string;
      owner : owner option;
      candidates : string list;
    }
  | Positional_after_labeled of { argument : Core.origin; label : string option }
  | Tuple_argument_out_of_order of {
      argument : Core.origin;
      owner : owner;
      filled : string;
      field : string;
    }
  | Bare_value of {
      argument : Core.origin;
      owner : bare_owner;
      fields : string list;
      label : string option;
    }
  | Repeated_argument of { at : Core.origin; name : string; is_pattern : bool }
  | Not_an_integer of { at : Core.origin; subject : integer_subject; excluded : shown }
  | No_method of { at : Core.origin; owner : method_owner; name : string; candidates : string list }
  | Counted_not_a_capability of { at : Core.origin; written : string }
  | Counted_not_a_function of { at : Core.origin; name : string; type_ : Types.ty }
  | Counted_neither of { at : Core.origin; name : string }
  | Cost_of_other_metric of {
      at : Core.origin;
      operand : cost_operand;
      cost_function_name : Core.origin;
      bounded : Language.Metric.t;
    }
  | Cost_of_calls of { at : Core.origin; operand : cost_operand }
  | Upper_bound_in_exact_bound of { at : Core.origin; operand : cost_operand }
  | Unbounded_time of { clause : Core.origin; condition : Types.condition; has_condition : bool }
  | Clause_never_holds of { at : Core.origin }
  | Constant_out_of_range of {
      at : Core.origin;
      constant : Z.t;
      type_ : Types.ty;
      low : Z.t;
      high : Z.t;
    }
  | Division_by_zero of { at : Core.origin }
  | Default_not_constant of { at : Core.origin }
  | Not_constant of { at : Core.origin }
  | Condition_not_constant of { at : Core.origin }
  | Condition_names_parameter of { at : Core.origin }
  | Constant_not_data of { at : Core.origin; part : not_data }
  | Hidden_in_public_clause of { at : Core.origin; name : string; hidden : Path.t }
  | Float_too_large of { at : Core.origin; target : shown }
  | Runs_in_formula of { at : Core.origin; construct : formula_construct }
  | Self_outside_method of { at : Core.origin }
  | Self_type_as_value of { at : Core.origin }
  | Quantifier_over_type_in_code of { at : Core.origin }
  | Static_method_as_value of { at : Core.origin; name : string }
  | Method_with_type_arguments_as_value of { at : Core.origin }
  | String_indexed of { at : Core.origin }
  | Not_sliceable of { at : Core.origin; base : shown }
  | Not_indexable of { at : Core.origin; base : shown }
  | Several_indexes of { at : Core.origin }
  | Parameter_with_arguments of { at : Core.origin; name : string }
  | Type_arity of { at : Core.origin; type_path : Path.t; expected : int; given : int }
  | Associated_in_type_arguments of { at : Core.origin }
  | Not_a_type_argument of { at : Core.origin }
  | Hidden_member of { at : Core.origin; hidden : Path.t; visibility : Language.Visibility.t }
  | No_receiver_overload of { at : Core.origin; name : string }
  | Old_arity of { at : Core.origin; given : int }
  | Final_misused of { at : Core.origin }
  | Identical_arity of { at : Core.origin; given : int }
  | Not_a_function_or_type of { at : Core.origin; name : string }
  | Callback_ensures_in_code of { at : Core.origin; name : string }
  | Callback_ensures_label of { at : Core.origin; name : string }
  | Callback_ensures_arity of {
      at : Core.origin;
      name : string;
      inputs : Language.Mode.t list;
      has_result : bool;
      given : int;
    }
  | Ensures_of_non_parameter of { at : Core.origin; name : string }
  | Ensures_without_function of { at : Core.origin; base : shown }
  | Cost_operand_not_callee of {
      at : Core.origin;
      metric : Language.Metric.t;
      operand : not_callee;
    }
  | No_bound_method of { at : Core.origin; type_ : Types.ty; name : string }
  | Ambiguous_cost_method of {
      at : Core.origin;
      type_ : Types.ty;
      name : string;
      metric : Language.Metric.t;
    }
  | New_on_literal_type of {
      at : Core.origin;
      type_ : Types.ty;
      literal : empty_literal;
      call : Core.origin option;
    }
  | Ambiguous_static_method of {
      at : Core.origin;
      type_ : Types.ty;
      name : string;
      traits : Types.trait_reference list;
    }
  | Trait_arity of { at : Core.origin; trait : Types.trait_reference; expected : int; given : int }
  | Receiver_missing_in_full_call of { at : Core.origin }
  | Wrong_receiver_overload of {
      at : Core.origin;
      name : string;
      wanted : Path.receiver;
      overloads : Path.receiver list;
    }
  | Missing_receiver_mode of { receiver : Core.origin; name : string }
  | Ambiguous_method_call of {
      at : Core.origin;
      call : Core.origin;
      type_ : Types.ty;
      name : string;
      receiver : Core.origin;
      arguments : Core.origin Description.range list;
      traits : Types.trait_reference list;
    }
  | Index_not_mutable of { at : Core.origin; by : mutation; self_type : Types.ty; assigns : bool }
  | Stored_slice_written of { at : Core.origin; by : mutation; stored : stored_slice }
  | Slice_parameter_assigned of { at : Core.origin; parameter : string }
  | Slice_passed_to_generic of { at : Core.origin }
  | Mutation_in_formula of { at : Core.origin; by : mutation }
  | Captured_mutation of { at : Core.origin; by : mutation; name : string }
  | Read_only_mutation of { at : Core.origin; by : mutation; name : string }
  | Lent_read_only_assigned of { at : Core.origin }
  | Mode_on_assignment_target of {
      at : Core.origin;
      inner : Core.origin;
      keyword : Language.Mode.t;
    }
  | Not_assignable_place of { at : Core.origin }
  | Mode_on_read_argument of { at : Core.origin; inner : Core.origin; parameter : string }
  | Missing_mut_argument of { at : Core.origin; parameter : string }
  | Lent_read_only_argument of { at : Core.origin; parameter : string }
  | Temporary_passed_mut of { at : Core.origin; parameter : string }
  | Redundant_own of { at : Core.origin; inner : Core.origin; type_ : Types.ty }
  | Mut_for_own of { at : Core.origin; parameter : string }
  | Type_parameter_as_value of { at : Core.origin; name : string }
  | Theorem_as_value of { at : Core.origin; name : string }
  | Type_as_value of { at : Core.origin; name : string }
  | Trait_as_value of { at : Core.origin; name : string }
  | Specification_function_as_value of { at : Core.origin; name : string }
  | Variant_with_fields_as_function of { at : Core.origin; variant : string; fields : string list }
  | No_variants of { at : Core.origin; type_ : Types.ty }
  | Unknown_field of { at : Core.origin; base : shown; name : string; candidates : string list }
  | Opaque_field_read of { at : Core.origin; type_ : Types.ty }
  | Method_as_field of { at : Core.origin; name : string }
  | Lending_function_value of { at : Core.origin }
  | No_member of { at : Core.origin; type_ : Types.ty; name : string; view : string option }
  | Type_argument_count of { at : Core.origin; expected : int; given : int }
  | Type_for_value_argument of { at : Core.origin }
  | Value_for_type_argument of { at : Core.origin }
  | Specification_call_in_code of { at : Core.origin; name : string; call : specification_call }
  | Not_an_integer_operand of { at : Core.origin; operator : integer_operator; excluded : shown }
  | Shift_amount_not_unsigned of { at : Core.origin; excluded : shown }
  | Try_error_mismatch of { at : Core.origin; output_error : Types.ty; error : Types.ty }
  | Try_misused of { at : Core.origin }
  | Implies_in_code of { at : Core.origin }
  | String_addition of { at : Core.origin; join : (joined_piece * joined_piece) option }
  | Alternative_type_mismatch of {
      at : Core.origin;
      name : string;
      first : Types.ty;
      here : Types.ty;
    }
  | Range_pattern_type of { at : Core.origin; excluded : shown }
  | Variant_pattern_without_fields of { at : Core.origin; variant : string }
  | Parenthesized_tuple_pattern of {
      at : Core.origin;
      patterns : Core.origin Description.range;
      type_ : Types.ty;
    }
  | Not_a_record_pattern of { at : Core.origin; type_ : shown }
  | Not_a_tuple_type_pattern of { at : Core.origin; type_ : shown }
  | Tuple_pattern_arity of { at : Core.origin; type_ : Types.ty; fields : string list; given : int }
  | Tuple_pattern_for_record of {
      at : Core.origin;
      type_ : Types.ty;
      fields : string list;
      form : (string option * Core.origin) list option;
    }
  | Opaque_pattern of { at : Core.origin; type_ : Types.ty }
  | Tuple_pattern_out_of_order of {
      at : Core.origin;
      type_ : Types.ty;
      name : string;
      bound_field : string;
      reorder : string list option;
    }
  | Unmatched_fields of { at : Core.origin; missing : string list }
  | Not_structural of { at : Core.origin; type_ : Types.ty; constant : string }
  | Not_a_constant of { at : Core.origin }
  | Literal_does_not_fit of {
      at : Core.origin;
      number : Z.t;
      excluded : shown;
      low : Z.t;
      high : Z.t;
    }
  | Negated_unsigned of { at : Core.origin; excluded : shown; is_unsigned : bool }
  | Literal_fits_no_integer of { at : Core.origin; number : Z.t }
  | Character_literal of { at : Core.origin; tag : Language.Builtin_type.t }
  | Integer_pattern_type of { at : Core.origin; excluded : shown }
  | String_pattern_type of { at : Core.origin; type_ : Types.ty }
  | Capability_mismatch of {
      at : Core.origin;
      left : Types.capability_set;
      right : Types.capability_set;
    }
  | Undetermined of { at : Core.origin; undetermined : undetermined }
  | Types_undetermined of { at : Core.origin }
  | Trait_arguments_undetermined of { at : Core.origin; trait : Path.t }
  | Lambda_needs_type of { at : Core.origin; remedy : lambda_remedy }
  | Range_not_integer of { at : Core.origin; owner : range_owner; element : Types.ty }
  | Unused_value of { at : Core.origin; type_ : Types.ty }
  | Let_else_falls_through of { at : Core.origin }
  | Not_iterable_loop of { at : Core.origin; mode : Language.Mode.t; type_ : shown }
  | Cursor_not_cursor of { at : Core.origin; type_ : Types.ty; cursor : Types.ty }
  | Not_displayable of { at : Core.origin; type_ : Types.ty }
  | Template_part_conversion of {
      at : Core.origin;
      part_type : Types.ty;
      part : Types.ty;
      tag_type : Types.ty;
    }
  | Not_a_tag of { at : Core.origin; tag_type : Types.ty }
  | Tag_not_a_type of { at : Core.origin }
  | Array_length of { at : Core.origin; given : int; count : Z.t }
  | Lambda_arity of { at : Core.origin; given : int; function_type : Types.ty; expected : int }
  | Arm_pattern_count of { at : Core.origin; given : int; expected : int }
  | Not_iterable_quantifier of { at : Core.origin; type_ : shown }
  | Specification_only_type of {
      at : Core.origin;
      subject : specification_subject;
      type_ : Types.ty;
      specification_type : Types.ty;
    }

let raise_bug format = Compiler_bug.raise_bug ~stage:"Catalog" format

let make ?(fixes = []) ?(notes = []) code location message =
  { Description.code = Types code; severity = Error; location; message; notes; fixes }

let say text : _ Description.piece list = [ Text text ]
let fix title edits = { Description.title = say title; edits }
let show_count = Diagnostic.show_count
let show_owner = function Variant_name name -> name | Type_named type_ -> Types.show type_
let show_names names = String.concat ", " (List.map (fun name -> "`" ^ name ^ "`") names)

let show_shown = function
  | Some_integer -> "an integer"
  | Some_float -> "a float"
  | Exactly type_ -> "`" ^ Types.show type_ ^ "`"

let show_shown_capitalized shown = String.capitalize_ascii (show_shown shown)
let show_mode_keyword : Language.Mode.t -> string = function Mut -> "mut" | Own | Read -> "own"
let show_mutation = function Assignment -> "assigned" | Passed_mut -> "passed `mut`"

let code_of_mutation : mutation -> Diagnostic.Code.types = function
  | Assignment -> Not_assignable
  | Passed_mut -> Wrong_mode

let show_trait_name (trait : Path.t) =
  match trait with Top { name; _ } -> name | path -> Path.show path

let show_declaration : Path.t -> string = function
  | Method { owner; name; _ } -> Path.show_name owner ^ "." ^ name
  | path -> Path.show_name path

let write_bracket_remedy declared_on ~is_type =
  Printf.sprintf "Give `%s` its %s in brackets." (show_declaration declared_on)
    (if is_type then "type arguments" else "arguments")

let write_impl_need = function
  | Some { needing; condition } ->
      Printf.sprintf " Its impl needs `%s: %s`." (Types.show needing) (Types.show_trait condition)
  | None -> ""

let label_fix field argument =
  fix
    (Printf.sprintf "Label it `%s`." field)
    [ Build.insert_before argument [ Text (field ^ ": ") ] ]

let insert_mut_fix at = fix "Pass it `mut`." [ Build.insert_before at [ Text "mut " ] ]

let remove_keyword_fix at inner =
  fix "Remove the keyword." [ Build.delete (Start at) (Start inner) ]

let show_cost_callee = function
  | Function_parameter name -> name
  | Bound_method { self_type; method_ } -> Printf.sprintf "%s.%s" (Types.show self_type) method_
  | Unknown_callee -> "..."

let show_cost_operand { cost_function; callee } =
  Printf.sprintf "%s(%s)" (Language.Metric.show cost_function) (show_cost_callee callee)

let describe_associated (type_ : Types.ty) =
  match type_ with
  | Projection { base; trait; name } ->
      Printf.sprintf "the `%s` of `%s` under `%s`" name (Types.show base)
        (Types.show_trait { trait with associated = [] })
  | type_ -> Printf.sprintf "`%s`" (Types.show type_)

let explain_decision (site : decision_site) ~name ~decided =
  let took where =
    name @ [ Description.Text (Printf.sprintf " took its default type, `%s`, %s." decided where) ]
  in
  let needs user =
    (Description.Text (user ^ " needs the type of ") :: name)
    @ (Description.Text ", so " :: name)
    @ [ Text (Printf.sprintf " takes its default type `%s` here." decided) ]
  in
  let is_decided prefix =
    (Description.Text prefix :: name) @ [ Text (Printf.sprintf " is `%s`." decided) ]
  in
  match site with
  | Use ->
      ( is_decided "An earlier statement decided that the type of ",
        is_decided "This statement decides that the type of " )
  | Statement_end -> (took "at an earlier statement", needs "This statement")
  | Actual_head ->
      ( took "where the type of an earlier value was needed",
        (Description.Text "The type of this value is needed here, so " :: name)
        @ [ Text (Printf.sprintf " takes its default type `%s`." decided) ] )
  | Method_call -> (took "at an earlier method call", needs "Method lookup")

let describe_mismatch : mismatch -> Diagnostic.Code.types * string * Nodes.node Description.fix list
    = function
  | Expected { expected; actual; copy } ->
      let fixes =
        match copy with
        | Some { copy_method; edit } ->
            let title = Printf.sprintf "Copy the view with `%s()`." copy_method in
            [
              fix title
                [
                  (match edit with
                  | Rename_copy name -> Build.replace name [ Text copy_method ]
                  | Append_copy written ->
                      Build.insert_after written [ Text ("." ^ copy_method ^ "()") ]
                  | Wrap_copy written ->
                      Build.replace written
                        [
                          Text "("; Build.quote written; Text (Printf.sprintf ").%s()" copy_method);
                        ]);
                ];
            ]
        | None -> []
      in
      ( Mismatch,
        Printf.sprintf "Expected %s, found %s." (show_shown expected) (show_shown actual),
        fixes )
  | Loop_element { element; annotated } ->
      ( Mismatch,
        Printf.sprintf "Each element of this loop is %s, not %s." (show_shown element)
          (show_shown annotated),
        [] )
  | Mismatched_integers { left; right; widening } ->
      ( Mismatched_integers,
        Printf.sprintf
          "Integer types never convert implicitly: this compares or combines `%s` with `%s`."
          (Types.show left) (Types.show right),
        match widening with
        | Some { side; operand; target } ->
            [
              fix
                (Printf.sprintf "Convert the %s side to `%s`."
                   (match side with Left -> "left" | Right -> "right")
                   (Types.show target))
                [
                  Build.replace operand
                    [ Text (Types.show target ^ ".from_integer("); Build.quote operand; Text ")" ];
                ];
            ]
        | None -> [] )
  | Unsatisfied_bound { of_type; subject; bound; unmet; impl_need } ->
      let needs =
        Printf.sprintf "%s needs `%s: %s`"
          (match of_type with
          | Some type_ -> Printf.sprintf "`%s`" (Types.show type_)
          | None -> "This")
          (Types.show subject) (Types.show_trait bound)
      in
      ( Unsatisfied_bound,
        (match unmet with
          | Slice_lacks_mut_self ->
              needs
              ^ ", which does not hold: a slice implements no trait with a `mut self` method. \
                 Generic code could call the method on a copy of the slice, and a copy views the \
                 same elements."
          | Does_not_hold -> needs ^ ", which does not hold."
          | Associated_differs { name; found } ->
              Printf.sprintf "%s, and its `%s` is `%s`." needs name (Types.show found))
        ^ write_impl_need impl_need,
        [] )

let describe_undetermined at = function
  | Binding_type ->
      [
        Description.Text "The type of `";
        Build.quote at;
        Text "` cannot be inferred from this statement alone. Declare `";
        Build.quote at;
        Text "` with a type.";
      ]
  | Generic_argument { parameter; is_type; declared_on } ->
      say
        (Printf.sprintf "Nothing here determines `%s`, %s of `%s`. %s" parameter
           (if is_type then "a type parameter" else "a value parameter")
           (show_declaration declared_on)
           (write_bracket_remedy declared_on ~is_type))
  | List_element ->
      [
        Text "Nothing here determines the element type of `";
        Build.quote at;
        Text "`. Bind the list with a typed `let`, such as `let names: List[String] = []`.";
      ]
  | Map_entries ->
      [
        Text "Nothing here determines the key and value types of `";
        Build.quote at;
        Text "`. Bind the map with a typed `let`, such as `let ages: Map[String, UInt8] = [:]`.";
      ]

let show_construct = function
  | Unreachable_expression -> "`unreachable`"
  | Break_expression -> "`break`"
  | Continue_expression -> "`continue`"
  | Return_expression -> "`return`"
  | Try_expression -> "`?`"
  | Var_binding -> "A `var`"
  | For_statement -> "A `for` loop"
  | While_statement -> "A `while` loop"
  | Concurrent_block -> "A `concurrent` block"
  | Parallel_block -> "A `parallel` block"

let show_integer_subject = function
  | Potential -> "A `potential`"
  | Decreases_measure -> "A `decreases` measure"
  | Cost_bound -> "A cost bound"
  | Log_argument -> "An argument of `log`"
  | Power_argument -> "An argument of `power`"

let show_method_owner = function
  | Type_owner { type_; _ } -> Types.show type_
  | Named_owner name -> name
  | Path_owner path -> Path.show path

let write_labeled_form form =
  Description.Text "("
  :: List.concat
       (List.mapi
          (fun index (label, entry) ->
            (if index = 0 then [] else [ Description.Text ", " ])
            @ (match label with Some field -> [ Description.Text (field ^ ": ") ] | None -> [])
            @ [ Build.quote entry ])
          form)
  @ [ Text ")" ]

let describe = function
  | Mismatch { at = origin; mismatch; decision } -> (
      let code, message, fixes = describe_mismatch mismatch in
      match decision with
      | None -> make ~fixes code (Build.at origin) (say message)
      | Some { name; decided; site; decided_at; declares } ->
          let explanation, note =
            explain_decision site
              ~name:[ Text "`"; Build.quote name; Text "`" ]
              ~decided:(Types.show decided)
          in
          make
            ~fixes:
              (match site with Use -> fixes | Statement_end | Actual_head | Method_call -> [])
            ~notes:[ (Build.at decided_at, note) ]
            code (Build.at origin)
            ((Description.Text (message ^ " ") :: explanation)
            @
            if declares then [ Text " Declare `"; Build.quote name; Text "` with a type." ] else []
            ))
  | Integer_for_float { at = origin; wanted; literals } ->
      make Integer_for_float (Build.at origin)
        (Description.Text
           (Printf.sprintf "An integer literal is never a float, and %s is expected here. Write "
              (show_shown wanted))
         :: List.concat
              (List.mapi
                 (fun index (literal, number) ->
                   (if index = 0 then [] else [ Description.Text " and " ])
                   @ [
                       Text "`";
                       Build.quote literal;
                       Text (Printf.sprintf "` as `%s.0`" (Z.to_string number));
                     ])
                 literals)
        @ [ Text "." ])
  | Decided_in_specification { at = origin; local } ->
      make Decided_in_specification (Build.at origin)
        (match local with
        | Some local ->
            [
              Text "A specification cannot decide the type of `";
              Build.quote local;
              Text "`. Declare `";
              Build.quote local;
              Text "` with a type.";
            ]
        | None ->
            say
              "A specification cannot decide a type that code computes with. Give the call its \
               type arguments.")
  | Operator_output { at = origin; found; wanted; impl_need } ->
      make Mismatch (Build.at origin)
        (say
           ((match found with
              | Projection _ ->
                  Printf.sprintf "%s may differ from %s."
                    (String.capitalize_ascii (describe_associated found))
                    (describe_associated wanted)
              | found ->
                  Printf.sprintf "This operator gives `%s`, and %s is expected." (Types.show found)
                    (describe_associated wanted))
           ^ write_impl_need impl_need))
  | Operator_not_implemented { at = origin; subject; trait; impl_need } ->
      make No_impl (Build.at origin)
        (say
           (Printf.sprintf "`%s` does not implement `%s`, so the operator does not apply.%s"
              (Types.show subject) (Types.show_trait trait) (write_impl_need impl_need)))
  | Not_implemented { at = origin; subject; trait; is_iteration; impl_need } ->
      make
        (if is_iteration then Not_iterable else No_impl)
        (Build.at origin)
        (say
           (Printf.sprintf "`%s` does not implement `%s`.%s" (Types.show subject)
              (Types.show_trait trait) (write_impl_need impl_need)))
  | Body_ends_without_value { body; output } ->
      make Mismatch (Build.after body)
        (say (Printf.sprintf "This body must end with a value of type `%s`." (Types.show output)))
  | Last_statement_without_value { statement; output } ->
      make Mismatch (Build.at statement)
        (say (Printf.sprintf "This body must end with a value of type `%s`." (Types.show output)))
  | Not_bit_vector { at = origin; type_ } ->
      make Not_bit_vector (Build.at origin)
        (say
           (Printf.sprintf
              "An assertion `by bit_vector` can name only integers and booleans, and this is a \
               `%s`."
              (Types.show type_)))
  | Unchecked_invariant { at = origin } ->
      make Cannot_derive (Build.at origin)
        (say
           "This invariant cannot be checked at run time, so `serialization.Deserialize` cannot be \
            derived: a value read from data might break it. Write the `impl`, which checks the \
            value another way.")
  | Argument_count { at = origin; callee; expected; given } ->
      let given_text = show_count given "is" "are" in
      make
        (if given < expected then Missing_argument else Too_many_arguments)
        (Build.at origin)
        (say
           (match callee with
           | Fields_of owner ->
               Printf.sprintf "`%s` has %s, and %s given." (show_owner owner)
                 (show_count expected "field" "fields")
                 (show_count given "argument is" "arguments are")
           | Method_besides_self ->
               Printf.sprintf "This method takes %s besides `self`, and %s given."
                 (show_count expected "argument" "arguments")
                 given_text
           | Plain_function ->
               Printf.sprintf "This function takes %s, and %s given."
                 (show_count expected "argument" "arguments")
                 given_text))
  | Label_in_indirect_call { label; value } ->
      make Unknown_label (Build.at label)
        ~fixes:[ fix "Remove the label." [ Build.delete (Start label) (Start value) ] ]
        (say "A call through a function value passes its arguments by position, without labels.")
  | Not_callable { at = origin; callee } ->
      make Not_callable (Build.at origin)
        (say
           (Printf.sprintf "%s is not a function, so it cannot be called."
              (show_shown_capitalized callee)))
  | Missing_parameter { at = origin; parameter } ->
      make Missing_argument (Build.at origin)
        (say (Printf.sprintf "`%s` is not given, and has no default." parameter))
  | Unknown_variant { at = origin; type_; variant; candidates } ->
      make Unknown_variant (Build.at origin)
        ~fixes:(Build.list_spelling_fixes origin ~written:variant candidates)
        (say (Printf.sprintf "`%s` has no variant `%s`." (Types.show type_) variant))
  | Variant_without_fields { at = origin; variant } ->
      make Too_many_arguments (Build.at origin) (say (Printf.sprintf "`%s` has no fields." variant))
  | Not_a_record_construction { at = origin; type_ } ->
      make Not_a_record (Build.at origin)
        (say
           (Printf.sprintf "`%s` is not a record, so it cannot be built this way."
              (Types.show type_)))
  | Opaque_construction { at = origin; type_ } ->
      make Private_field (Build.at origin)
        (say
           (Printf.sprintf "`%s` is opaque, so only its own package can build it."
              (Types.show type_)))
  | Mut_base_of_with { at = origin } ->
      make Wrong_mode (Build.at origin)
        (say "`with` takes ownership of its base, so the base is passed `own`, not `mut`.")
  | Unknown_label { label; written; owner; candidates } ->
      make Unknown_label (Build.at label)
        ~fixes:(Build.list_spelling_fixes label ~written candidates)
        (say
           (match owner with
           | None -> Printf.sprintf "No parameter is named `%s`." written
           | Some owner -> Printf.sprintf "`%s` has no field `%s`." (show_owner owner) written))
  | Positional_after_labeled { argument; label } ->
      make Positional_after_labeled (Build.at argument)
        ~fixes:(Option.to_list (Option.map (fun field -> label_fix field argument) label))
        (say
           "A positional argument cannot follow a labeled argument. Label it, or move it before \
            the labeled arguments.")
  | Tuple_argument_out_of_order { argument; owner; filled; field } ->
      make Out_of_order (Build.at argument)
        ~fixes:[ label_fix field argument ]
        [
          Text (Printf.sprintf "`%s` is a tuple type, built by position, so `" (show_owner owner));
          Build.quote argument;
          Text
            (Printf.sprintf
               "` here fills the field `%s`. Label it, or move it to the position of `%s`." filled
               field);
        ]
  | Bare_value { argument; owner; fields; label } ->
      make Missing_label (Build.at argument)
        ~fixes:(Option.to_list (Option.map (fun field -> label_fix field argument) label))
        (say
           (match owner with
           | Pattern_owner { owner; is_tuple_type } ->
               Printf.sprintf
                 "A bare pattern must name a field, since `%s` has %d fields: %s. In parentheses, \
                  fields match by name.%s"
                 (show_owner owner) (List.length fields) (show_names fields)
                 (if is_tuple_type then
                    " A list of patterns without parentheses, after `let`, `var`, or `for`, \
                     matches the fields of this tuple type by position."
                  else "")
           | Construction_owner owner ->
               Printf.sprintf
                 "`%s` has %d fields: %s. Fields have no order, so every argument needs a label, \
                  or a variable with its field's name."
                 (show_owner owner) (List.length fields) (show_names fields)))
  | Repeated_argument { at = origin; name; is_pattern } ->
      make Repeated_argument (Build.at origin)
        (say
           (Printf.sprintf "`%s` is %s more than once." name
              (if is_pattern then "matched" else "given")))
  | Not_an_integer { at = origin; subject; excluded } ->
      make Mismatch (Build.at origin)
        (say
           (Printf.sprintf "%s is an integer, not %s." (show_integer_subject subject)
              (show_shown excluded)))
  | No_method { at = origin; owner; name; candidates } ->
      make Unknown_member (Build.at origin)
        ~fixes:(Build.list_spelling_fixes origin ~written:name candidates)
        (say
           (match owner with
           | Type_owner { type_; view = Some view } ->
               Printf.sprintf "`%s` has no method `%s`, and neither has its view `%s`."
                 (Types.show type_) name (Types.show view)
           | owner -> Printf.sprintf "`%s` has no method `%s`." (show_method_owner owner) name))
  | Counted_not_a_capability { at = origin; written } ->
      make Not_a_capability (Build.at origin)
        (say
           (Printf.sprintf "`calls` counts the calls of a capability, and `%s` is not one." written))
  | Counted_not_a_function { at = origin; name; type_ } ->
      make Not_callable (Build.at origin)
        (say
           (Printf.sprintf "`calls` counts the calls through a function, and `%s` is a `%s`." name
              (Types.show type_)))
  | Counted_neither { at = origin; name } ->
      make Not_callable (Build.at origin)
        (say
           (Printf.sprintf
              "`calls` counts the calls of a capability or through a function parameter, and `%s` \
               is neither."
              name))
  | Cost_of_other_metric { at = origin; operand; cost_function_name; bounded } ->
      let bounded = Language.Metric.show bounded in
      make Cost_of_other_resource (Build.at origin)
        ~fixes:
          [
            fix
              (Printf.sprintf "Write `%s`." bounded)
              [ Build.replace cost_function_name [ Text bounded ] ];
          ]
        (say
           (Printf.sprintf
              "`%s` bounds the `%s` of one call, not its `%s`, which this clause bounds. Write \
               `%s(%s)`."
              (show_cost_operand operand)
              (Language.Metric.show operand.cost_function)
              bounded bounded (show_cost_callee operand.callee)))
  | Cost_of_calls { at = origin; operand } ->
      make Cost_of_other_resource (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` bounds the `%s` of one call, not the calls it makes, which this clause counts."
              (show_cost_operand operand)
              (Language.Metric.show operand.cost_function)))
  | Upper_bound_in_exact_bound { at = origin; operand } ->
      make Upper_bound_in_exact_bound (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` is an upper bound on one call, and a call may spend less, so an exact amount \
               that names it would be false for that call. State this bound with `<=` or `O(...)`."
              (show_cost_operand operand)))
  | Unbounded_time { clause; condition; has_condition } ->
      let shown = Types.show_condition condition in
      let added = (if has_condition then "&& " else "when ") ^ shown in
      make Unbounded_time (Build.at clause)
        ~fixes:
          [
            fix
              (Printf.sprintf "Add `%s`." added)
              [ Build.insert_after clause [ Text (" " ^ added) ] ];
          ]
        (say
           (Printf.sprintf
              "This function uses `RunForever unless %s`, so it may run forever where the \
               condition does not hold, and a `time` clause bounds it only `when` a condition that \
               implies `%s`."
              shown shown))
  | Clause_never_holds { at = origin } ->
      make Decided_condition (Build.at origin)
        (say
           "This clause's condition never holds where it is written, so the clause would bind \
            nothing. Remove the clause, or name a type parameter in its condition.")
  | Constant_out_of_range { at = origin; constant; type_; low; high } ->
      make Constant_overflow (Build.at origin)
        (say
           (Printf.sprintf "This is %s, which does not fit in `%s`, which holds %s to %s."
              (Z.to_string constant) (Types.show type_) (Z.to_string low) (Z.to_string high)))
  | Division_by_zero { at = origin } ->
      make Constant_overflow (Build.at origin) (say "This divides by zero.")
  | Default_not_constant { at = origin } ->
      make Default_not_constant (Build.at origin)
        (say
           "A default must be a constant expression: literals, arithmetic, constants, and records, \
            variants, and collections built from them. It cannot call a function or name a \
            parameter.")
  | Not_constant { at = origin } ->
      make Not_constant (Build.at origin)
        (say
           "The value of a constant is made of literals, other constants, operators, calls, \
            quantifiers over ranges and collections, and the records, variants, collections, and \
            strings built from them. Move this into a function, and call the function here.")
  | Condition_not_constant { at = origin } ->
      make Condition_not_constant (Build.at origin)
        (say
           "An assertion `by evaluation` is evaluated when the code is checked, before any \
            variable has a value. Its condition is made of literals, constants, operators, calls, \
            quantifiers over ranges and collections, and the records, variants, collections, and \
            strings built from them. Move this into a function, and call the function here.")
  | Condition_names_parameter { at = origin } ->
      make Condition_not_constant (Build.at origin)
        (say
           "An assertion `by evaluation` is evaluated once, when the code is checked, so its \
            condition cannot mention a type parameter or a value parameter of the code around it.")
  | Constant_not_data { at = origin; part } ->
      make Constant_not_data (Build.at origin)
        (say
           (Printf.sprintf
              "A constant is stored in the compiled program as data, so its type cannot be or hold \
               %s."
              (match part with
              | Function_type -> "a function type"
              | Handle -> "a handle"
              | Shared_state -> "state that tasks share")))
  | Hidden_in_public_clause { at = origin; name; hidden } ->
      let hidden = Path.show hidden in
      make Private_in_public (Build.at origin)
        (say
           (Printf.sprintf
              "Other packages can call `%s`, so the proofs of its callers there read this clause, \
               and those packages cannot see `%s`. Make `%s` public, or state the clause with \
               functions and constants that are public."
              name hidden hidden))
  | Float_too_large { at = origin; target } ->
      make Literal_out_of_range (Build.at origin)
        (say
           (Printf.sprintf "This literal is too large for %s; it would round to infinity."
              (show_shown target)))
  | Runs_in_formula { at = origin; construct } ->
      make Not_in_specification (Build.at origin)
        (say
           (Printf.sprintf
              "%s runs, so it cannot be part of a specification, a proof, or a quantifier's body, \
               which the prover reads as formulas: they are built from `let`, `if`, `match`, and \
               calls."
              (show_construct construct)))
  | Self_outside_method { at = origin } ->
      make Not_a_value (Build.at origin)
        (say "`self` is a method's receiver, and this is not a method that takes one.")
  | Self_type_as_value { at = origin } ->
      make Not_a_value (Build.at origin)
        (say "`Self` is a type. Build a value of it, or call one of its methods.")
  | Quantifier_over_type_in_code { at = origin } ->
      make Specification_only (Build.at origin)
        (say
           "A quantifier over a whole type cannot run, so it is only for specifications and the \
            bodies of functions for specifications only. Quantify over a range or a collection.")
  | Static_method_as_value { at = origin; name } ->
      make Not_a_value (Build.at origin)
        (say (Printf.sprintf "`%s` is a method; call it with `(...)`." name))
  | Method_with_type_arguments_as_value { at = origin } ->
      make Not_a_value (Build.at origin)
        (say "A method with type arguments is called: write `(...)` after it.")
  | String_indexed { at = origin } ->
      make Not_indexable (Build.at origin)
        (say "Strings cannot be indexed: say which you mean with `bytes()` or `characters()`.")
  | Not_sliceable { at = origin; base } ->
      make Not_indexable (Build.at origin)
        (say (Printf.sprintf "%s cannot be sliced." (show_shown_capitalized base)))
  | Not_indexable { at = origin; base } ->
      make Not_indexable (Build.at origin)
        (say (Printf.sprintf "%s cannot be indexed." (show_shown_capitalized base)))
  | Several_indexes { at = origin } ->
      make Not_indexable (Build.at origin) (say "An index is one value.")
  | Parameter_with_arguments { at = origin; name } ->
      make Arity (Build.at origin)
        (say (Printf.sprintf "`%s` is a generic parameter, which takes no arguments." name))
  | Type_arity { at = origin; type_path; expected; given } ->
      make Arity (Build.at origin)
        (say
           (Printf.sprintf "`%s` takes %s, and %s given."
              (Types.show (Named { path = type_path; arguments = [] }))
              (show_count expected "argument" "arguments")
              (show_count given "is" "are")))
  | Associated_in_type_arguments { at = origin } ->
      make Arity (Build.at origin)
        (say
           "An associated type is fixed in a bound, as in `Source: Cursor[Element = Int64]`, not \
            among type arguments in an expression.")
  | Not_a_type_argument { at = origin } ->
      make Not_a_type (Build.at origin) (say "A type argument is a type, or a `UInt64` value.")
  | Hidden_member { at = origin; hidden; visibility } ->
      make Member_not_visible (Build.at origin) (say (Build.write_hidden hidden visibility))
  | No_receiver_overload { at = origin; name } ->
      make Wrong_receiver (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` has no overload for this receiver's mode; pass the receiver `mut` or `own` as \
               its overloads take."
              name))
  | Old_arity { at = origin; given } ->
      make
        (if given = 0 then Missing_argument else Too_many_arguments)
        (Build.at origin)
        (say "`old` takes one value: `old(value)`.")
  | Final_misused { at = origin } ->
      make Not_callable (Build.at origin)
        (say
           "`final` takes the part that a lending method lends: `final(result)` is that part as \
            the caller left it.")
  | Identical_arity { at = origin; given } ->
      make
        (if given < 2 then Missing_argument else Too_many_arguments)
        (Build.at origin)
        (say "`identical` takes two values of one type.")
  | Not_a_function_or_type { at = origin; name } ->
      make Not_callable (Build.at origin)
        (say (Printf.sprintf "`%s` is not a function or a type, so it cannot be called." name))
  | Callback_ensures_in_code { at = origin; name } ->
      make Specification_only (Build.at origin)
        (say
           (Printf.sprintf
              "`%s.ensures` names the postcondition of the function passed for `%s`, so it appears \
               only in specifications."
              name name))
  | Callback_ensures_label { at = origin; name } ->
      make Unknown_label (Build.at origin)
        (say
           (Printf.sprintf
              "`%s.ensures` takes its arguments by position, as a call through `%s` does." name name))
  | Callback_ensures_arity { at = origin; name; inputs; has_result; given } ->
      let shape =
        List.concat_map
          (fun (mode : Language.Mode.t) ->
            match mode with
            | Mut -> [ "its value at entry"; "its value at exit" ]
            | Read | Own -> [ "an input" ])
          inputs
        @ if has_result then [ "the result" ] else []
      in
      let expected = List.length shape in
      make
        (if given < expected then Missing_argument else Too_many_arguments)
        (Build.at origin)
        (say
           (Printf.sprintf "`%s.ensures` takes %d %s: %s." name expected
              (if expected = 1 then "argument" else "arguments")
              (if shape = [] then "none" else String.concat ", " shape)))
  | Ensures_of_non_parameter { at = origin; name } ->
      make Not_callable (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` is not a parameter of this definition, and `.ensures` names the postcondition \
               of the function passed for a function parameter, as in `transform.ensures(value, \
               output)`."
              name))
  | Ensures_without_function { at = origin; base } ->
      make Not_callable (Build.at origin)
        (say
           (Printf.sprintf
              "`.ensures` follows a function parameter, as in `transform.ensures(value, output)`, \
               and this is %s."
              (show_shown base)))
  | Cost_operand_not_callee { at = origin; metric; operand } ->
      let cost_function = Language.Metric.show metric in
      make Not_callable (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` takes a function parameter, as in `%s(visit)`, or a method of a bound, as in \
               `%s(Element.equal)`, and %s."
              cost_function cost_function cost_function
              (match operand with
              | Operand_is_neither -> "its operand is neither"
              | Local_of_type { name; type_ } ->
                  Printf.sprintf "`%s` is a `%s`" name (Types.show type_)
              | Name_is_neither name -> Printf.sprintf "`%s` is neither" name)))
  | No_bound_method { at = origin; type_; name } ->
      make Unknown_member (Build.at origin)
        (say
           (Printf.sprintf "`%s` has no method `%s`: no trait that bounds it declares one."
              (Types.show type_) name))
  | Ambiguous_cost_method { at = origin; type_; name; metric } ->
      make Ambiguous_method (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` has more than one method `%s`, and none of them is the only one that takes \
               `self` read-only, so `%s` cannot tell which one is meant."
              (Types.show type_) name (Language.Metric.show metric)))
  | New_on_literal_type { at = origin; type_; literal; call } ->
      let literal = match literal with Empty_list -> "[]" | Empty_map -> "[:]" in
      make Unknown_member (Build.at origin)
        ~fixes:
          (Option.to_list
             (Option.map
                (fun call ->
                  fix (Printf.sprintf "Write `%s`." literal) [ Build.replace call [ Text literal ] ])
                call))
        (say
           (Printf.sprintf "`%s` has no method `new`. The literal `%s` is an empty `%s`."
              (Types.show type_) literal (Types.show type_)))
  | Ambiguous_static_method { at = origin; type_; name; traits } ->
      make Ambiguous_method (Build.at origin)
        (say
           (Printf.sprintf
              "More than one trait gives `%s` a method `%s`: %s. Call it through the trait to say \
               which."
              (Types.show type_) name
              (String.concat ", "
                 (List.map (fun trait -> "`" ^ Types.show_trait trait ^ "`") traits))))
  | Trait_arity { at = origin; trait; expected; given } ->
      make Arity (Build.at origin)
        (say
           (Printf.sprintf "`%s` takes %s, and %s given." (Types.show_trait trait)
              (show_count expected "type argument" "type arguments")
              (show_count given "is" "are")))
  | Receiver_missing_in_full_call { at = origin } ->
      make Missing_argument (Build.at origin)
        (say "A method written in full takes its receiver as its first argument, without a label.")
  | Wrong_receiver_overload { at = origin; name; wanted; overloads } ->
      make Wrong_receiver (Build.at origin)
        (say
           (Printf.sprintf "`%s` has no overload that takes %s here; it has %s." name
              (Path.show_receiver wanted)
              (String.concat ", " (List.map Path.show_receiver overloads))))
  | Missing_receiver_mode { receiver; name } ->
      make Missing_mode (Build.at receiver)
        ~fixes:[ insert_mut_fix receiver ]
        (say
           (Printf.sprintf "`%s` takes `mut self`, so the call site passes its receiver `mut`." name))
  | Ambiguous_method_call { at = origin; call; type_; name; receiver; arguments; traits } ->
      make Ambiguous_method (Build.at origin)
        ~fixes:
          (List.map
             (fun (trait : Types.trait_reference) ->
               let trait_name = show_trait_name trait.trait in
               fix
                 (Printf.sprintf "Call `%s`'s `%s`." trait_name name)
                 [
                   Build.replace call
                     (Description.Text (Printf.sprintf "%s.%s(" trait_name name)
                      :: Build.quote receiver
                      :: List.concat_map
                           (fun argument -> [ Description.Text ", "; Build.quote_over argument ])
                           arguments
                     @ [ Text ")" ]);
                 ])
             traits)
        (say
           (Printf.sprintf
              "More than one trait gives `%s` a method `%s`. Write the call in full to say which."
              (Types.show type_) name))
  | Index_not_mutable { at = origin; by; self_type; assigns } ->
      make (code_of_mutation by) (Build.at origin)
        (say
           (Printf.sprintf
              "An element of `%s` cannot be mutated in place: `%s` implements `Index`, which lends \
               an element read-only, and not `IndexMut`.%s"
              (Types.show self_type) (Types.show self_type)
              (if assigns then " Assign the whole element with `=`." else "")))
  | Stored_slice_written { at = origin; by; stored } ->
      make (code_of_mutation by) (Build.at origin)
        (say
           (Printf.sprintf
              "%s, so its elements cannot be written through it: a slice held in a variable, a \
               field, or an element may alias another view of the same elements. Write through a \
               range of the collection, as in `mut items[1..]`, or through a `mut Slice` \
               parameter."
              (match stored with
              | Held_by name -> Printf.sprintf "`%s` holds a slice" name
              | In_field -> "This slice is held in a field"
              | In_element -> "This slice is an element of a collection"
              | Lent_by_a_call -> "This slice is lent by a call")))
  | Slice_parameter_assigned { at = origin; parameter } ->
      make Not_assignable (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` is a `mut` slice parameter, so it cannot be assigned: the caller lends it \
               write access to a range of elements, and a different slice would carry that access \
               to elements the caller did not lend. Write its elements instead."
              parameter))
  | Slice_passed_to_generic { at = origin } ->
      make Wrong_mode (Build.at origin)
        (say
           "A slice is passed `mut` only to a `mut Slice` parameter, and this parameter's declared \
            type is a type parameter or an associated type. The callee could assign it a different \
            slice, which would leave the elements the caller lent unchanged while its contract \
            describes them as written.")
  | Mutation_in_formula { at = origin; by } ->
      make Not_in_specification (Build.at origin)
        (say
           (Printf.sprintf
              "Nothing in a specification, a proof, or a quantifier's body can be %s: the prover \
               reads them as formulas, which mutate nothing."
              (show_mutation by)))
  | Captured_mutation { at = origin; by; name } ->
      make (code_of_mutation by) (Build.at origin)
        (say
           (Printf.sprintf
              "A lambda cannot mutate its captures, and `%s` is from outside it. Return the new \
               value instead, or use a loop."
              name))
  | Read_only_mutation { at = origin; by; name } ->
      make (code_of_mutation by) (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` cannot be mutated here: only a `var`, a `mut` parameter, or `mut self`, and \
               their parts, can be %s."
              name (show_mutation by)))
  | Lent_read_only_assigned { at = origin } ->
      make Not_assignable (Build.at origin)
        ~fixes:[ insert_mut_fix origin ]
        (say
           "This part is lent read-only, so it cannot be mutated. Pass the place it is lent from \
            `mut`, so that it is lent `mut`.")
  | Mode_on_assignment_target { at = origin; inner; keyword } ->
      make Redundant_mode (Build.at origin)
        ~fixes:[ remove_keyword_fix origin inner ]
        [
          Text "An assignment writes its target, so `";
          Build.quote inner;
          Text (Printf.sprintf "` takes no `%s`." (show_mode_keyword keyword));
        ]
  | Not_assignable_place { at = origin } ->
      make Not_assignable (Build.at origin)
        (say "Only a place, such as a variable, a field, or an element, can be assigned.")
  | Mode_on_read_argument { at = origin; inner; parameter } ->
      make Redundant_mode (Build.at origin)
        ~fixes:[ remove_keyword_fix origin inner ]
        (say
           (Printf.sprintf "`%s` only reads its argument, so it takes no mode keyword." parameter))
  | Missing_mut_argument { at = origin; parameter } ->
      make Missing_mode (Build.at origin)
        ~fixes:[ insert_mut_fix origin ]
        (say
           (Printf.sprintf "`%s` may mutate its argument, so the call site passes it `mut`."
              parameter))
  | Lent_read_only_argument { at = origin; parameter } ->
      make Wrong_mode (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` may mutate its argument, and this part is lent read-only. Pass the place it is \
               lent from `mut`, so that it is lent `mut`."
              parameter))
  | Temporary_passed_mut { at = origin; parameter } ->
      make Wrong_mode (Build.at origin)
        (say
           (Printf.sprintf "`%s` mutates its argument in place, so it must be a place passed `mut`."
              parameter))
  | Redundant_own { at = origin; inner; type_ } ->
      make Redundant_mode (Build.at origin)
        ~fixes:[ remove_keyword_fix origin inner ]
        (say (Printf.sprintf "`%s` copies implicitly, so it needs no `own`." (Types.show type_)))
  | Mut_for_own { at = origin; parameter } ->
      make Wrong_mode (Build.at origin)
        (say
           (Printf.sprintf "`%s` takes ownership of its argument, so it is passed `own`, not `mut`."
              parameter))
  | Type_parameter_as_value { at = origin; name } ->
      make Not_a_value (Build.at origin) (say (Printf.sprintf "`%s` is a type, not a value." name))
  | Theorem_as_value { at = origin; name } ->
      make Not_a_value (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` is a theorem, so it is not a value. Call it in a proof to use its `ensures`."
              name))
  | Type_as_value { at = origin; name } ->
      make Not_a_value (Build.at origin)
        (say (Printf.sprintf "`%s` is a type. Build a value with `%s(...)`." name name))
  | Trait_as_value { at = origin; name } ->
      make Not_a_value (Build.at origin) (say (Printf.sprintf "`%s` is not a value." name))
  | Specification_function_as_value { at = origin; name } ->
      make Not_a_value (Build.at origin)
        (say (Printf.sprintf "`%s` is applied to its subject, as in `%s(...)`." name name))
  | Variant_with_fields_as_function { at = origin; variant; fields } ->
      make Not_a_value (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` has %d fields, so it is not a function: a function takes its arguments by \
               position, and fields have no order. Build it with named fields, as in `%s(%s)`."
              variant (List.length fields) variant
              (String.concat ", " (List.map (fun field -> field ^ ": ...") fields))))
  | No_variants { at = origin; type_ } ->
      make Unknown_variant (Build.at origin)
        (say (Printf.sprintf "`%s` has no variants." (Types.show type_)))
  | Unknown_field { at = origin; base; name; candidates } ->
      make Unknown_member (Build.at origin)
        ~fixes:(Build.list_spelling_fixes origin ~written:name candidates)
        (say (Printf.sprintf "%s has no field `%s`." (show_shown_capitalized base) name))
  | Opaque_field_read { at = origin; type_ } ->
      make Private_field (Build.at origin)
        (say
           (Printf.sprintf "`%s` is opaque, so its fields can be read only in its own package."
              (Types.show type_)))
  | Method_as_field { at = origin; name } ->
      make Not_a_value (Build.at origin)
        (say (Printf.sprintf "`%s` is a method, so it is called: `%s()`." name name))
  | Lending_function_value { at = origin } ->
      make Not_a_value (Build.at origin)
        [
          Text "`";
          Build.quote origin;
          Text
            "` lends a part, and a function value cannot lend. Call it where the part is used, or \
             write a lambda that returns a copy of the part.";
        ]
  | No_member { at = origin; type_; name; view } ->
      make Unknown_member (Build.at origin)
        (say
           (match view with
           | Some view ->
               Printf.sprintf
                 "`%s` has no member `%s` of its own. The method is its view's: `%s.%s`."
                 (Types.show type_) name view name
           | None -> Printf.sprintf "`%s` has no member `%s`." (Types.show type_) name))
  | Type_argument_count { at = origin; expected; given } ->
      make Arity (Build.at origin)
        (say
           (Printf.sprintf "This takes %s, and %s given."
              (show_count expected "type argument" "type arguments")
              (show_count given "is" "are")))
  | Type_for_value_argument { at = origin } ->
      make Argument_kind (Build.at origin)
        (say "A type argument is given where a `UInt64` value is expected.")
  | Value_for_type_argument { at = origin } ->
      make Argument_kind (Build.at origin)
        (say "A `UInt64` value is given where a type argument is expected.")
  | Specification_call_in_code { at = origin; name; call } ->
      make Specification_only (Build.at origin)
        (say
           (match call with
           | Theorem_call ->
               Printf.sprintf
                 "`%s` is a theorem, so it is called only in specifications and proofs, which are \
                  not compiled."
                 name
           | Mentions specification_type ->
               Printf.sprintf
                 "`%s` mentions `%s`, which exists only in specifications, so it is called only in \
                  specifications."
                 name (Types.show specification_type)
           | Specification_function_call ->
               Printf.sprintf
                 "`%s` is for specifications only, so it is called only in specifications." name))
  | Not_an_integer_operand { at = origin; operator; excluded } ->
      make No_impl (Build.at origin)
        (say
           (Printf.sprintf
              (match operator with
              | Bitwise -> "Bitwise operators work on built-in integers, not %s."
              | Shift -> "Shifts work on built-in integers, not %s."
              | Complement -> "`~` works on built-in integers, not %s.")
              (show_shown excluded)))
  | Shift_amount_not_unsigned { at = origin; excluded } ->
      make Mismatch (Build.at origin)
        (say
           (Printf.sprintf "A shift amount is an unsigned integer, not %s." (show_shown excluded)))
  | Try_error_mismatch { at = origin; output_error; error } ->
      make Wrong_try (Build.at origin)
        (say
           (Printf.sprintf
              "`?` returns the error unchanged, so it needs the function's error type `%s`, not \
               `%s`. Convert it first with `map_error`."
              (Types.show output_error) (Types.show error)))
  | Try_misused { at = origin } ->
      make Wrong_try (Build.at origin)
        (say
           "`?` works on a `Result` in a function that returns a `Result`, and on an `Option` in a \
            function that returns an `Option`. Convert between them with `ok_or` or `ok`.")
  | Implies_in_code { at = origin } ->
      make Specification_only (Build.at origin)
        (say
           "`==>` is only for specifications and the bodies of functions for specifications only; \
            in code, write `!a || b`.")
  | String_addition { at = origin; join } ->
      let write_piece = function
        | Fragment fragment -> [ Build.quote fragment ]
        | Interpolated side -> [ Text "${"; Build.quote side; Text "}" ]
      in
      make String_addition (Build.at origin)
        ~fixes:
          (match join with
          | Some (left, right) ->
              [
                fix "Join them with interpolation."
                  [
                    Build.replace origin
                      ((Description.Text "\"" :: write_piece left)
                      @ write_piece right @ [ Text "\"" ]);
                  ];
              ]
          | None -> [])
        (say "Strings have no `+`. Join them with interpolation, or with methods such as `push`.")
  | Alternative_type_mismatch { at = origin; name; first; here } ->
      make Mismatch (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` is a `%s` in the first alternative, and a `%s` here; every alternative binds \
               it with one type."
              name (Types.show first) (Types.show here)))
  | Range_pattern_type { at = origin; excluded } ->
      make Mismatch (Build.at origin)
        (say
           (Printf.sprintf "A range pattern matches an integer or a `Character`, not %s."
              (show_shown excluded)))
  | Variant_pattern_without_fields { at = origin; variant } ->
      make Missing_argument (Build.at origin)
        ~fixes:[ fix "Match its fields with `..`." [ Build.insert_after origin [ Text "(..)" ] ] ]
        (say
           (Printf.sprintf "`%s` has fields, so its pattern names them, or writes `(..)`." variant))
  | Parenthesized_tuple_pattern { at = origin; patterns; type_ } ->
      let first, last =
        match (patterns.covering, List.rev patterns.covering) with
        | first :: _, last :: _ -> (first, last)
        | _ -> raise_bug "a parenthesized tuple pattern has no patterns"
      in
      make Missing_label (Build.at origin)
        ~fixes:
          [
            fix "Remove the parentheses."
              [ Build.delete (Start origin) (Start first); Build.delete (Stop last) (Stop origin) ];
          ]
        [
          Text
            (Printf.sprintf
               "`%s` is a tuple type, so a list of patterns without parentheses matches its fields \
                by position, as in `"
               (Types.show type_));
          Build.quote_over patterns;
          Text "`. In parentheses, fields match by name.";
        ]
  | Not_a_record_pattern { at = origin; type_ } ->
      make Not_a_record (Build.at origin)
        (say (Printf.sprintf "%s is not a record." (show_shown_capitalized type_)))
  | Not_a_tuple_type_pattern { at = origin; type_ } ->
      make Not_a_tuple_type (Build.at origin)
        (say
           (Printf.sprintf "%s is not a tuple type, so a list of patterns cannot match it."
              (show_shown_capitalized type_)))
  | Tuple_pattern_arity { at = origin; type_; fields; given } ->
      make Arity (Build.at origin)
        (say
           (Printf.sprintf
              "`%s` has %d fields, %s, so its tuple pattern has %d patterns, not %d. `_` skips a \
               field."
              (Types.show type_) (List.length fields) (show_names fields) (List.length fields) given))
  | Tuple_pattern_for_record { at = origin; type_; fields; form } -> (
      match form with
      | Some form ->
          make Not_a_tuple_type (Build.at origin)
            ~fixes:
              [
                fix "Match its fields by name, in parentheses."
                  [ Build.replace origin (write_labeled_form form) ];
              ]
            (Description.Text
               (Printf.sprintf
                  "`%s` is not a tuple type, so its fields match by name, in parentheses, as in `"
                  (Types.show type_))
             :: write_labeled_form form
            @ [ Text "`." ])
      | None ->
          make Not_a_tuple_type (Build.at origin)
            (say
               (Printf.sprintf
                  "`%s` is not a tuple type, so its fields, %s, match by name, in parentheses."
                  (Types.show type_) (show_names fields))))
  | Opaque_pattern { at = origin; type_ } ->
      make Private_field (Build.at origin)
        (say
           (Printf.sprintf "`%s` is opaque, so only its own package can match on it."
              (Types.show type_)))
  | Tuple_pattern_out_of_order { at = origin; type_; name; bound_field; reorder } ->
      make Out_of_order (Build.at origin)
        ~fixes:
          (Option.to_list
             (Option.map
                (fun fields ->
                  fix "Put the patterns in the order of the fields."
                    [ Build.replace origin [ Text (String.concat ", " fields) ] ])
                reorder))
        (say
           (Printf.sprintf
              "The patterns name the fields of `%s` out of order. A tuple pattern matches each \
               field by its position, so `%s` here would bind the field `%s`."
              (Types.show type_) name bound_field))
  | Unmatched_fields { at = origin; missing } ->
      make Missing_argument (Build.at origin)
        (say
           (Printf.sprintf "This pattern does not match %s. Name %s, or write `..` for the rest."
              (show_names missing)
              (match missing with [ _ ] -> "it" | _ -> "them")))
  | Not_structural { at = origin; type_; constant } ->
      make Not_structural (Build.at origin)
        (say
           (Printf.sprintf
              "A constant in a pattern needs a type with structural equality, whose `==` compares \
               contents, because the checks that a `match` covers every case and that every arm is \
               reachable compare constants by their contents. `%s` does not have it: its equality \
               is hand-written, or it holds a float, whose `==` treats `-0.0` and `0.0` as equal. \
               Match with a guard instead, as in `value if value == %s`."
              (Types.show type_) constant))
  | Not_a_constant { at = origin } ->
      make Unknown_member (Build.at origin) (say "This names no constant.")
  | Literal_does_not_fit { at = origin; number; excluded; low; high } ->
      make Literal_out_of_range (Build.at origin)
        (say
           (Printf.sprintf "`%s` does not fit in %s, which holds %s to %s." (Z.to_string number)
              (show_shown excluded) (Z.to_string low) (Z.to_string high)))
  | Negated_unsigned { at = origin; excluded; is_unsigned } ->
      make Negated_unsigned (Build.at origin)
        (say
           (Printf.sprintf "%s %s unsigned, so it cannot be negated."
              (show_shown_capitalized excluded)
              (if is_unsigned then "is" else "may be")))
  | Literal_fits_no_integer { at = origin; number } ->
      make Literal_out_of_range (Build.at origin)
        (say (Printf.sprintf "`%s` does not fit in any integer type." (Z.to_string number)))
  | Character_literal { at = origin; tag } ->
      make Character_scalar_count (Build.at origin)
        (say
           (match tag with
           | Character ->
               "`Character\"...\"` holds exactly one Unicode scalar value, with no `${...}`."
           | _ -> "`UInt8\"...\"` holds exactly one ASCII character, with no `${...}`."))
  | Integer_pattern_type { at = origin; excluded } ->
      make Mismatch (Build.at origin)
        (say
           (Printf.sprintf "An integer pattern matches an integer, not %s." (show_shown excluded)))
  | String_pattern_type { at = origin; type_ } ->
      make Mismatch (Build.at origin)
        (say (Printf.sprintf "A string pattern matches a string, not `%s`." (Types.show type_)))
  | Capability_mismatch { at = origin; left; right } ->
      make Mismatch (Build.at origin)
        (say
           (Printf.sprintf
              "Two function types here must use the same capabilities, and one uses `%s` where the \
               other uses `%s`."
              (Types.show_capabilities left) (Types.show_capabilities right)))
  | Undetermined { at = origin; undetermined } ->
      make Cannot_infer (Build.at origin) (describe_undetermined origin undetermined)
  | Types_undetermined { at = origin } ->
      make Cannot_infer (Build.at origin)
        (say "The types here cannot be inferred from this code alone.")
  | Trait_arguments_undetermined { at = origin; trait } ->
      make Cannot_infer (Build.at origin)
        (say
           (Printf.sprintf
              "This call does not determine the arguments of `%s`. Write the call in full with \
               them."
              (show_trait_name trait)))
  | Lambda_needs_type { at = origin; remedy } ->
      make Lambda_needs_type (Build.at origin)
        (say
           ("A lambda's parameter types come from where it is used, and nothing here gives them. "
           ^
           match remedy with
           | Bracket_arguments { declared_on; is_type } -> write_bracket_remedy declared_on ~is_type
           | Typed_let ->
               "Bind it with a typed `let`, such as `let double: fn(Int64) -> Int64 = fn(x) { x * \
                2 }`."))
  | Range_not_integer { at = origin; owner; element } ->
      make Not_iterable (Build.at origin)
        (say
           (Printf.sprintf "%s range is of integers, not `%s`."
              (match owner with
              | Range_of_loop -> "A `for` loop's"
              | Range_of_quantifier -> "A quantifier's")
              (Types.show element)))
  | Unused_value { at = origin; type_ } ->
      make Unused_value (Build.at origin)
        ~fixes:[ fix "Discard it on purpose." [ Build.insert_before origin [ Text "let _ = " ] ] ]
        (say
           (Printf.sprintf
              "This value of type `%s` is not used. Use it, or discard it with `let _ =`."
              (Types.show type_)))
  | Let_else_falls_through { at = origin } ->
      make Mismatch (Build.at origin)
        (say
           "The `else` of a `let` must leave the block, with `return`, `break`, `continue`, or \
            `unreachable`.")
  | Not_iterable_loop { at = origin; mode; type_ } ->
      make Not_iterable (Build.at origin)
        (say
           (match mode with
           | Read ->
               Printf.sprintf
                 "A `for` loop cannot go over %s: it implements neither `Iterable` nor `Cursor`."
                 (show_shown type_)
           | Mut ->
               Printf.sprintf
                 "A `for` loop cannot mutate the elements of %s: it implements neither \
                  `IterableMut` nor `Cursor`."
                 (show_shown type_)
           | Own ->
               Printf.sprintf
                 "A `for` loop cannot consume %s: it implements neither `IntoCursor` nor `Cursor`."
                 (show_shown type_)))
  | Cursor_not_cursor { at = origin; type_; cursor } ->
      make Not_iterable (Build.at origin)
        (say
           (Printf.sprintf
              "The `IntoCursor` impl of `%s` gives `%s` as its `Cursor`, which does not implement \
               `Cursor`."
              (Types.show type_) (Types.show cursor)))
  | Not_displayable { at = origin; type_ } ->
      make No_impl (Build.at origin)
        (say
           (Printf.sprintf "`%s` does not implement `Display`, so it cannot be interpolated."
              (Types.show type_)))
  | Template_part_conversion { at = origin; part_type; part; tag_type } ->
      make No_impl (Build.at origin)
        (say
           (Printf.sprintf "`%s` cannot become a `%s`, the part type of `%s`."
              (Types.show part_type) (Types.show part) (Types.show tag_type)))
  | Not_a_tag { at = origin; tag_type } ->
      make No_impl (Build.at origin)
        (say
           (Printf.sprintf "`%s` does not implement `FromTemplate`, so it is not a tag."
              (Types.show tag_type)))
  | Tag_not_a_type { at = origin } ->
      make Not_a_type (Build.at origin) (say "A string's tag is a type.")
  | Array_length { at = origin; given; count } ->
      make Mismatch (Build.at origin)
        (say
           (Printf.sprintf "This array has %d elements, and its type says %s." given
              (Z.to_string count)))
  | Lambda_arity { at = origin; given; function_type; expected } ->
      make Mismatch (Build.at origin)
        (say
           (Printf.sprintf "This lambda takes %d parameters, and `%s` takes %d." given
              (Types.show function_type) expected))
  | Arm_pattern_count { at = origin; given; expected } ->
      make Mismatch (Build.at origin)
        (say
           (Printf.sprintf "This arm has %d patterns, and the `match` has %d values." given expected))
  | Not_iterable_quantifier { at = origin; type_ } ->
      make Not_iterable (Build.at origin)
        (say
           (Printf.sprintf "A quantifier cannot go over %s: it does not implement `Iterable`."
              (show_shown type_)))
  | Specification_only_type { at = origin; subject; type_; specification_type } ->
      let subject =
        match subject with
        | Binding_subject binding -> [ Description.Text "`"; Build.quote binding; Text "`" ]
        | Value_subject -> [ Text "This value" ]
      in
      make Specification_only (Build.at origin)
        (subject
        @ say
            (if Types.equal type_ specification_type then
               Printf.sprintf
                 " has the type `%s`, which exists only in specifications and has no \
                  representation in code that runs."
                 (Types.show type_)
             else
               Printf.sprintf
                 " has the type `%s`, which holds `%s`. `%s` exists only in specifications and has \
                  no representation in code that runs."
                 (Types.show type_) (Types.show specification_type) (Types.show specification_type))
        )

let examples : t list =
  [
    Mismatch
      {
        at = Build.example "at";
        mismatch =
          Expected
            {
              expected = Some_integer;
              actual = Some_integer;
              copy =
                Some { copy_method = "‹copy_method›"; edit = Rename_copy (Build.example "edit") };
            };
        decision =
          Some
            {
              name = Build.example "name";
              decided = Build.example_type;
              site = Use;
              decided_at = Build.example "decided_at";
              declares = false;
            };
      };
    Mismatch
      {
        at = Build.example "at";
        mismatch = Loop_element { element = Some_integer; annotated = Some_integer };
        decision =
          Some
            {
              name = Build.example "name";
              decided = Build.example_type;
              site = Use;
              decided_at = Build.example "decided_at";
              declares = false;
            };
      };
    Mismatch
      {
        at = Build.example "at";
        mismatch =
          Mismatched_integers
            {
              left = Build.example_type;
              right = Build.example_type;
              widening =
                Some { side = Left; operand = Build.example "operand"; target = Build.example_type };
            };
        decision =
          Some
            {
              name = Build.example "name";
              decided = Build.example_type;
              site = Use;
              decided_at = Build.example "decided_at";
              declares = false;
            };
      };
    Mismatch
      {
        at = Build.example "at";
        mismatch =
          Unsatisfied_bound
            {
              of_type = Some Build.example_type;
              subject = Build.example_type;
              bound = Build.example_trait;
              unmet = Does_not_hold;
              impl_need = Some { needing = Build.example_type; condition = Build.example_trait };
            };
        decision =
          Some
            {
              name = Build.example "name";
              decided = Build.example_type;
              site = Use;
              decided_at = Build.example "decided_at";
              declares = false;
            };
      };
    Mismatch
      {
        at = Build.example "at";
        mismatch =
          Expected
            {
              expected = Some_integer;
              actual = Some_integer;
              copy =
                Some { copy_method = "‹copy_method›"; edit = Rename_copy (Build.example "edit") };
            };
        decision = None;
      };
    Integer_for_float
      {
        at = Build.example "at";
        wanted = Some_integer;
        literals = [ (Build.example "literals", Z.of_int 300) ];
      };
    Integer_for_float
      {
        at = Build.example "at";
        wanted = Some_float;
        literals = [ (Build.example "literals", Z.of_int 300) ];
      };
    Integer_for_float
      {
        at = Build.example "at";
        wanted = Exactly Build.example_type;
        literals = [ (Build.example "literals", Z.of_int 300) ];
      };
    Decided_in_specification { at = Build.example "at"; local = Some (Build.example "local") };
    Decided_in_specification { at = Build.example "at"; local = None };
    Operator_output
      {
        at = Build.example "at";
        found = Build.example_type;
        wanted = Build.example_type;
        impl_need = Some { needing = Build.example_type; condition = Build.example_trait };
      };
    Operator_output
      {
        at = Build.example "at";
        found = Build.example_type;
        wanted = Build.example_type;
        impl_need = None;
      };
    Operator_not_implemented
      {
        at = Build.example "at";
        subject = Build.example_type;
        trait = Build.example_trait;
        impl_need = Some { needing = Build.example_type; condition = Build.example_trait };
      };
    Operator_not_implemented
      {
        at = Build.example "at";
        subject = Build.example_type;
        trait = Build.example_trait;
        impl_need = None;
      };
    Not_implemented
      {
        at = Build.example "at";
        subject = Build.example_type;
        trait = Build.example_trait;
        is_iteration = false;
        impl_need = Some { needing = Build.example_type; condition = Build.example_trait };
      };
    Not_implemented
      {
        at = Build.example "at";
        subject = Build.example_type;
        trait = Build.example_trait;
        is_iteration = true;
        impl_need = Some { needing = Build.example_type; condition = Build.example_trait };
      };
    Not_implemented
      {
        at = Build.example "at";
        subject = Build.example_type;
        trait = Build.example_trait;
        is_iteration = false;
        impl_need = None;
      };
    Body_ends_without_value { body = Build.example "body"; output = Build.example_type };
    Last_statement_without_value
      { statement = Build.example "statement"; output = Build.example_type };
    Not_bit_vector { at = Build.example "at"; type_ = Build.example_type };
    Unchecked_invariant { at = Build.example "at" };
    Argument_count
      {
        at = Build.example "at";
        callee = Fields_of (Variant_name "‹callee›");
        expected = 2;
        given = 3;
      };
    Argument_count
      { at = Build.example "at"; callee = Method_besides_self; expected = 2; given = 3 };
    Argument_count { at = Build.example "at"; callee = Plain_function; expected = 2; given = 3 };
    Label_in_indirect_call { label = Build.example "label"; value = Build.example "value" };
    Not_callable { at = Build.example "at"; callee = Some_integer };
    Not_callable { at = Build.example "at"; callee = Some_float };
    Not_callable { at = Build.example "at"; callee = Exactly Build.example_type };
    Missing_parameter { at = Build.example "at"; parameter = "‹parameter›" };
    Unknown_variant
      {
        at = Build.example "at";
        type_ = Build.example_type;
        variant = "‹variant›";
        candidates = [ "‹candidates›" ];
      };
    Variant_without_fields { at = Build.example "at"; variant = "‹variant›" };
    Not_a_record_construction { at = Build.example "at"; type_ = Build.example_type };
    Opaque_construction { at = Build.example "at"; type_ = Build.example_type };
    Mut_base_of_with { at = Build.example "at" };
    Unknown_label
      {
        label = Build.example "label";
        written = "‹written›";
        owner = Some (Variant_name "‹owner›");
        candidates = [ "‹candidates›" ];
      };
    Unknown_label
      {
        label = Build.example "label";
        written = "‹written›";
        owner = None;
        candidates = [ "‹candidates›" ];
      };
    Positional_after_labeled { argument = Build.example "argument"; label = Some "‹label›" };
    Positional_after_labeled { argument = Build.example "argument"; label = None };
    Tuple_argument_out_of_order
      {
        argument = Build.example "argument";
        owner = Variant_name "‹owner›";
        filled = "‹filled›";
        field = "‹field›";
      };
    Tuple_argument_out_of_order
      {
        argument = Build.example "argument";
        owner = Type_named Build.example_type;
        filled = "‹filled›";
        field = "‹field›";
      };
    Bare_value
      {
        argument = Build.example "argument";
        owner = Pattern_owner { owner = Variant_name "‹owner›"; is_tuple_type = false };
        fields = [ "‹fields›" ];
        label = Some "‹label›";
      };
    Bare_value
      {
        argument = Build.example "argument";
        owner = Construction_owner (Variant_name "‹owner›");
        fields = [ "‹fields›" ];
        label = Some "‹label›";
      };
    Bare_value
      {
        argument = Build.example "argument";
        owner = Pattern_owner { owner = Variant_name "‹owner›"; is_tuple_type = false };
        fields = [ "‹fields›" ];
        label = None;
      };
    Repeated_argument { at = Build.example "at"; name = "‹name›"; is_pattern = false };
    Repeated_argument { at = Build.example "at"; name = "‹name›"; is_pattern = true };
    Not_an_integer { at = Build.example "at"; subject = Potential; excluded = Some_integer };
    Not_an_integer { at = Build.example "at"; subject = Decreases_measure; excluded = Some_integer };
    Not_an_integer { at = Build.example "at"; subject = Cost_bound; excluded = Some_integer };
    Not_an_integer { at = Build.example "at"; subject = Log_argument; excluded = Some_integer };
    Not_an_integer { at = Build.example "at"; subject = Power_argument; excluded = Some_integer };
    Not_an_integer { at = Build.example "at"; subject = Potential; excluded = Some_float };
    Not_an_integer
      { at = Build.example "at"; subject = Potential; excluded = Exactly Build.example_type };
    No_method
      {
        at = Build.example "at";
        owner = Type_owner { type_ = Build.example_type; view = Some Build.example_type };
        name = "‹name›";
        candidates = [ "‹candidates›" ];
      };
    No_method
      {
        at = Build.example "at";
        owner = Named_owner "‹owner›";
        name = "‹name›";
        candidates = [ "‹candidates›" ];
      };
    No_method
      {
        at = Build.example "at";
        owner = Path_owner Build.example_path;
        name = "‹name›";
        candidates = [ "‹candidates›" ];
      };
    Counted_not_a_capability { at = Build.example "at"; written = "‹written›" };
    Counted_not_a_function { at = Build.example "at"; name = "‹name›"; type_ = Build.example_type };
    Counted_neither { at = Build.example "at"; name = "‹name›" };
    Cost_of_other_metric
      {
        at = Build.example "at";
        operand = { cost_function = Language.Metric.Time; callee = Function_parameter "‹callee›" };
        cost_function_name = Build.example "cost_function_name";
        bounded = Language.Metric.Time;
      };
    Cost_of_calls
      {
        at = Build.example "at";
        operand = { cost_function = Language.Metric.Time; callee = Function_parameter "‹callee›" };
      };
    Upper_bound_in_exact_bound
      {
        at = Build.example "at";
        operand = { cost_function = Language.Metric.Time; callee = Function_parameter "‹callee›" };
      };
    Unbounded_time
      {
        clause = Build.example "clause";
        condition = Build.example_condition;
        has_condition = false;
      };
    Unbounded_time
      { clause = Build.example "clause"; condition = Build.example_condition; has_condition = true };
    Clause_never_holds { at = Build.example "at" };
    Constant_out_of_range
      {
        at = Build.example "at";
        constant = Z.of_int 300;
        type_ = Build.example_type;
        low = Z.of_int 300;
        high = Z.of_int 300;
      };
    Division_by_zero { at = Build.example "at" };
    Default_not_constant { at = Build.example "at" };
    Not_constant { at = Build.example "at" };
    Condition_not_constant { at = Build.example "at" };
    Condition_names_parameter { at = Build.example "at" };
    Constant_not_data { at = Build.example "at"; part = Function_type };
    Constant_not_data { at = Build.example "at"; part = Handle };
    Constant_not_data { at = Build.example "at"; part = Shared_state };
    Hidden_in_public_clause
      { at = Build.example "at"; name = "‹name›"; hidden = Build.example_path };
    Float_too_large { at = Build.example "at"; target = Some_integer };
    Float_too_large { at = Build.example "at"; target = Some_float };
    Float_too_large { at = Build.example "at"; target = Exactly Build.example_type };
    Runs_in_formula { at = Build.example "at"; construct = Unreachable_expression };
    Runs_in_formula { at = Build.example "at"; construct = Break_expression };
    Runs_in_formula { at = Build.example "at"; construct = Continue_expression };
    Runs_in_formula { at = Build.example "at"; construct = Return_expression };
    Runs_in_formula { at = Build.example "at"; construct = Try_expression };
    Runs_in_formula { at = Build.example "at"; construct = Var_binding };
    Runs_in_formula { at = Build.example "at"; construct = For_statement };
    Runs_in_formula { at = Build.example "at"; construct = While_statement };
    Runs_in_formula { at = Build.example "at"; construct = Concurrent_block };
    Runs_in_formula { at = Build.example "at"; construct = Parallel_block };
    Self_outside_method { at = Build.example "at" };
    Self_type_as_value { at = Build.example "at" };
    Quantifier_over_type_in_code { at = Build.example "at" };
    Static_method_as_value { at = Build.example "at"; name = "‹name›" };
    Method_with_type_arguments_as_value { at = Build.example "at" };
    String_indexed { at = Build.example "at" };
    Not_sliceable { at = Build.example "at"; base = Some_integer };
    Not_sliceable { at = Build.example "at"; base = Some_float };
    Not_sliceable { at = Build.example "at"; base = Exactly Build.example_type };
    Not_indexable { at = Build.example "at"; base = Some_integer };
    Not_indexable { at = Build.example "at"; base = Some_float };
    Not_indexable { at = Build.example "at"; base = Exactly Build.example_type };
    Several_indexes { at = Build.example "at" };
    Parameter_with_arguments { at = Build.example "at"; name = "‹name›" };
    Type_arity { at = Build.example "at"; type_path = Build.example_path; expected = 2; given = 3 };
    Associated_in_type_arguments { at = Build.example "at" };
    Not_a_type_argument { at = Build.example "at" };
    Hidden_member
      {
        at = Build.example "at";
        hidden = Build.example_path;
        visibility = Language.Visibility.Private;
      };
    No_receiver_overload { at = Build.example "at"; name = "‹name›" };
    Old_arity { at = Build.example "at"; given = 3 };
    Final_misused { at = Build.example "at" };
    Identical_arity { at = Build.example "at"; given = 3 };
    Not_a_function_or_type { at = Build.example "at"; name = "‹name›" };
    Callback_ensures_in_code { at = Build.example "at"; name = "‹name›" };
    Callback_ensures_label { at = Build.example "at"; name = "‹name›" };
    Callback_ensures_arity
      {
        at = Build.example "at";
        name = "‹name›";
        inputs = [ Language.Mode.Read ];
        has_result = false;
        given = 3;
      };
    Callback_ensures_arity
      {
        at = Build.example "at";
        name = "‹name›";
        inputs = [ Language.Mode.Read ];
        has_result = true;
        given = 3;
      };
    Ensures_of_non_parameter { at = Build.example "at"; name = "‹name›" };
    Ensures_without_function { at = Build.example "at"; base = Some_integer };
    Ensures_without_function { at = Build.example "at"; base = Some_float };
    Ensures_without_function { at = Build.example "at"; base = Exactly Build.example_type };
    Cost_operand_not_callee
      { at = Build.example "at"; metric = Language.Metric.Time; operand = Operand_is_neither };
    Cost_operand_not_callee
      {
        at = Build.example "at";
        metric = Language.Metric.Time;
        operand = Local_of_type { name = "‹name›"; type_ = Build.example_type };
      };
    Cost_operand_not_callee
      {
        at = Build.example "at";
        metric = Language.Metric.Time;
        operand = Name_is_neither "‹operand›";
      };
    No_bound_method { at = Build.example "at"; type_ = Build.example_type; name = "‹name›" };
    Ambiguous_cost_method
      {
        at = Build.example "at";
        type_ = Build.example_type;
        name = "‹name›";
        metric = Language.Metric.Time;
      };
    New_on_literal_type
      {
        at = Build.example "at";
        type_ = Build.example_type;
        literal = Empty_list;
        call = Some (Build.example "call");
      };
    New_on_literal_type
      {
        at = Build.example "at";
        type_ = Build.example_type;
        literal = Empty_map;
        call = Some (Build.example "call");
      };
    New_on_literal_type
      { at = Build.example "at"; type_ = Build.example_type; literal = Empty_list; call = None };
    Ambiguous_static_method
      {
        at = Build.example "at";
        type_ = Build.example_type;
        name = "‹name›";
        traits = [ Build.example_trait ];
      };
    Trait_arity { at = Build.example "at"; trait = Build.example_trait; expected = 2; given = 3 };
    Receiver_missing_in_full_call { at = Build.example "at" };
    Wrong_receiver_overload
      {
        at = Build.example "at";
        name = "‹name›";
        wanted = Path.Instance Read;
        overloads = [ Path.Instance Read ];
      };
    Missing_receiver_mode { receiver = Build.example "receiver"; name = "‹name›" };
    Ambiguous_method_call
      {
        at = Build.example "at";
        call = Build.example "call";
        type_ = Build.example_type;
        name = "‹name›";
        receiver = Build.example "receiver";
        arguments = [ { Description.covering = [ Build.example "arguments" ] } ];
        traits = [ Build.example_trait ];
      };
    Index_not_mutable
      { at = Build.example "at"; by = Assignment; self_type = Build.example_type; assigns = false };
    Index_not_mutable
      { at = Build.example "at"; by = Passed_mut; self_type = Build.example_type; assigns = false };
    Index_not_mutable
      { at = Build.example "at"; by = Assignment; self_type = Build.example_type; assigns = true };
    Stored_slice_written { at = Build.example "at"; by = Assignment; stored = Held_by "‹stored›" };
    Stored_slice_written { at = Build.example "at"; by = Passed_mut; stored = Held_by "‹stored›" };
    Stored_slice_written { at = Build.example "at"; by = Assignment; stored = In_field };
    Stored_slice_written { at = Build.example "at"; by = Assignment; stored = In_element };
    Stored_slice_written { at = Build.example "at"; by = Assignment; stored = Lent_by_a_call };
    Slice_parameter_assigned { at = Build.example "at"; parameter = "‹parameter›" };
    Slice_passed_to_generic { at = Build.example "at" };
    Mutation_in_formula { at = Build.example "at"; by = Assignment };
    Mutation_in_formula { at = Build.example "at"; by = Passed_mut };
    Captured_mutation { at = Build.example "at"; by = Assignment; name = "‹name›" };
    Captured_mutation { at = Build.example "at"; by = Passed_mut; name = "‹name›" };
    Read_only_mutation { at = Build.example "at"; by = Assignment; name = "‹name›" };
    Read_only_mutation { at = Build.example "at"; by = Passed_mut; name = "‹name›" };
    Lent_read_only_assigned { at = Build.example "at" };
    Mode_on_assignment_target
      { at = Build.example "at"; inner = Build.example "inner"; keyword = Language.Mode.Read };
    Not_assignable_place { at = Build.example "at" };
    Mode_on_read_argument
      { at = Build.example "at"; inner = Build.example "inner"; parameter = "‹parameter›" };
    Missing_mut_argument { at = Build.example "at"; parameter = "‹parameter›" };
    Lent_read_only_argument { at = Build.example "at"; parameter = "‹parameter›" };
    Temporary_passed_mut { at = Build.example "at"; parameter = "‹parameter›" };
    Redundant_own
      { at = Build.example "at"; inner = Build.example "inner"; type_ = Build.example_type };
    Mut_for_own { at = Build.example "at"; parameter = "‹parameter›" };
    Type_parameter_as_value { at = Build.example "at"; name = "‹name›" };
    Theorem_as_value { at = Build.example "at"; name = "‹name›" };
    Type_as_value { at = Build.example "at"; name = "‹name›" };
    Trait_as_value { at = Build.example "at"; name = "‹name›" };
    Specification_function_as_value { at = Build.example "at"; name = "‹name›" };
    Variant_with_fields_as_function
      { at = Build.example "at"; variant = "‹variant›"; fields = [ "‹fields›" ] };
    No_variants { at = Build.example "at"; type_ = Build.example_type };
    Unknown_field
      {
        at = Build.example "at";
        base = Some_integer;
        name = "‹name›";
        candidates = [ "‹candidates›" ];
      };
    Unknown_field
      {
        at = Build.example "at";
        base = Some_float;
        name = "‹name›";
        candidates = [ "‹candidates›" ];
      };
    Unknown_field
      {
        at = Build.example "at";
        base = Exactly Build.example_type;
        name = "‹name›";
        candidates = [ "‹candidates›" ];
      };
    Opaque_field_read { at = Build.example "at"; type_ = Build.example_type };
    Method_as_field { at = Build.example "at"; name = "‹name›" };
    Lending_function_value { at = Build.example "at" };
    No_member
      { at = Build.example "at"; type_ = Build.example_type; name = "‹name›"; view = Some "‹view›" };
    No_member { at = Build.example "at"; type_ = Build.example_type; name = "‹name›"; view = None };
    Type_argument_count { at = Build.example "at"; expected = 2; given = 3 };
    Type_for_value_argument { at = Build.example "at" };
    Value_for_type_argument { at = Build.example "at" };
    Specification_call_in_code { at = Build.example "at"; name = "‹name›"; call = Theorem_call };
    Specification_call_in_code
      { at = Build.example "at"; name = "‹name›"; call = Mentions Build.example_type };
    Specification_call_in_code
      { at = Build.example "at"; name = "‹name›"; call = Specification_function_call };
    Not_an_integer_operand { at = Build.example "at"; operator = Bitwise; excluded = Some_integer };
    Not_an_integer_operand { at = Build.example "at"; operator = Shift; excluded = Some_integer };
    Not_an_integer_operand
      { at = Build.example "at"; operator = Complement; excluded = Some_integer };
    Not_an_integer_operand { at = Build.example "at"; operator = Bitwise; excluded = Some_float };
    Not_an_integer_operand
      { at = Build.example "at"; operator = Bitwise; excluded = Exactly Build.example_type };
    Shift_amount_not_unsigned { at = Build.example "at"; excluded = Some_integer };
    Shift_amount_not_unsigned { at = Build.example "at"; excluded = Some_float };
    Shift_amount_not_unsigned { at = Build.example "at"; excluded = Exactly Build.example_type };
    Try_error_mismatch
      { at = Build.example "at"; output_error = Build.example_type; error = Build.example_type };
    Try_misused { at = Build.example "at" };
    Implies_in_code { at = Build.example "at" };
    String_addition
      {
        at = Build.example "at";
        join = Some (Fragment (Build.example "join"), Fragment (Build.example "join"));
      };
    String_addition { at = Build.example "at"; join = None };
    Alternative_type_mismatch
      {
        at = Build.example "at";
        name = "‹name›";
        first = Build.example_type;
        here = Build.example_type;
      };
    Range_pattern_type { at = Build.example "at"; excluded = Some_integer };
    Range_pattern_type { at = Build.example "at"; excluded = Some_float };
    Range_pattern_type { at = Build.example "at"; excluded = Exactly Build.example_type };
    Variant_pattern_without_fields { at = Build.example "at"; variant = "‹variant›" };
    Parenthesized_tuple_pattern
      {
        at = Build.example "at";
        patterns = { Description.covering = [ Build.example "patterns" ] };
        type_ = Build.example_type;
      };
    Not_a_record_pattern { at = Build.example "at"; type_ = Some_integer };
    Not_a_record_pattern { at = Build.example "at"; type_ = Some_float };
    Not_a_record_pattern { at = Build.example "at"; type_ = Exactly Build.example_type };
    Not_a_tuple_type_pattern { at = Build.example "at"; type_ = Some_integer };
    Not_a_tuple_type_pattern { at = Build.example "at"; type_ = Some_float };
    Not_a_tuple_type_pattern { at = Build.example "at"; type_ = Exactly Build.example_type };
    Tuple_pattern_arity
      { at = Build.example "at"; type_ = Build.example_type; fields = [ "‹fields›" ]; given = 3 };
    Tuple_pattern_for_record
      {
        at = Build.example "at";
        type_ = Build.example_type;
        fields = [ "‹fields›" ];
        form = Some [ (Some "‹form›", Build.example "form") ];
      };
    Tuple_pattern_for_record
      { at = Build.example "at"; type_ = Build.example_type; fields = [ "‹fields›" ]; form = None };
    Opaque_pattern { at = Build.example "at"; type_ = Build.example_type };
    Tuple_pattern_out_of_order
      {
        at = Build.example "at";
        type_ = Build.example_type;
        name = "‹name›";
        bound_field = "‹bound_field›";
        reorder = Some [ "‹reorder›" ];
      };
    Tuple_pattern_out_of_order
      {
        at = Build.example "at";
        type_ = Build.example_type;
        name = "‹name›";
        bound_field = "‹bound_field›";
        reorder = None;
      };
    Unmatched_fields { at = Build.example "at"; missing = [ "‹missing›" ] };
    Not_structural { at = Build.example "at"; type_ = Build.example_type; constant = "‹constant›" };
    Not_a_constant { at = Build.example "at" };
    Literal_does_not_fit
      {
        at = Build.example "at";
        number = Z.of_int 300;
        excluded = Some_integer;
        low = Z.of_int 300;
        high = Z.of_int 300;
      };
    Literal_does_not_fit
      {
        at = Build.example "at";
        number = Z.of_int 300;
        excluded = Some_float;
        low = Z.of_int 300;
        high = Z.of_int 300;
      };
    Literal_does_not_fit
      {
        at = Build.example "at";
        number = Z.of_int 300;
        excluded = Exactly Build.example_type;
        low = Z.of_int 300;
        high = Z.of_int 300;
      };
    Negated_unsigned { at = Build.example "at"; excluded = Some_integer; is_unsigned = false };
    Negated_unsigned { at = Build.example "at"; excluded = Some_float; is_unsigned = false };
    Negated_unsigned
      { at = Build.example "at"; excluded = Exactly Build.example_type; is_unsigned = false };
    Negated_unsigned { at = Build.example "at"; excluded = Some_integer; is_unsigned = true };
    Literal_fits_no_integer { at = Build.example "at"; number = Z.of_int 300 };
    Character_literal { at = Build.example "at"; tag = Language.Builtin_type.Int8 };
    Integer_pattern_type { at = Build.example "at"; excluded = Some_integer };
    Integer_pattern_type { at = Build.example "at"; excluded = Some_float };
    Integer_pattern_type { at = Build.example "at"; excluded = Exactly Build.example_type };
    String_pattern_type { at = Build.example "at"; type_ = Build.example_type };
    Capability_mismatch
      {
        at = Build.example "at";
        left = Types.make_capability_set [ Build.example_capability ];
        right = Types.make_capability_set [ Build.example_capability ];
      };
    Undetermined { at = Build.example "at"; undetermined = Binding_type };
    Undetermined
      {
        at = Build.example "at";
        undetermined =
          Generic_argument
            { parameter = "‹parameter›"; is_type = false; declared_on = Build.example_path };
      };
    Undetermined { at = Build.example "at"; undetermined = List_element };
    Undetermined { at = Build.example "at"; undetermined = Map_entries };
    Types_undetermined { at = Build.example "at" };
    Trait_arguments_undetermined { at = Build.example "at"; trait = Build.example_path };
    Lambda_needs_type
      {
        at = Build.example "at";
        remedy = Bracket_arguments { declared_on = Build.example_path; is_type = false };
      };
    Lambda_needs_type { at = Build.example "at"; remedy = Typed_let };
    Range_not_integer
      { at = Build.example "at"; owner = Range_of_loop; element = Build.example_type };
    Range_not_integer
      { at = Build.example "at"; owner = Range_of_quantifier; element = Build.example_type };
    Unused_value { at = Build.example "at"; type_ = Build.example_type };
    Let_else_falls_through { at = Build.example "at" };
    Not_iterable_loop { at = Build.example "at"; mode = Language.Mode.Read; type_ = Some_integer };
    Not_iterable_loop { at = Build.example "at"; mode = Language.Mode.Read; type_ = Some_float };
    Not_iterable_loop
      { at = Build.example "at"; mode = Language.Mode.Read; type_ = Exactly Build.example_type };
    Cursor_not_cursor
      { at = Build.example "at"; type_ = Build.example_type; cursor = Build.example_type };
    Not_displayable { at = Build.example "at"; type_ = Build.example_type };
    Template_part_conversion
      {
        at = Build.example "at";
        part_type = Build.example_type;
        part = Build.example_type;
        tag_type = Build.example_type;
      };
    Not_a_tag { at = Build.example "at"; tag_type = Build.example_type };
    Tag_not_a_type { at = Build.example "at" };
    Array_length { at = Build.example "at"; given = 3; count = Z.of_int 300 };
    Lambda_arity
      { at = Build.example "at"; given = 3; function_type = Build.example_type; expected = 2 };
    Arm_pattern_count { at = Build.example "at"; given = 3; expected = 2 };
    Not_iterable_quantifier { at = Build.example "at"; type_ = Some_integer };
    Not_iterable_quantifier { at = Build.example "at"; type_ = Some_float };
    Not_iterable_quantifier { at = Build.example "at"; type_ = Exactly Build.example_type };
    Specification_only_type
      {
        at = Build.example "at";
        subject = Binding_subject (Build.example "subject");
        type_ = Build.example_type;
        specification_type = Build.example_type;
      };
    Specification_only_type
      {
        at = Build.example "at";
        subject = Value_subject;
        type_ = Build.example_type;
        specification_type = Build.example_type;
      };
  ]

let list_examples code =
  List.filter (fun example -> (describe example).code = Diagnostic.Code.Types code) examples
