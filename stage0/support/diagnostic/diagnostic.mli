(** Errors with spans and exact fixes, shared by every stage of the compiler.

    Every diagnostic is an error: Truss has no warnings. Each has a stable code, so that tools and
    agents match on codes rather than on message text. *)

type span = Source.span = private { start : int; stop : int }

(** The codes, one constructor each and grouped by the stage that reports them, so that a misspelled
    code cannot compile and every stable code is listed in one place. {!Code.name} gives the name
    tools see, such as ["lexer.unterminated_string"]: the stage, then the code. *)
module Code : sig
  type lexer =
    | Invalid_utf8
    | Carriage_return
    | Forbidden_character
    | Comment
    | Semicolon
    | Unexpected_character
    | Strict_equality
    | Character_literal
    | String_prefix
    | String_delimiter
    | Attribute
    | Foreign_operator
    | Confusable_character
    | Lifetime
    | Number_hexadecimal_float
    | Name_case
    | Name_not_ascii
    | Number_suffix
    | Number_uppercase_prefix
    | Number_uppercase_exponent
    | Number_missing_digits
    | Number_invalid_digit
    | Number_followed_by_name
    | Number_underscore
    | Number_digit_separator
    | Number_leading_zero
    | Unterminated_string
    | Invalid_escape
    | Line_break_in_interpolation
    | Empty_interpolation
    | Interpolation_too_deep
    | Raw_string_quotes
    | Raw_string_closing_not_alone
    | Raw_string_indentation
    | Unclosed_bracket
    | Unmatched_closing_bracket

  type parser =
    | Unexpected_token
    | Needs_parentheses
    | Reserved_word
    | Use_after_definition
    | Statement_at_top_level
    | Missing_body
    | Open_range
    | Interpolation_not_allowed
    | Float_pattern
    | Let_else_brace
    | Nesting_too_deep
    | Misplaced_opaque
    | Misplaced_visibility
    | Misplaced_self
    | Lends_own
    | Repeated_clause
    | Cost_word
    | Finite_not_time
    | Loop_cost_bound
    | Function_type_names
    | Misplaced_requires
    | Misplaced_potential
    | Increment
    | Double_negation
    | Match_arm_comma
    | Conditional_operator
    | Let_mut
    | Address_of
    | Closure_bars
    | Brace_record
    | Turbofish
    | Trailing_lambda
    | As_conversion
    | Elif
    | Angle_brackets
    | Path_separator
    | Qualified_variant
    | Macro_call
    | Tuple
    | Power_operator
    | Short_declaration
    | Pipe_operator
    | Lambda_annotation
    | Impl_parameters
    | Null_coalescing
    | Specification_only
    | Misplaced_assert
    | Misplaced_proof
    | Misplaced_loop_exit
    | Exits_parallel
    | Echo_in_specification
    | Reserved_specification_name

  type resolve =
    | Unknown_name
    | Unknown_module
    | Not_visible
    | Ambiguous_module
    | Duplicate_import
    | Unused_import
    | Intrinsic_import
    | Shadowed_name
    | Duplicate_definition
    | Not_a_place
    | Not_generic
    | Not_a_constant
    | Alternative_bindings
    | Not_a_generic_parameter
    | Null

  type types =
    | Character_scalar_count
    | Misplaced_self_type
    | Mismatch
    | Not_bit_vector
    | Cannot_infer
    | Missing_label
    | Unknown_label
    | Out_of_order
    | Missing_argument
    | Too_many_arguments
    | Repeated_argument
    | Missing_mode
    | Redundant_mode
    | Wrong_mode
    | Unknown_member
    | Ambiguous_method
    | Private_field
    | Not_callable
    | Not_a_value
    | No_impl
    | Mismatched_integers
    | String_addition
    | Literal_out_of_range
    | Integer_for_float
    | Negated_unsigned
    | Unused_value
    | Not_assignable
    | Wrong_try
    | Lambda_needs_type
    | Not_a_record
    | Unknown_variant
    | Specification_only
    | Not_in_specification
    | Not_structural
    | Not_overridable
    | Wrong_receiver
    | Not_indexable
    | Implements_built_in
    | Not_derivable
    | Not_a_type
    | Not_a_trait
    | Not_a_capability
    | Misplaced_capability_parameter
    | Arity
    | Argument_kind
    | Unsatisfied_bound
    | Private_in_public
    | Method_outside_package
    | Default_not_constant
    | Not_constant
    | Constant_overflow
    | Main_signature
    | Duplicate_field
    | Cannot_derive
    | Derives_inferred
    | Redeclared_method
    | Trait_cycle
    | Missing_member
    | Extra_member
    | Signature_mismatch
    | Missing_required_impl
    | Implements_panic
    | Impl_uses
    | Unknown_associated_type
    | Unknown_associated_capability
    | Associated_type_not_fixed

  type patterns = Not_covered | Unreachable_arm | Unreachable_alternative | Refutable
  type usage = Unused_variable | Unreachable_code

  type ownership =
    | Views_temporary
    | Use_after_move
    | Not_owned
    | Not_reinitialized
    | Conflicting_loan
    | Mutated_while_viewed
    | View_escapes
    | Self_referential
    | View_crosses_capability
    | Needs_owned
    | Data_race
    | Lent_part_escapes
    | Lends_other_parameter
    | Read_only_view
    | Lent_mut_in_variant
    | Task_outlives_view

  type capabilities =
    | Not_available
    | Lambda_uses
    | Not_granted
    | Provide_mode
    | Not_an_implementation
    | Callback_may_deadlock
    | Monitor_needs_tasks

  type prover =
    | Overflow
    | Division
    | Shift
    | Out_of_range
    | Requires
    | Ensures
    | Invariant
    | Termination
    | Assertion
    | Law
    | Cost
    | Disjoint
    | Unreachable
    | Unsupported

  type package =
    | Impl_location
    | Sealed_trait_impl
    | Overlapping_impls
    | Method_name_clash
    | Needs_indirect
    | Not_strictly_positive
    | Growing_type
    | Instantiation_cycle
    | Duplicate_test

  (* Each stage adds its own group; its codes are named "stage.code". *)
  type t =
    | Lexer of lexer
    | Parser of parser
    | Resolve of resolve
    | Types of types
    | Patterns of patterns
    | Usage of usage
    | Ownership of ownership
    | Capabilities of capabilities
    | Package of package
    | Prover of prover
    | Too_many_diagnostics

  val name : t -> string
end

type 'span edit = { span : 'span; replacement : string }
(** Replace the bytes of [span] with [replacement]. An empty span inserts. *)

type 'span fix = { title : string; edits : 'span edit list }

type 'span diagnostic = {
  code : Code.t;
  message : string;
      (** Whole sentences, each starting with a capital letter, or with code in backticks, and
          ending with a period: "This string is not closed on its line." Every stage writes them the
          same way. *)
  span : 'span;
  notes : ('span * string) list;
  fixes : 'span fix list;  (** Alternatives. Most diagnostics have at most one. *)
}
(** A diagnostic's spans are either file offsets, {!span}, or offsets relative to a definition's
    base, [Syntax.Span.t]. Every stage that caches its results per definition keeps its diagnostics
    relative, so that moving a definition invalidates none of them. The two kinds of span are
    different types, so a relative diagnostic cannot be shown at the wrong place in its file. *)

type t = span diagnostic
(** A diagnostic in its file's offsets, which can be shown. *)

val make :
  ?notes:('span * string) list ->
  ?fixes:'span fix list ->
  code:Code.t ->
  'span ->
  string ->
  'span diagnostic

val fix : string -> 'span edit list -> 'span fix
val replace : 'span -> string -> 'span edit

val insert : 'span -> string -> 'span edit
(** [insert at text] inserts [text] at [at], an empty span. *)

val delete : 'span -> 'span edit

val edit_distance : string -> string -> int
(** The optimal string alignment distance: insertions, deletions, substitutions, and swaps of two
    neighboring letters each count one. *)

val closest : string -> string list -> string option
(** The candidate closest to a name, if one is near enough to be a typo: at most a third of the
    name's letters away, and at least one. *)

type reported

val reported : _ diagnostic -> reported
(** The diagnostic is the report. *)

val recovered : _ -> reported
(** A span the parser recorded as a recovery is the report: it records one only where it or the
    lexer reported an error. *)

val map_spans : ('a -> 'b) -> 'a diagnostic -> 'b diagnostic
(** Converts every span in a diagnostic: its own, its notes', and its fixes' edits. *)

val apply_fix : string -> span fix -> string
(** Applies a fix's edits to the text it was made for. Raises [Invalid_argument] if the edits
    overlap. *)

(** Collects the diagnostics of one file. Every diagnostic is kept, so that later checks, such as of
    fixes, see all of them; only {!shown} limits how many are listed. *)
module Collector : sig
  type diagnostic := t
  type t

  val create : unit -> t
  val add : t -> diagnostic -> unit

  val to_list : t -> diagnostic list
  (** In order of position. *)
end

val shown : t list -> t list
(** The diagnostics to list: at most {!limit}, and then, if there were more, one with the code
    [Too_many_diagnostics] that counts the rest, so that a binary file opened by mistake gives a
    short report. *)

(** {1 Showing diagnostics} *)

val render : Source.t -> t -> string
(** For people: the position, the code and message, the line of source with the span marked, and the
    notes and fixes. *)

val to_json : Source.t -> t list -> string
(** For tools: a JSON array. Spans carry byte offsets as well as lines and columns, and fixes are
    always byte ranges. The output is always valid UTF-8: a byte that is not valid UTF-8, which can
    only come from quoted source text, is written as U+FFFD. *)

val to_json_object : Source.t -> t -> string
(** One diagnostic as {!to_json} writes it, for a tool's output that gathers several files'. *)

val json_string : string -> string
(** Text as a JSON string, always valid UTF-8, as {!to_json} writes every string: a byte that is not
    valid UTF-8 is written as U+FFFD. *)

val quote : string -> string
(** Text in double quotes, with quotes, backslashes, control characters, and bytes that are not
    valid UTF-8 escaped, so that text in any script stays readable and the result is valid UTF-8. *)

module For_testing : sig
  val limit : int
end
