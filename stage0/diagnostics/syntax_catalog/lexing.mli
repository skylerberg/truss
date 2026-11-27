type character =
  | Invalid_byte of int
  | Ascii of char
  | Unicode of { text : string; code_point : int }

type radix = Hexadecimal | Binary | Octal
type reading = Octal_reading | Decimal_reading
type bracket_end = End_of_file | End_of_interpolation | Next_definition
type forbidden_context = In_code | In_ordinary_string | In_raw_string
type forbidden_kind = Bidirectional_control | Control_character | Invisible_character
type forbidden = { code_point : int; name : string option; kind : forbidden_kind }
type confusable = Space_character | Punctuation of string
type escape = Written_escape | Backslash_then of character
type string_prefix = Format_prefix of string | Raw_prefix of string | Byte_prefix

type foreign_operator =
  | Half_open_range
  | Diamond
  | Range_ellipsis
  | Todo_ellipsis
  | Spread_ellipsis

type name_problem =
  | Leading_underscore
  | Constant_case of string
  | Upper_with_underscore
  | Lower_with_upper
  | Trailing_underscore
  | Doubled_underscore
  | Not_ascii of character

type number_problem =
  | Misplaced_underscore
  | Radix_without_digits of { prefix : string; radix : radix }
  | Invalid_radix_digit of { digit : string; radix : radix }
  | Exponent_without_digits
  | Followed_by_name of string
  | Digit_separator of { grouped : string }
  | Hexadecimal_float
  | Uppercase_prefix of { prefix : string }
  | Type_suffix of { suffix : string; type_name : string; number : string }
  | Uppercase_exponent
  | Leading_zero of { octal : (string * string) option }
  | Missing_digit_after_point of { written : string }
  | Missing_digit_before_point of { fixed : string option }

type problem =
  | Unused_character of character
  | Dollar_outside_string
  | Name of name_problem
  | Number of number_problem
  | Forbidden_characters of { characters : forbidden list; context : forbidden_context }
  | Invalid_utf8
  | Carriage_return
  | Interpolation_too_deep of { limit : int }
  | Line_break_in_interpolation
  | Multi_line_string_in_interpolation
  | Empty_interpolation
  | Unclosed_ordinary_string
  | Not_an_escape of escape
  | Line_continuation
  | Unicode_escape_form
  | Escape_not_scalar_value of { digits : string }
  | Long_quote_run of { run : int; quotes : int; is_multi_line : bool }
  | Unclosed_one_line_raw_string of { delimiter : string }
  | Unclosed_raw_string of { delimiter : string }
  | Raw_closing_not_alone
  | Raw_string_indentation of { expected : string; found : string }
  | Comment of { is_closed : bool }
  | Semicolon
  | Inline_semicolon
  | Attribute
  | Inline_attribute
  | Confusable of { character : character; spelled : confusable }
  | Foreign_escape of { code_point : int }
  | Parenthesized_interpolation
  | Escaped_apostrophe
  | Path_separator
  | Foreign_operator of foreign_operator
  | Strict_equality of { written : string; replacement : string }
  | Character_literal of { is_byte : bool; replacement : string }
  | String_prefix of string_prefix
  | Raw_hash_string
  | Template_literal
  | Quoted_string
  | Curly_quote
  | Lifetime
  | Apostrophe
  | Backtick
  | Unclosed_bracket of { opener : string; before : bracket_end option }
  | Unmatched_closer of { closer : string; opener : string }

type note =
  | Also_unclosed of { opener : string }
  | Closes_earlier of { closer : string; opener : string }
  | Meant_to_end of { delimiter : string }
  | Empty_raw_string

type action =
  | Write of string
  | Write_reading of { code : string; reading : reading }
  | Write_escape of int
  | Write_apostrophe
  | Replace_with_line_feed
  | Remove_empty_interpolation
  | Close_string
  | Close_string_with_quotes of int
  | Move_closing_delimiter
  | Indent_like_delimiter
  | Replace_semicolon
  | Remove_semicolon
  | Delete_characters of { is_plural : bool }
  | Delete_comment
  | Replace_with_escapes of int list
  | Write_interpolation
  | Write_ordinary_string
  | Write_raw_string
  | Remove_prefix
  | Write_between_quotes
  | Insert_closers of Token.bracket list

type code =
  | Removed
  | Space
  | Line_feed
  | Line_break_indented of string
  | Quote_marks of int
  | Apostrophe_mark
  | Backslash
  | Dollar
  | Interpolation_opening
  | Interpolation_closing
  | Single_brace of { is_opening : bool }
  | Escapes of int list
  | Closer of { bracket : Token.bracket; indentation : string option }
  | Spelled of string

type edit = { replaced : Source.span; code : code }
type fix = { action : action; edits : edit list }

type t = {
  at : Source.span;
  problem : problem;
  notes : (Source.span * note) list;
  fixes : fix list;
}
