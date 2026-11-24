open Description

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
  | Foreign_escape of { replacement : string }
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
  | Replace_with_line_feed
  | Remove_empty_interpolation
  | Close_string
  | Close_string_with of string
  | Move_closing_delimiter
  | Indent_like_delimiter
  | Replace_semicolon
  | Remove_semicolon
  | Delete_characters of { is_plural : bool }
  | Replace_with of string
  | Write_interpolation
  | Write_ordinary_string
  | Write_raw_string
  | Remove_prefix
  | Write_between_quotes
  | Insert of string

type fix = { action : action; edits : Source.span Diagnostic.edit list }

type t = {
  at : Source.span;
  problem : problem;
  notes : (Source.span * note) list;
  fixes : fix list;
}

let say text = [ Text text ]

let show_character = function
  | Invalid_byte byte -> Printf.sprintf "the byte 0x%02X" byte
  | Ascii character -> Printf.sprintf "`%c`" character
  | Unicode { text; code_point } -> Printf.sprintf "`%s` (U+%04X)" text code_point

let show_radix = function Hexadecimal -> "hexadecimal" | Binary -> "binary" | Octal -> "octal"

let find_code : problem -> Diagnostic.Code.lexer = function
  | Unused_character _ | Dollar_outside_string | Apostrophe | Backtick -> Unexpected_character
  | Name (Not_ascii _) -> Name_not_ascii
  | Name _ -> Name_case
  | Number Misplaced_underscore -> Number_underscore
  | Number
      ( Radix_without_digits _ | Exponent_without_digits | Missing_digit_after_point _
      | Missing_digit_before_point _ ) ->
      Number_missing_digits
  | Number (Invalid_radix_digit _) -> Number_invalid_digit
  | Number (Followed_by_name _) -> Number_followed_by_name
  | Number (Digit_separator _) -> Number_digit_separator
  | Number Hexadecimal_float -> Number_hexadecimal_float
  | Number (Uppercase_prefix _) -> Number_uppercase_prefix
  | Number (Type_suffix _) -> Number_suffix
  | Number Uppercase_exponent -> Number_uppercase_exponent
  | Number (Leading_zero _) -> Number_leading_zero
  | Forbidden_characters _ -> Forbidden_character
  | Invalid_utf8 -> Invalid_utf8
  | Carriage_return -> Carriage_return
  | Interpolation_too_deep _ -> Interpolation_too_deep
  | Line_break_in_interpolation | Multi_line_string_in_interpolation -> Line_break_in_interpolation
  | Empty_interpolation -> Empty_interpolation
  | Unclosed_ordinary_string | Unclosed_one_line_raw_string _ | Unclosed_raw_string _ ->
      Unterminated_string
  | Not_an_escape _ | Line_continuation | Unicode_escape_form | Escape_not_scalar_value _
  | Foreign_escape _ | Parenthesized_interpolation | Escaped_apostrophe ->
      Invalid_escape
  | Long_quote_run _ -> Raw_string_quotes
  | Raw_closing_not_alone -> Raw_string_closing_not_alone
  | Raw_string_indentation _ -> Raw_string_indentation
  | Comment _ -> Comment
  | Semicolon | Inline_semicolon -> Semicolon
  | Attribute | Inline_attribute -> Attribute
  | Confusable _ | Curly_quote -> Confusable_character
  | Path_separator -> Path_separator
  | Foreign_operator _ -> Foreign_operator
  | Strict_equality _ -> Strict_equality
  | Character_literal _ -> Character_literal
  | String_prefix _ | Raw_hash_string -> String_prefix
  | Template_literal | Quoted_string -> String_delimiter
  | Lifetime -> Lifetime
  | Unclosed_bracket _ -> Unclosed_bracket
  | Unmatched_closer _ -> Unmatched_closing_bracket

let describe_name_problem = function
  | Leading_underscore -> "Names cannot start with `_`."
  | Constant_case name ->
      Printf.sprintf
        "`%s` is written like a constant from another language. Constants are values, so their \
         names are lower_snake_case."
        name
  | Upper_with_underscore ->
      "A name that starts with an uppercase letter is UpperCamelCase, with no `_`."
  | Lower_with_upper ->
      "A name that starts with a lowercase letter is lower_snake_case, with no uppercase letters."
  | Trailing_underscore -> "Names cannot end with `_`."
  | Doubled_underscore -> "`_` appears only singly, between the parts of a name."
  | Not_ascii character ->
      Printf.sprintf
        "Names use only ASCII letters, digits, and `_`, and %s is not ASCII. Text in any language \
         goes in strings."
        (show_character character)

let describe_number_problem = function
  | Misplaced_underscore -> "`_` can only go between digits."
  | Radix_without_digits { prefix; radix } ->
      Printf.sprintf "`%s` must be followed by %s digits." prefix (show_radix radix)
  | Invalid_radix_digit { digit; radix } ->
      Printf.sprintf "`%s` is not a %s digit." digit (show_radix radix)
  | Exponent_without_digits -> "The exponent needs digits after `e`."
  | Followed_by_name character ->
      Printf.sprintf "A number cannot be followed directly by a name character such as `%s`."
        character
  | Digit_separator { grouped } -> Printf.sprintf "Digits are grouped with `_`, as in `%s`." grouped
  | Hexadecimal_float -> "Truss has no hexadecimal floats. Write the value as a decimal float."
  | Uppercase_prefix { prefix } ->
      Printf.sprintf "Number prefixes are lowercase: write `%s`." prefix
  | Type_suffix { suffix; type_name; number } ->
      Printf.sprintf
        "Number literals have no type suffixes such as `%s`. A literal takes its type from its \
         context, as in `let value: %s = %s`."
        suffix type_name number
  | Uppercase_exponent -> "The exponent is written with a lowercase `e`."
  | Leading_zero { octal = Some (written, without_zeros) } ->
      Printf.sprintf
        "Decimal numbers do not start with `0`. In C and Go, `%s` would be octal: write `0o%s` for \
         octal, or `%s` for decimal."
        written without_zeros without_zeros
  | Leading_zero { octal = None } -> "Decimal numbers do not start with `0`."
  | Missing_digit_after_point { written } ->
      Printf.sprintf "A float has a digit after its `.`: `%s0`." written
  | Missing_digit_before_point { fixed = Some fixed } ->
      Printf.sprintf "A float has a digit before its `.`: `%s`." fixed
  | Missing_digit_before_point { fixed = None } -> "A float has a digit before its `.`."

let describe_forbidden ~characters ~context =
  let names =
    String.concat ", "
      (List.map
         (fun { code_point; name; _ } ->
           match name with
           | Some name -> Printf.sprintf "U+%04X %s" code_point name
           | None -> Printf.sprintf "U+%04X" code_point)
         characters)
  in
  let reasons =
    List.sort_uniq compare
      (List.map
         (fun { kind; _ } ->
           match kind with
           | Bidirectional_control ->
               "Bidirectional controls can make code display differently from how it compiles."
           | Control_character -> "Control characters can make a terminal hide or rewrite text."
           | Invisible_character -> "Invisible characters can hide text from a reader.")
         characters)
  in
  let base =
    Printf.sprintf "%s %s not allowed in source files. %s" names
      (if List.length characters > 1 then "are" else "is")
      (String.concat " " reasons)
  in
  match context with
  | In_code -> base
  | In_ordinary_string -> base ^ " Write it as an escape, so that it can be seen."
  | In_raw_string ->
      base
      ^ " A raw string has no escapes, so write the text as an ordinary string, with the character \
         as an escape such as `\\u{200B}`."

let describe_whitespace whitespace =
  if whitespace = "" then "no indentation"
  else
    let rec list_groups index =
      if index >= String.length whitespace then []
      else
        let character = whitespace.[index] in
        let rec stop position =
          if position < String.length whitespace && whitespace.[position] = character then
            stop (position + 1)
          else position
        in
        let next = stop index in
        let count = next - index in
        (if character = '\t' then Diagnostic.show_count count "tab" "tabs"
         else Diagnostic.show_count count "space" "spaces")
        :: list_groups next
    in
    String.concat " then " (list_groups 0)

let comment_message = "Truss has no comments. Say this with a name, a contract, or a test instead."

let describe_problem at = function
  | Unused_character character ->
      say (Printf.sprintf "%s is not used in Truss." (show_character character))
  | Dollar_outside_string ->
      say
        "`$` is used only in strings: `${...}` inside a string interpolates, and `$`s before a raw \
         string's `\"\"\"` choose how it interpolates."
  | Name problem -> say (describe_name_problem problem)
  | Number problem -> say (describe_number_problem problem)
  | Forbidden_characters { characters; context } -> say (describe_forbidden ~characters ~context)
  | Invalid_utf8 -> say "Source files must be UTF-8, and these bytes are not valid UTF-8."
  | Carriage_return -> say "A carriage return is a line break only before a line feed."
  | Interpolation_too_deep { limit } ->
      say (Printf.sprintf "Interpolations can nest at most %d deep." limit)
  | Line_break_in_interpolation ->
      say
        "An interpolation cannot contain a line break. Move the expression into a `let` before the \
         string."
  | Multi_line_string_in_interpolation ->
      say
        "An interpolation cannot contain a line break, so it cannot hold a multi-line string. Move \
         the expression into a `let` before the string."
  | Empty_interpolation -> say "An interpolation needs an expression."
  | Unclosed_ordinary_string ->
      say
        "This string is not closed on its line. An ordinary string fits on one line; text that \
         spans lines goes in a raw string, between `\"\"\"`s."
  | Not_an_escape escape ->
      (match escape with
        | Written_escape -> [ Text "`"; Quote at; Text "`" ]
        | Backslash_then character ->
            [ Text (Printf.sprintf "`\\` followed by %s" (show_character character)) ])
      @ say
          " is not an escape. The escapes are `\\n`, `\\t`, `\\r`, `\\0`, `\\\\`, `\\\"`, `\\${`, \
           and `\\u{...}`. For text with backslashes, such as a regular expression or a Windows \
           path, a raw string has no escapes: `\"\"\"\\d+\"\"\"`."
  | Line_continuation ->
      say
        "A `\\` at the end of a line does not continue the string. Text that spans lines goes in a \
         raw string, between `\"\"\"`s."
  | Unicode_escape_form ->
      say "A Unicode escape is written `\\u{...}`, with 1 to 6 hexadecimal digits."
  | Escape_not_scalar_value { digits } ->
      say
        (Printf.sprintf
           "`\\u{%s}` is not a Unicode scalar value: surrogates and values above 10FFFF have no \
            character."
           digits)
  | Long_quote_run { run; quotes; is_multi_line } ->
      say
        (Printf.sprintf "A run of %d `\"`s is longer than this string's delimiter of %d.%s" run
           quotes
           (if is_multi_line then " Open the string with a longer delimiter."
            else
              " A one-line raw string cannot start or end with `\"`; use the multi-line form, or a \
               longer delimiter."))
  | Unclosed_one_line_raw_string { delimiter } ->
      say
        (Printf.sprintf
           "This raw string is not closed on its line. A raw string with text after its opening \
            `%s` is a one-line string. For several lines, start the text on the line after the \
            opening `%s`."
           delimiter delimiter)
  | Unclosed_raw_string { delimiter } ->
      say
        (Printf.sprintf
           "This raw string is never closed, so it runs to the end of the file. Close it with `%s` \
            on a line of its own."
           delimiter)
  | Raw_closing_not_alone ->
      say "The closing delimiter of a multi-line raw string goes on a line of its own."
  | Raw_string_indentation { expected; found } ->
      say
        (Printf.sprintf
           "Every line of a multi-line raw string starts with the indentation of its closing \
            delimiter, which is %s. This line starts with %s."
           (describe_whitespace expected) (describe_whitespace found))
  | Comment { is_closed = true } -> say comment_message
  | Comment { is_closed = false } ->
      say (comment_message ^ " This comment is never closed, so it runs to the end of the file.")
  | Semicolon -> say "Statements end at a line break. Truss has no `;`."
  | Inline_semicolon -> say "Truss has no `;`."
  | Attribute ->
      say
        "Truss has no attributes. A type lists the traits it derives in a `derives` clause, and a \
         test is a `test` definition."
  | Inline_attribute -> say "Truss has no attributes."
  | Confusable { character; spelled } ->
      say
        (Printf.sprintf "%s is not %s. Truss is written with ASCII punctuation."
           (show_character character)
           (match spelled with
           | Space_character -> "the space character"
           | Punctuation spelling -> "`" ^ spelling ^ "`"))
  | Foreign_escape { replacement } ->
      [
        Text "`";
        Quote at;
        Text
          (Printf.sprintf
             "` is not an escape in Truss. A character is written by its code point: `%s`."
             replacement);
      ]
  | Parenthesized_interpolation -> say "A string interpolates with `${...}`."
  | Escaped_apostrophe -> say "`'` needs no escape in a string."
  | Path_separator ->
      say "Truss separates the names of a path with `.`, as in `json.parse` and `Shape.Circle`."
  | Foreign_operator Half_open_range -> say "Truss has no `..<`; write `..`."
  | Foreign_operator Diamond -> say "Truss has no `<>`; write `!=`."
  | Foreign_operator Range_ellipsis ->
      say
        "Truss has no `...`. A range that leaves out its end is written `..`, and one that \
         includes its end is written `..=`."
  | Foreign_operator Todo_ellipsis ->
      say "Truss has no `...`; code that is not written yet is `todo`."
  | Foreign_operator Spread_ellipsis ->
      say
        "Truss has no `...`: it has no spread or rest operator, and a function takes a list where \
         it takes any number of values."
  | Strict_equality { written; replacement } ->
      say
        (Printf.sprintf "Truss has no `%s`. `%s` already compares values of the same type." written
           replacement)
  | Character_literal { is_byte; replacement } ->
      let kind = if is_byte then "byte" else "character" in
      say
        (Printf.sprintf "Truss has no %s literals. A single %s is a tagged string: `%s`." kind kind
           replacement)
  | String_prefix (Format_prefix prefix) ->
      say
        (Printf.sprintf
           "Truss has no `%s` strings. Every string interpolates with `${...}`, as in `\"Hello \
            ${name}\"`."
           prefix)
  | String_prefix (Raw_prefix prefix) ->
      say
        (Printf.sprintf
           "Truss has no `%s` strings. A raw string, which has no escapes, is written between \
            `\"\"\"`s, as in `\"\"\"\\d+\"\"\"`."
           prefix)
  | String_prefix Byte_prefix ->
      say "Truss has no byte strings. A string is UTF-8 text, and `text.bytes()` gives its bytes."
  | Raw_hash_string ->
      say
        "Truss has no `r#` strings. A raw string is written between `\"\"\"`s, or between more \
         quotes when its text has `\"\"\"` in it."
  | Template_literal ->
      say
        "Truss has no template literals. Every string is written between `\"`s and interpolates \
         with `${...}`."
  | Quoted_string -> say "A string is written between `\"`s."
  | Curly_quote -> say "A string is written between straight quotes, `\"`. This is a curly quote."
  | Lifetime -> say "Truss has no lifetimes. How long a view lasts is checked without annotations."
  | Apostrophe -> say "`'` is not used in Truss. Strings are written with `\"`."
  | Backtick -> say "The backtick is not used in Truss."
  | Unclosed_bracket { opener; before } ->
      say
        (Printf.sprintf "This `%s` is never closed%s." opener
           (match before with
           | Some End_of_file -> " before the end of the file"
           | Some End_of_interpolation -> " before the end of the interpolation"
           | Some Next_definition -> " before the next definition"
           | None -> ""))
  | Unmatched_closer { closer; opener } ->
      say (Printf.sprintf "This `%s` has no `%s` to close." closer opener)

let describe_note = function
  | Also_unclosed { opener } -> say (Printf.sprintf "This `%s` is not closed either." opener)
  | Closes_earlier { closer; opener } ->
      say (Printf.sprintf "This `%s` closes an earlier `%s` first." closer opener)
  | Meant_to_end { delimiter } ->
      say
        (Printf.sprintf "The string may have been meant to end with `%s` before this line."
           delimiter)
  | Empty_raw_string -> say "For an empty string, write `\"\"`."

let describe_action = function
  | Write code -> "Write `" ^ code ^ "`"
  | Write_reading { code; reading } ->
      Printf.sprintf "Write `%s` (%s)" code
        (match reading with Octal_reading -> "octal" | Decimal_reading -> "decimal")
  | Replace_with_line_feed -> "Replace with a line feed"
  | Remove_empty_interpolation -> "Remove the empty interpolation"
  | Close_string -> "Close the string"
  | Close_string_with delimiter -> "Close the string with `" ^ delimiter ^ "`"
  | Move_closing_delimiter -> "Move the closing delimiter to its own line"
  | Indent_like_delimiter -> "Indent the line like the closing delimiter"
  | Replace_semicolon -> "Replace the `;` with a line break"
  | Remove_semicolon -> "Remove the `;`"
  | Delete_characters { is_plural } ->
      if is_plural then "Delete the characters" else "Delete the character"
  | Replace_with replacement -> "Replace with `" ^ replacement ^ "`"
  | Write_interpolation -> "Write `${...}`"
  | Write_ordinary_string -> "Write an ordinary string"
  | Write_raw_string -> "Write a raw string"
  | Remove_prefix -> "Remove the prefix"
  | Write_between_quotes -> "Write the string between `\"`s"
  | Insert closers -> Printf.sprintf "Insert `%s`" closers

let describe ({ at; problem; notes; fixes } : t) : Source.span Description.t =
  {
    code = Lexer (find_code problem);
    severity = Error;
    location = At at;
    message = describe_problem at problem;
    notes = List.map (fun (span, note) -> (At span, describe_note note)) notes;
    fixes =
      List.map
        (fun ({ action; edits } : fix) : Source.span Description.fix ->
          {
            title = say (describe_action action);
            edits =
              List.map
                (fun (edit : Source.span Diagnostic.edit) ->
                  Replace (edit.span, [ Text edit.replacement ]))
                edits;
          })
        fixes;
  }

let render ~text diagnostic = Description.render_file ~text (describe diagnostic)

let examples : t list =
  [
    {
      at = Source.make_span 0 1;
      problem = Unused_character (Invalid_byte 2);
      notes = [];
      fixes = [];
    };
    { at = Source.make_span 0 1; problem = Unused_character (Ascii '#'); notes = []; fixes = [] };
    {
      at = Source.make_span 0 1;
      problem = Unused_character (Unicode { text = "‹text›"; code_point = 0x200B });
      notes = [];
      fixes = [];
    };
    { at = Source.make_span 0 1; problem = Dollar_outside_string; notes = []; fixes = [] };
    { at = Source.make_span 0 1; problem = Name Leading_underscore; notes = []; fixes = [] };
    { at = Source.make_span 0 1; problem = Name (Constant_case "‹name›"); notes = []; fixes = [] };
    { at = Source.make_span 0 1; problem = Name Upper_with_underscore; notes = []; fixes = [] };
    { at = Source.make_span 0 1; problem = Name Lower_with_upper; notes = []; fixes = [] };
    { at = Source.make_span 0 1; problem = Name Trailing_underscore; notes = []; fixes = [] };
    { at = Source.make_span 0 1; problem = Name Doubled_underscore; notes = []; fixes = [] };
    {
      at = Source.make_span 0 1;
      problem = Name (Not_ascii (Invalid_byte 2));
      notes = [];
      fixes = [];
    };
    { at = Source.make_span 0 1; problem = Number Misplaced_underscore; notes = []; fixes = [] };
    {
      at = Source.make_span 0 1;
      problem = Number (Radix_without_digits { prefix = "‹prefix›"; radix = Hexadecimal });
      notes = [];
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Number (Invalid_radix_digit { digit = "‹digit›"; radix = Hexadecimal });
      notes = [];
      fixes = [];
    };
    { at = Source.make_span 0 1; problem = Number Exponent_without_digits; notes = []; fixes = [] };
    {
      at = Source.make_span 0 1;
      problem = Number (Followed_by_name "‹number›");
      notes = [];
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Number (Digit_separator { grouped = "‹grouped›" });
      notes = [];
      fixes = [];
    };
    { at = Source.make_span 0 1; problem = Number Hexadecimal_float; notes = []; fixes = [] };
    {
      at = Source.make_span 0 1;
      problem = Number (Uppercase_prefix { prefix = "‹prefix›" });
      notes = [];
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem =
        Number (Type_suffix { suffix = "‹suffix›"; type_name = "‹type_name›"; number = "‹number›" });
      notes = [];
      fixes = [];
    };
    { at = Source.make_span 0 1; problem = Number Uppercase_exponent; notes = []; fixes = [] };
    {
      at = Source.make_span 0 1;
      problem = Number (Leading_zero { octal = Some ("‹octal›", "‹octal›") });
      notes = [];
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Number (Missing_digit_after_point { written = "‹written›" });
      notes = [];
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Number (Missing_digit_before_point { fixed = Some "‹fixed›" });
      notes = [];
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem =
        Forbidden_characters
          {
            characters =
              [ { code_point = 0x200B; name = Some "‹name›"; kind = Bidirectional_control } ];
            context = In_code;
          };
      notes = [];
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem =
        Forbidden_characters
          {
            characters =
              [ { code_point = 0x200B; name = Some "‹name›"; kind = Bidirectional_control } ];
            context = In_ordinary_string;
          };
      notes = [];
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem =
        Forbidden_characters
          {
            characters =
              [ { code_point = 0x200B; name = Some "‹name›"; kind = Bidirectional_control } ];
            context = In_raw_string;
          };
      notes = [];
      fixes = [];
    };
    { at = Source.make_span 0 1; problem = Invalid_utf8; notes = []; fixes = [] };
    { at = Source.make_span 0 1; problem = Carriage_return; notes = []; fixes = [] };
    {
      at = Source.make_span 0 1;
      problem = Interpolation_too_deep { limit = 64 };
      notes = [];
      fixes = [];
    };
    { at = Source.make_span 0 1; problem = Line_break_in_interpolation; notes = []; fixes = [] };
    {
      at = Source.make_span 0 1;
      problem = Multi_line_string_in_interpolation;
      notes = [];
      fixes = [];
    };
    { at = Source.make_span 0 1; problem = Empty_interpolation; notes = []; fixes = [] };
    { at = Source.make_span 0 1; problem = Unclosed_ordinary_string; notes = []; fixes = [] };
    { at = Source.make_span 0 1; problem = Not_an_escape Written_escape; notes = []; fixes = [] };
    {
      at = Source.make_span 0 1;
      problem = Not_an_escape (Backslash_then (Invalid_byte 2));
      notes = [];
      fixes = [];
    };
    { at = Source.make_span 0 1; problem = Line_continuation; notes = []; fixes = [] };
    { at = Source.make_span 0 1; problem = Unicode_escape_form; notes = []; fixes = [] };
    {
      at = Source.make_span 0 1;
      problem = Escape_not_scalar_value { digits = "‹digits›" };
      notes = [];
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Long_quote_run { run = 4; quotes = 3; is_multi_line = false };
      notes = [];
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Long_quote_run { run = 4; quotes = 3; is_multi_line = true };
      notes = [];
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unclosed_one_line_raw_string { delimiter = "‹delimiter›" };
      notes = [];
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unclosed_raw_string { delimiter = "‹delimiter›" };
      notes = [];
      fixes = [];
    };
    { at = Source.make_span 0 1; problem = Raw_closing_not_alone; notes = []; fixes = [] };
    {
      at = Source.make_span 0 1;
      problem = Raw_string_indentation { expected = "‹expected›"; found = "‹found›" };
      notes = [];
      fixes = [];
    };
    { at = Source.make_span 0 1; problem = Comment { is_closed = false }; notes = []; fixes = [] };
    { at = Source.make_span 0 1; problem = Comment { is_closed = true }; notes = []; fixes = [] };
    { at = Source.make_span 0 1; problem = Semicolon; notes = []; fixes = [] };
    { at = Source.make_span 0 1; problem = Inline_semicolon; notes = []; fixes = [] };
    { at = Source.make_span 0 1; problem = Attribute; notes = []; fixes = [] };
    { at = Source.make_span 0 1; problem = Inline_attribute; notes = []; fixes = [] };
    {
      at = Source.make_span 0 1;
      problem = Confusable { character = Invalid_byte 2; spelled = Space_character };
      notes = [];
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Confusable { character = Ascii '#'; spelled = Space_character };
      notes = [];
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem =
        Confusable
          {
            character = Unicode { text = "‹text›"; code_point = 0x200B };
            spelled = Space_character;
          };
      notes = [];
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Confusable { character = Invalid_byte 2; spelled = Punctuation "‹spelled›" };
      notes = [];
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Foreign_escape { replacement = "‹replacement›" };
      notes = [];
      fixes = [];
    };
    { at = Source.make_span 0 1; problem = Parenthesized_interpolation; notes = []; fixes = [] };
    { at = Source.make_span 0 1; problem = Escaped_apostrophe; notes = []; fixes = [] };
    { at = Source.make_span 0 1; problem = Path_separator; notes = []; fixes = [] };
    {
      at = Source.make_span 0 1;
      problem = Foreign_operator Half_open_range;
      notes = [];
      fixes = [];
    };
    { at = Source.make_span 0 1; problem = Foreign_operator Diamond; notes = []; fixes = [] };
    { at = Source.make_span 0 1; problem = Foreign_operator Range_ellipsis; notes = []; fixes = [] };
    { at = Source.make_span 0 1; problem = Foreign_operator Todo_ellipsis; notes = []; fixes = [] };
    {
      at = Source.make_span 0 1;
      problem = Foreign_operator Spread_ellipsis;
      notes = [];
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Strict_equality { written = "‹written›"; replacement = "‹replacement›" };
      notes = [];
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Character_literal { is_byte = false; replacement = "‹replacement›" };
      notes = [];
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Character_literal { is_byte = true; replacement = "‹replacement›" };
      notes = [];
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = String_prefix (Format_prefix "‹string_prefix›");
      notes = [];
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = String_prefix (Raw_prefix "‹string_prefix›");
      notes = [];
      fixes = [];
    };
    { at = Source.make_span 0 1; problem = String_prefix Byte_prefix; notes = []; fixes = [] };
    { at = Source.make_span 0 1; problem = Raw_hash_string; notes = []; fixes = [] };
    { at = Source.make_span 0 1; problem = Template_literal; notes = []; fixes = [] };
    { at = Source.make_span 0 1; problem = Quoted_string; notes = []; fixes = [] };
    { at = Source.make_span 0 1; problem = Curly_quote; notes = []; fixes = [] };
    { at = Source.make_span 0 1; problem = Lifetime; notes = []; fixes = [] };
    { at = Source.make_span 0 1; problem = Apostrophe; notes = []; fixes = [] };
    { at = Source.make_span 0 1; problem = Backtick; notes = []; fixes = [] };
    {
      at = Source.make_span 0 1;
      problem = Unclosed_bracket { opener = "‹opener›"; before = Some End_of_file };
      notes = [];
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unclosed_bracket { opener = "‹opener›"; before = None };
      notes = [];
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unmatched_closer { closer = "‹closer›"; opener = "‹opener›" };
      notes = [];
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unclosed_raw_string { delimiter = "\"\"\"" };
      notes = [ (Source.make_span 0 1, Also_unclosed { opener = "‹opener›" }) ];
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unclosed_raw_string { delimiter = "\"\"\"" };
      notes =
        [ (Source.make_span 0 1, Closes_earlier { closer = "‹closer›"; opener = "‹opener›" }) ];
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unclosed_raw_string { delimiter = "\"\"\"" };
      notes = [ (Source.make_span 0 1, Meant_to_end { delimiter = "‹delimiter›" }) ];
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Unclosed_raw_string { delimiter = "\"\"\"" };
      notes = [ (Source.make_span 0 1, Empty_raw_string) ];
      fixes = [];
    };
    {
      at = Source.make_span 0 1;
      problem = Semicolon;
      notes = [];
      fixes =
        [
          {
            action = Write "‹write›";
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Semicolon;
      notes = [];
      fixes =
        [
          {
            action = Write_reading { code = "‹code›"; reading = Octal_reading };
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Semicolon;
      notes = [];
      fixes =
        [
          {
            action = Write_reading { code = "‹code›"; reading = Decimal_reading };
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Semicolon;
      notes = [];
      fixes =
        [
          {
            action = Replace_with_line_feed;
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Semicolon;
      notes = [];
      fixes =
        [
          {
            action = Remove_empty_interpolation;
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Semicolon;
      notes = [];
      fixes =
        [
          { action = Close_string; edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ] };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Semicolon;
      notes = [];
      fixes =
        [
          {
            action = Close_string_with "‹close_string_with›";
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Semicolon;
      notes = [];
      fixes =
        [
          {
            action = Move_closing_delimiter;
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Semicolon;
      notes = [];
      fixes =
        [
          {
            action = Indent_like_delimiter;
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Semicolon;
      notes = [];
      fixes =
        [
          {
            action = Replace_semicolon;
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Semicolon;
      notes = [];
      fixes =
        [
          {
            action = Remove_semicolon;
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Semicolon;
      notes = [];
      fixes =
        [
          {
            action = Delete_characters { is_plural = false };
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Semicolon;
      notes = [];
      fixes =
        [
          {
            action = Delete_characters { is_plural = true };
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Semicolon;
      notes = [];
      fixes =
        [
          {
            action = Replace_with "‹replace_with›";
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Semicolon;
      notes = [];
      fixes =
        [
          {
            action = Write_interpolation;
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Semicolon;
      notes = [];
      fixes =
        [
          {
            action = Write_ordinary_string;
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Semicolon;
      notes = [];
      fixes =
        [
          {
            action = Write_raw_string;
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Semicolon;
      notes = [];
      fixes =
        [
          { action = Remove_prefix; edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ] };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Semicolon;
      notes = [];
      fixes =
        [
          {
            action = Write_between_quotes;
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
    {
      at = Source.make_span 0 1;
      problem = Semicolon;
      notes = [];
      fixes =
        [
          {
            action = Insert "‹insert›";
            edits = [ Diagnostic.replace (Source.make_span 0 1) "‹code›" ];
          };
        ];
    };
  ]

let list_examples code =
  List.filter (fun example -> (describe example).code = Diagnostic.Code.Lexer code) examples
