(rule
 (with-stdout-to
  blank_lines.output
  (with-accepted-exit-codes
   (or 0 1)
   (run %{exe:../../bin/truss_lex.exe} --tokens %{dep:blank_lines.truss}))))

(rule
 (alias runtest)
 (action
  (diff blank_lines.expected blank_lines.output)))

(rule
 (with-stdout-to
  bracket_recovery.output
  (with-accepted-exit-codes
   (or 0 1)
   (run %{exe:../../bin/truss_lex.exe} --tokens %{dep:bracket_recovery.truss}))))

(rule
 (alias runtest)
 (action
  (diff bracket_recovery.expected bracket_recovery.output)))

(rule
 (with-stdout-to
  brackets.output
  (with-accepted-exit-codes
   (or 0 1)
   (run %{exe:../../bin/truss_lex.exe} --tokens %{dep:brackets.truss}))))

(rule
 (alias runtest)
 (action
  (diff brackets.expected brackets.output)))

(rule
 (with-stdout-to
  deep_interpolation.output
  (with-accepted-exit-codes
   (or 0 1)
   (run %{exe:../../bin/truss_lex.exe} --tokens %{dep:deep_interpolation.truss}))))

(rule
 (alias runtest)
 (action
  (diff deep_interpolation.expected deep_interpolation.output)))

(rule
 (with-stdout-to
  empty.output
  (with-accepted-exit-codes
   (or 0 1)
   (run %{exe:../../bin/truss_lex.exe} --tokens %{dep:empty.truss}))))

(rule
 (alias runtest)
 (action
  (diff empty.expected empty.output)))

(rule
 (with-stdout-to
  layout.output
  (with-accepted-exit-codes
   (or 0 1)
   (run %{exe:../../bin/truss_lex.exe} --tokens %{dep:layout.truss}))))

(rule
 (alias runtest)
 (action
  (diff layout.expected layout.output)))

(rule
 (with-stdout-to
  line_endings.output
  (with-accepted-exit-codes
   (or 0 1)
   (run %{exe:../../bin/truss_lex.exe} --tokens %{dep:line_endings.truss}))))

(rule
 (alias runtest)
 (action
  (diff line_endings.expected line_endings.output)))

(rule
 (with-stdout-to
  name_case.output
  (with-accepted-exit-codes
   (or 0 1)
   (run %{exe:../../bin/truss_lex.exe} --tokens %{dep:name_case.truss}))))

(rule
 (alias runtest)
 (action
  (diff name_case.expected name_case.output)))

(rule
 (with-stdout-to
  name_unicode.output
  (with-accepted-exit-codes
   (or 0 1)
   (run %{exe:../../bin/truss_lex.exe} --tokens %{dep:name_unicode.truss}))))

(rule
 (alias runtest)
 (action
  (diff name_unicode.expected name_unicode.output)))

(rule
 (with-stdout-to
  names.output
  (with-accepted-exit-codes
   (or 0 1)
   (run %{exe:../../bin/truss_lex.exe} --tokens %{dep:names.truss}))))

(rule
 (alias runtest)
 (action
  (diff names.expected names.output)))

(rule
 (with-stdout-to
  no_trailing_newline.output
  (with-accepted-exit-codes
   (or 0 1)
   (run %{exe:../../bin/truss_lex.exe} --tokens %{dep:no_trailing_newline.truss}))))

(rule
 (alias runtest)
 (action
  (diff no_trailing_newline.expected no_trailing_newline.output)))

(rule
 (with-stdout-to
  number_errors.output
  (with-accepted-exit-codes
   (or 0 1)
   (run %{exe:../../bin/truss_lex.exe} --tokens %{dep:number_errors.truss}))))

(rule
 (alias runtest)
 (action
  (diff number_errors.expected number_errors.output)))

(rule
 (with-stdout-to
  numbers.output
  (with-accepted-exit-codes
   (or 0 1)
   (run %{exe:../../bin/truss_lex.exe} --tokens %{dep:numbers.truss}))))

(rule
 (alias runtest)
 (action
  (diff numbers.expected numbers.output)))

(rule
 (with-stdout-to
  punctuation.output
  (with-accepted-exit-codes
   (or 0 1)
   (run %{exe:../../bin/truss_lex.exe} --tokens %{dep:punctuation.truss}))))

(rule
 (alias runtest)
 (action
  (diff punctuation.expected punctuation.output)))

(rule
 (with-stdout-to
  raw_string_errors.output
  (with-accepted-exit-codes
   (or 0 1)
   (run %{exe:../../bin/truss_lex.exe} --tokens %{dep:raw_string_errors.truss}))))

(rule
 (alias runtest)
 (action
  (diff raw_string_errors.expected raw_string_errors.output)))

(rule
 (with-stdout-to
  raw_strings.output
  (with-accepted-exit-codes
   (or 0 1)
   (run %{exe:../../bin/truss_lex.exe} --tokens %{dep:raw_strings.truss}))))

(rule
 (alias runtest)
 (action
  (diff raw_strings.expected raw_strings.output)))

(rule
 (with-stdout-to
  raw_unterminated.output
  (with-accepted-exit-codes
   (or 0 1)
   (run %{exe:../../bin/truss_lex.exe} --tokens %{dep:raw_unterminated.truss}))))

(rule
 (alias runtest)
 (action
  (diff raw_unterminated.expected raw_unterminated.output)))

(rule
 (with-stdout-to
  raw_unterminated_at_end.output
  (with-accepted-exit-codes
   (or 0 1)
   (run %{exe:../../bin/truss_lex.exe} --tokens %{dep:raw_unterminated_at_end.truss}))))

(rule
 (alias runtest)
 (action
  (diff raw_unterminated_at_end.expected raw_unterminated_at_end.output)))

(rule
 (with-stdout-to
  rejected.output
  (with-accepted-exit-codes
   (or 0 1)
   (run %{exe:../../bin/truss_lex.exe} --tokens %{dep:rejected.truss}))))

(rule
 (alias runtest)
 (action
  (diff rejected.expected rejected.output)))

(rule
 (with-stdout-to
  source_text.output
  (with-accepted-exit-codes
   (or 0 1)
   (run %{exe:../../bin/truss_lex.exe} --tokens %{dep:source_text.truss}))))

(rule
 (alias runtest)
 (action
  (diff source_text.expected source_text.output)))

(rule
 (with-stdout-to
  string_errors.output
  (with-accepted-exit-codes
   (or 0 1)
   (run %{exe:../../bin/truss_lex.exe} --tokens %{dep:string_errors.truss}))))

(rule
 (alias runtest)
 (action
  (diff string_errors.expected string_errors.output)))

(rule
 (with-stdout-to
  strings.output
  (with-accepted-exit-codes
   (or 0 1)
   (run %{exe:../../bin/truss_lex.exe} --tokens %{dep:strings.truss}))))

(rule
 (alias runtest)
 (action
  (diff strings.expected strings.output)))

