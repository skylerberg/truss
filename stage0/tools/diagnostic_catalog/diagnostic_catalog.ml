type 'node printer = { show_node : 'node -> string }

let placeholder name = "\u{2039}" ^ name ^ "\u{203A}"

let show_origin (origin : Core.origin) =
  placeholder (Option.value (Catalog.find_example_name origin) ~default:"node")

let definition_printer =
  {
    show_node =
      (function
      | Catalog.Node origin | In_definition (_, origin) -> show_origin origin
      | Definition -> placeholder "definition");
  }

let span_printer = { show_node = (fun (_ : Source.span) -> placeholder "source") }

let show_range printer ({ covering } : _ Description.range) =
  String.concat " \u{2026} " (List.map printer.show_node covering)

let show_pieces printer pieces =
  String.concat ""
    (List.map
       (function
         | Description.Text text -> text
         | Quote node -> printer.show_node node
         | Quote_over range -> show_range printer range
         | Substituted { clause; _ } -> printer.show_node clause ^ " " ^ placeholder "substituted")
       pieces)

let show_boundary printer : _ Description.boundary -> string = function
  | Start node -> "the start of " ^ printer.show_node node
  | Stop node -> "the end of " ^ printer.show_node node

let show_edit printer : _ Description.edit -> string = function
  | Replace (node, pieces) ->
      Printf.sprintf "replace %s with `%s`" (printer.show_node node) (show_pieces printer pieces)
  | Insert_before (node, pieces) ->
      Printf.sprintf "insert `%s` before %s" (show_pieces printer pieces) (printer.show_node node)
  | Insert_after (node, pieces) ->
      Printf.sprintf "insert `%s` after %s" (show_pieces printer pieces) (printer.show_node node)
  | Delete (start, stop) ->
      Printf.sprintf "delete from %s to %s" (show_boundary printer start)
        (show_boundary printer stop)
  | Remove_entry { entry; _ } -> Printf.sprintf "remove the entry %s" (show_range printer entry)
  | Remove_lines range -> Printf.sprintf "remove the lines of %s" (show_range printer range)
  | Add_lines_after (node, lines) ->
      Printf.sprintf "add the lines %s after %s"
        (String.concat ", "
           (List.map (fun line -> Printf.sprintf "`%s`" (show_pieces printer line)) lines))
        (printer.show_node node)
  | Add_line_before (node, line) ->
      Printf.sprintf "add the line `%s` before %s" (show_pieces printer line)
        (printer.show_node node)

let show_location printer : _ Description.location -> string = function
  | At node -> printer.show_node node
  | Over range -> show_range printer range
  | Before node -> "before " ^ printer.show_node node
  | After node -> "after " ^ printer.show_node node

let print_description printer (description : _ Description.t) =
  Printf.printf "- %s\n  At %s.\n"
    (show_pieces printer description.message)
    (show_location printer description.location);
  List.iter
    (fun (location, note) ->
      Printf.printf "  - Note at %s: %s\n" (show_location printer location)
        (show_pieces printer note))
    description.notes;
  List.iter
    (fun (fix : _ Description.fix) ->
      Printf.printf "  - Fix: %s (%s)\n" (show_pieces printer fix.title)
        (String.concat "; " (List.map (show_edit printer) fix.edits)))
    description.fixes

type examples = Spans of Source.span Description.t list | Nodes of Catalog.description list

let list_examples : Diagnostic.Code.t -> examples = function
  | Lexer code ->
      Spans (List.map Syntax_catalog.Lexing.describe (Syntax_catalog.Lexing.list_examples code))
  | Parser code ->
      Spans (List.map Syntax_catalog.Parsing.describe (Syntax_catalog.Parsing.list_examples code))
  | Resolve code -> Nodes (List.map Catalog.Resolve.describe (Catalog.Resolve.list_examples code))
  | Types code ->
      Nodes
        (List.map Catalog.Typing.describe (Catalog.Typing.list_examples code)
        @ List.map Catalog.Inference.describe (Catalog.Inference.list_examples code))
  | Patterns code ->
      Nodes (List.map Catalog.Patterns.describe (Catalog.Patterns.list_examples code))
  | Usage code -> Nodes (List.map Catalog.Usage.describe (Catalog.Usage.list_examples code))
  | Ownership code ->
      Nodes (List.map Catalog.Ownership.describe (Catalog.Ownership.list_examples code))
  | Capabilities code ->
      Nodes (List.map Catalog.Capabilities.describe (Catalog.Capabilities.list_examples code))
  | Package code -> Nodes (List.map Catalog.Package.describe (Catalog.Package.list_examples code))
  | Prover code -> Nodes (List.map Catalog.Prover.describe (Catalog.Prover.list_examples code))
  | Too_many_diagnostics -> Spans [ Description.describe_hidden ~count:50 ~severity:Error 0 ]

let list_import_examples : Diagnostic.Code.t -> Source.span Description.t list = function
  | Resolve code ->
      List.map Catalog.Resolve.describe_import (Catalog.Resolve.list_import_examples code)
  | _ -> []

let find_family code =
  match String.index_opt (Diagnostic.Code.name code) '.' with
  | Some dot -> String.sub (Diagnostic.Code.name code) 0 dot
  | None -> Diagnostic.Code.name code

let () =
  print_string "# Diagnostics\n";
  let missing = ref [] in
  let family = ref "" in
  List.iter
    (fun code ->
      if find_family code <> !family then begin
        family := find_family code;
        Printf.printf "\n## %s\n" !family
      end;
      let spans, nodes =
        match list_examples code with
        | Spans examples -> (examples @ list_import_examples code, [])
        | Nodes examples -> (list_import_examples code, examples)
      in
      if spans = [] && nodes = [] then missing := Diagnostic.Code.name code :: !missing
      else begin
        Printf.printf "\n### `%s`\n\n" (Diagnostic.Code.name code);
        List.iter (print_description span_printer) spans;
        List.iter (print_description definition_printer) nodes
      end)
    Diagnostic.Code.all;
  print_string "\n## project\n\n";
  List.iter
    (fun problem -> Printf.printf "- %s\n" (Project_catalog.describe problem))
    Project_catalog.examples;
  match List.rev !missing with
  | [] -> ()
  | missing ->
      Printf.printf "\n## Codes without an example\n\n%s\n"
        (String.concat "\n" (List.map (Printf.sprintf "- `%s`") missing))
