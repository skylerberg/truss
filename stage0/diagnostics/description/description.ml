type 'node range = { covering : 'node list }
type 'node location = At of 'node | Over of 'node range | Before of 'node | After of 'node

type 'node piece =
  | Text of string
  | Quote of 'node
  | Quote_over of 'node range
  | Substituted of {
      clause : 'node;
      replacements : ('node * string) list;
      type_names : (string * string) list;
    }

type 'node boundary = Start of 'node | Stop of 'node

type 'node siblings =
  | Next of 'node range
  | Previous of 'node range
  | Alone of { clause : 'node; is_only_clause : bool }

type 'node edit =
  | Replace of 'node * 'node piece list
  | Insert_before of 'node * 'node piece list
  | Insert_after of 'node * 'node piece list
  | Delete of 'node boundary * 'node boundary
  | Remove_entry of { entry : 'node range; siblings : 'node siblings }
  | Remove_lines of 'node range
  | Add_lines_after of 'node * 'node piece list list
  | Add_line_before of 'node * 'node piece list

type 'node fix = { title : 'node piece list; edits : 'node edit list }

type 'node t = {
  code : Diagnostic.Code.t;
  severity : Diagnostic.severity;
  location : 'node location;
  message : 'node piece list;
  notes : ('node location * 'node piece list) list;
  fixes : 'node fix list;
}

let raise_bug format = Compiler_bug.raise_bug ~stage:"Renderer" format
let is_space character = character = ' ' || character = '\n' || character = '\r' || character = '\t'

let rec skip_spaces_before text position =
  if position > 0 && is_space text.[position - 1] then skip_spaces_before text (position - 1)
  else position

let rec skip_spaces_after text position =
  if position < String.length text && is_space text.[position] then
    skip_spaces_after text (position + 1)
  else position

type quoted = { definition_text : string; start : int; stop : int }

type ('node, 'span) source = {
  text : string Lazy.t;
  locate : 'node -> int * int;
  read_quoted : 'node -> quoted;
  make_span : int -> int -> 'span;
}

let locate_range source ({ covering } : _ range) =
  match List.map source.locate covering with
  | [] -> raise_bug "a range covers no node"
  | (start, stop) :: others ->
      ( List.fold_left (fun start (other, _) -> min start other) start others,
        List.fold_left (fun stop (_, other) -> max stop other) stop others )

let locate_location source : _ location -> int * int = function
  | At node -> source.locate node
  | Over range -> locate_range source range
  | Before node ->
      let start, _ = source.locate node in
      (start, start)
  | After node ->
      let _, stop = source.locate node in
      (stop, stop)

let locate_boundary source : _ boundary -> int = function
  | Start node -> fst (source.locate node)
  | Stop node -> snd (source.locate node)

let is_word_character character =
  character = '_'
  || (character >= 'a' && character <= 'z')
  || (character >= 'A' && character <= 'Z')
  || (character >= '0' && character <= '9')

let rename_types type_names text =
  if type_names = [] then text
  else begin
    let buffer = Buffer.create (String.length text) in
    let length = String.length text in
    let rec scan index =
      if index < length then
        if is_word_character text.[index] then begin
          let stop = ref index in
          while !stop < length && is_word_character text.[!stop] do
            incr stop
          done;
          let word = String.sub text index (!stop - index) in
          Buffer.add_string buffer (Option.value (List.assoc_opt word type_names) ~default:word);
          scan !stop
        end
        else begin
          Buffer.add_char buffer text.[index];
          scan (index + 1)
        end
    in
    scan 0;
    Buffer.contents buffer
  end

let substitute source clause replacements type_names =
  let quoted = source.read_quoted clause in
  let clause_text = String.sub quoted.definition_text quoted.start (quoted.stop - quoted.start) in
  let buffer = Buffer.create (String.length clause_text) in
  let next =
    List.fold_left
      (fun next ((start, stop), replacement) ->
        let start = start - quoted.start and stop = stop - quoted.start in
        if start < next || stop > String.length clause_text then next
        else begin
          Buffer.add_string buffer
            (rename_types type_names (String.sub clause_text next (start - next)));
          Buffer.add_string buffer replacement;
          stop
        end)
      0
      (List.sort_uniq compare
         (List.map
            (fun (node, replacement) ->
              let replaced = source.read_quoted node in
              ((replaced.start, replaced.stop), replacement))
            replacements))
  in
  Buffer.add_string buffer (rename_types type_names (String.drop_first next clause_text));
  Buffer.contents buffer

let render_pieces source pieces =
  String.concat ""
    (List.map
       (function
         | Text text -> text
         | Quote node ->
             let { definition_text; start; stop } = source.read_quoted node in
             if start = stop then raise_bug "a quote of an empty span at %d" start;
             String.sub definition_text start (stop - start)
         | Quote_over range ->
             let start, stop = locate_range source range in
             String.sub (Lazy.force source.text) start (stop - start)
         | Substituted { clause; replacements; type_names } ->
             substitute source clause replacements type_names)
       pieces)

let delete source start stop = Some (Diagnostic.delete (source.make_span start stop))

let remove_clause source clause ~is_only_clause =
  let text = Lazy.force source.text and clause_start, clause_stop = source.locate clause in
  let start = skip_spaces_before text clause_start in
  let brace = skip_spaces_after text clause_stop in
  let is_brace_on_own_line =
    brace < String.length text
    && text.[brace] = '{'
    && String.contains (String.sub text clause_stop (brace - clause_stop)) '\n'
  in
  if is_only_clause && is_brace_on_own_line then
    Some (Diagnostic.replace (source.make_span start brace) " ")
  else delete source start clause_stop

let read_indentation text position =
  let line_start = Source.compute_fragment_line_start text position in
  let indentation_end =
    Option.value ~default:(String.length text)
      (String.find_first_index (Fun.negate Char.Ascii.is_blank) ~start:line_start text)
  in
  String.sub text line_start (indentation_end - line_start)

let add_line_before source node line =
  let text = Lazy.force source.text and start, _ = source.locate node in
  if start > 0 && text.[start - 1] = '\n' then
    Some (Diagnostic.replace (source.make_span start start) ("  " ^ line ^ "\n"))
  else if start > 0 && text.[start - 1] = ' ' then
    Some (Diagnostic.replace (source.make_span (start - 1) start) ("\n  " ^ line ^ "\n"))
  else None

let render_edit source : _ edit -> _ Diagnostic.edit option = function
  | Replace (node, pieces) ->
      let start, stop = source.locate node in
      Some (Diagnostic.replace (source.make_span start stop) (render_pieces source pieces))
  | Insert_before (node, pieces) ->
      let start, _ = source.locate node in
      Some (Diagnostic.insert (source.make_span start start) (render_pieces source pieces))
  | Insert_after (node, pieces) ->
      let _, stop = source.locate node in
      Some (Diagnostic.insert (source.make_span stop stop) (render_pieces source pieces))
  | Delete (start, stop) ->
      delete source (locate_boundary source start) (locate_boundary source stop)
  | Remove_entry { entry; siblings } -> (
      let entry_start, entry_stop = locate_range source entry in
      match siblings with
      | Next next -> delete source entry_start (fst (locate_range source next))
      | Previous previous -> delete source (snd (locate_range source previous)) entry_stop
      | Alone { clause; is_only_clause } -> remove_clause source clause ~is_only_clause)
  | Remove_lines range ->
      let text = Lazy.force source.text and start, stop = locate_range source range in
      let line_start = Source.compute_fragment_line_start text start in
      if line_start > 0 then delete source (line_start - 1) stop
      else
        delete source line_start
          (if stop < String.length text && text.[stop] = '\n' then stop + 1 else stop)
  | Add_lines_after (node, lines) ->
      let text = Lazy.force source.text and start, stop = source.locate node in
      let indentation = read_indentation text start in
      Some
        (Diagnostic.replace (source.make_span stop stop)
           (String.concat ""
              (List.map (fun line -> "\n" ^ indentation ^ render_pieces source line) lines)))
  | Add_line_before (node, line) -> add_line_before source node (render_pieces source line)

let render_fix source (fix : _ fix) =
  let edits = List.map (render_edit source) fix.edits in
  if List.for_all Option.is_some edits then
    Some (Diagnostic.fix (render_pieces source fix.title) (List.filter_map Fun.id edits))
  else None

let render_with source (description : _ t) =
  let start, stop = locate_location source description.location in
  Diagnostic.make ~severity:description.severity
    ~fixes:(List.filter_map (render_fix source) description.fixes)
    ~notes:
      (List.map
         (fun (location, note) ->
           let start, stop = locate_location source location in
           (source.make_span start stop, render_pieces source note))
         description.notes)
    ~code:description.code (source.make_span start stop)
    (render_pieces source description.message)

let render_file ~text (description : Source.span t) =
  let locate (span : Source.span) = (span.start, span.stop) in
  render_with
    {
      text = Lazy.from_val text;
      locate;
      read_quoted =
        (fun span ->
          let start, stop = locate span in
          { definition_text = text; start; stop });
      make_span = Source.make_span;
    }
    description

let shown_limit = 200

let describe_hidden ~count ~severity position : Source.span t =
  {
    code = Too_many_diagnostics;
    severity;
    location = At (Source.make_zero_width position);
    message = [ Text (Printf.sprintf "%d more diagnostics are not shown." count) ];
    notes = [];
    fixes = [];
  }

let render_spans (description : Source.span t) =
  render_with
    {
      text = lazy (raise_bug "a description over spans reads source text");
      locate = (fun (span : Source.span) -> (span.start, span.stop));
      read_quoted = (fun _ -> raise_bug "a description over spans quotes source text");
      make_span = Source.make_span;
    }
    description

let select_shown diagnostics =
  let rec take count last = function
    | [] -> []
    | rest when count = shown_limit ->
        [
          render_spans
            (describe_hidden ~count:(List.length rest)
               ~severity:(if List.exists Diagnostic.is_error rest then Error else Warning)
               last);
        ]
    | (first : Diagnostic.t) :: rest -> first :: take (count + 1) first.span.stop rest
  in
  take 0 0 diagnostics

module For_testing = struct
  let limit = shown_limit
end
