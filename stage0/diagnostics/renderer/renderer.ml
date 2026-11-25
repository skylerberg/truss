type file_diagnostic =
  | Syntax of Syntax_catalog.Syntax_diagnostic.t
  | Import of Catalog.Resolve.import

type placed = { file : Path.file; base : int; stop : int; spans : Source.Definition_span.t array }
type lookups = { read_placed : Resolve.Names.key -> placed; read_file_text : Path.file -> string }

let raise_bug format = Compiler_bug.raise_bug ~stage:"Renderer" format

let locate_in (placed : placed) origin =
  let (span : Source.Definition_span.t) =
    Source.Definition_span.locate placed.spans (Core_walk.locate_origin origin)
  in
  (placed.base + span.start, placed.base + span.stop)

let render_description lookups key (description : Catalog.description) =
  let home = lookups.read_placed key in
  let text = lazy (lookups.read_file_text home.file) in
  let locate : Catalog.node -> int * int = function
    | Node origin -> locate_in home origin
    | Definition -> (home.base, home.stop)
    | In_definition (other, origin) when other = key -> locate_in home origin
    | In_definition (other, origin) ->
        let placed = lookups.read_placed other in
        if placed.file <> home.file then
          raise_bug "a location in %s, outside the file of %s" (Resolve.Names.show_key other)
            (Resolve.Names.show_key key)
        else locate_in placed origin
  in
  let read_quoted : Catalog.node -> Description.quoted = function
    | In_definition (other, origin) when other <> key ->
        let placed = lookups.read_placed other in
        let start, stop = locate_in placed origin in
        { source_text = lookups.read_file_text placed.file; start; stop }
    | node ->
        let start, stop = locate node in
        { source_text = Lazy.force text; start; stop }
  in
  Description.render_with { text; locate; read_quoted; make_span = Source.make_span } description

let render lookups key diagnostic = render_description lookups key (Catalog.describe diagnostic)

let locate lookups key origin =
  let start, stop = locate_in (lookups.read_placed key) origin in
  Source.make_span start stop

let describe_file_diagnostic = function
  | Syntax diagnostic -> Syntax_catalog.Syntax_diagnostic.describe diagnostic
  | Import import -> Catalog.Resolve_description.describe_import import

let render_file_diagnostic ~text diagnostic =
  Description.render_file ~text (describe_file_diagnostic diagnostic)
