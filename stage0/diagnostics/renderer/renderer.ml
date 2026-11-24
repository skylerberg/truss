let raise_bug format = Compiler_bug.raise_bug ~stage:"Renderer" format

let make_definition_source (names : Resolve.Names.lookups) key =
  let spans = lazy (names.read_spans key) and text = lazy (names.read_text key) in
  let locate_origin origin =
    let (span : Source.Definition_span.t) =
      Source.Definition_span.locate (Lazy.force spans) (Core_walk.locate_origin origin)
    in
    (span.start, span.stop)
  in
  (text, locate_origin, fun () -> (names.read_definition key).id)

let render (names : Resolve.Names.lookups) key description =
  let home_text, locate_home, find_definition = make_definition_source names key in
  let locate_definition () =
    let spans = names.read_spans key in
    let (span : Source.Definition_span.t) =
      Source.Definition_span.locate spans (find_definition ())
    in
    (span.start, span.stop)
  in
  let locate : Catalog.node -> int * int = function
    | Node origin -> locate_home origin
    | Definition -> locate_definition ()
    | In_definition (other, origin) when other = key -> locate_home origin
    | In_definition (other, _) ->
        raise_bug "a location in %s, outside %s" (Resolve.Names.show_key other)
          (Resolve.Names.show_key key)
  in
  let read_quoted : Catalog.node -> Description.quoted = function
    | In_definition (other, origin) when other <> key ->
        let text, locate_other, _ = make_definition_source names other in
        let start, stop = locate_other origin in
        { definition_text = Lazy.force text; start; stop }
    | node ->
        let start, stop = locate node in
        { definition_text = Lazy.force home_text; start; stop }
  in
  Description.render_with
    { text = home_text; locate; read_quoted; make_span = Source.Definition_span.make }
    description
