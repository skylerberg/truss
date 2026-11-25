module Path_table = Hashtbl.Make (Path)

type t = {
  names : Resolve.Names.lookups;
  source : Resolve.Names.source;
  read_source : Path.file -> Source.t;
  places : Resolve.Names.place Path_table.t;
  sources : (Path.file, Source.t) Hashtbl.t;
}

type location = { file : Path.file; line : int; column : int }

let create names ~source ~read_source =
  { names; source; read_source; places = Path_table.create 16; sources = Hashtbl.create 4 }

let read_place positions definition =
  match Path_table.find_opt positions.places definition with
  | Some place -> place
  | None -> (
      match Option.map positions.source.read_place (positions.names.find_key definition) with
      | Some place ->
          Path_table.replace positions.places definition place;
          place
      | None ->
          Compiler_bug.raise_bug ~stage:"Lowering" "%s has no place in a file"
            (Path.show definition))

let read_source positions file =
  match Hashtbl.find_opt positions.sources file with
  | Some source -> source
  | None ->
      let source = positions.read_source file in
      Hashtbl.replace positions.sources file source;
      source

let locate positions definition offset =
  let { Resolve.Names.file; base } = read_place positions definition in
  let line, column = Source.compute_position (read_source positions file) (base + offset) in
  { file; line; column }

let locate_site positions (site : Lowered.site) = locate positions site.definition site.offset
