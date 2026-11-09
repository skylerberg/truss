module Names = Resolve.Names

type t = {
  database : Query.database;
  context : Lower.context;
  toolchain : Toolchain.t;
  cache : Build.cache;
  settings : Build.settings;
  mutable done_ : (Instance.key * Lir.compiled) list;
  mutable pulled : (Ground.yielding * (Lir.function_ * Lir.local list)) list;
      (** Each pulled method, with its drops elaborated *)
}

(* A pulled method's version with its drops elaborated, made once. *)
let pulled t yielding =
  match List.find_opt (fun (y, _) -> Ground.equal (Cursor y) (Cursor yielding)) t.pulled with
  | Some (_, made) -> made
  | None ->
      let f, owned = Lower.pulled t.context yielding in
      let glue = t.context.glue in
      let made =
        ( Drops.elaborate t.context.env
            ~needs_drop:(fun ty -> not (Glue.trivial glue ty))
            ~environment:(fun _ -> [])
            f,
          owned )
      in
      t.pulled <- (yielding, made) :: t.pulled;
      made

let create database target toolchain cache settings =
  let t =
    {
      database;
      context = Lower.context database target;
      toolchain;
      cache;
      settings;
      done_ = [];
      pulled = [];
    }
  in
  (t.context.cursor_fields :=
     fun yielding -> Yields.cursor_fields t.context.env (fst (pulled t yielding)));
  t

let environment (instance : Lir.t) n = instance.nested.(n).environment

let make t (key : Instance.key) : Lir.compiled =
  let glue = t.context.glue in
  let code instance =
    let needs_drop ty = not (Glue.trivial glue ty) in
    let elaborate f =
      Drops.elaborate t.context.env ~needs_drop ~environment:(environment instance) f
    in
    Lir.Code
      (Lir.canonical_instance
         {
           instance with
           main = elaborate instance.main;
           nested = Array.map elaborate instance.nested;
         })
  in
  match key with
  | Code _ -> (
      try code (Lower.instance t.context key)
      with Invalid_argument message ->
        invalid_arg (message ^ ", lowering " ^ Instance.to_string key))
  | Constant path -> Data (Lower.constant t.context path)
  | Drop (Cursor yielding as cursor) ->
      let f, owned = pulled t yielding in
      Code
        (Lir.canonical_instance
           { key; main = Yields.cursor_drop t.context.env ~cursor ~owned f; nested = [||] })
  | Cursor_next yielding ->
      let f, _ = pulled t yielding in
      let cursor = Ground.Cursor yielding in
      let result = Lower.cursor_result t.context yielding in
      Code
        (Lir.canonical_instance
           { key; main = Yields.cursor_next t.context.env ~cursor ~result f; nested = [||] })
  | Drop ty -> code (Glue.drop glue ty)
  | Copy ty -> code (Glue.copy glue ty)
  | Debug ty -> code (Glue.debug glue ty)
  | Entry _ | Program_main _ | Any_entry _ | Adapter _ -> code (Lower.instance t.context key)
  | Any_table _ -> Table (Lower.any_table t.context key)
  | Table _ -> Table (Lower.table t.context key)
  | Real_evidence capability -> Evidence (Lower.real_evidence t.context capability)

let compiled t key =
  match List.find_opt (fun (k, _) -> Instance.equal k key) t.done_ with
  | Some (_, instance) -> instance
  | None ->
      let instance = make t key in
      t.done_ <- (key, instance) :: t.done_;
      instance

(* The definitions an instance's positions are relative to. *)
let anchored (instance : Lir.t) =
  let of_function (f : Lir.function_) =
    Array.to_list f.blocks
    |> List.concat_map (fun (b : Lir.basic_block) ->
        List.filter_map
          (function Lir.Echo { site; _ } -> Some site.definition | _ -> None)
          b.statements
        @ match b.terminator with Fail { site; _ } -> [ site.definition ] | _ -> [])
  in
  of_function instance.main @ List.concat_map of_function (Array.to_list instance.nested)

let anchor t (path : Path.t) : Positions.anchor option =
  match Query.demand t.database Interface.Summary.key path with
  | None -> None
  | Some key -> (
      match Query.demand t.database Names.base key with
      | None -> None
      | Some (module_, base) ->
          let file = Query.demand t.database Workspace.file module_ in
          let line, _ = Source.position file.source base in
          Some { definition = path; path = Source.path file.source; first_line = line })

(* Builds what the roots reach into a program with the given startup code,
   and runs it with [arguments]. *)
let build_and_run t ~roots ~startup ~arguments =
  match Reachable.reachable t.context.env ~lookup:(compiled t) roots with
  | exception Invalid_argument message -> Error message
  | units -> (
      let code = List.filter_map (function Lir.Code i -> Some i | _ -> None) units in
      let paths = List.sort_uniq Path.compare (List.concat_map anchored code) in
      let anchors = List.filter_map (anchor t) paths in
      let target = Memory_layout.target t.context.env in
      let sources = [ ("startup", startup); ("anchors", Positions.anchors_file target anchors) ] in
      let output =
        Filename.concat (Filename.get_temp_dir_name ())
          (Printf.sprintf "truss-%d-%d" (Unix.getpid ()) (Hashtbl.hash roots))
      in
      match
        Build.program t.toolchain t.cache t.context.env t.settings
          ~files:(List.map (fun unit -> [ unit ]) units)
          ~sources ~output
      with
      | Error message -> Error message
      | Ok () ->
          let result = Toolchain.run output arguments in
          (try Sys.remove output with Sys_error _ -> ());
          Ok result)

let run_tests t ~time_limit tests =
  let roots = List.map Lower.test_key tests in
  match
    build_and_run t ~roots
      ~startup:(Startup.tests_calling ~time_limit (List.map Instance.symbol roots))
      ~arguments:[]
  with
  | Error message -> Error message
  | Ok (status, out, _) -> Ok (status, out)

let run_program t ~main ~arguments =
  let root = Instance.Program_main main in
  build_and_run t ~roots:[ root ]
    ~startup:(Startup.program_calling (Instance.symbol root))
    ~arguments
