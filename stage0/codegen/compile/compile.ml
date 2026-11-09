module Names = Resolve.Names

type t = {
  database : Query.database;
  context : Lower.context;
  toolchain : Toolchain.t;
  cache : Build.cache;
  settings : Build.settings;
  mutable done_ : (Instance.key * Lir.t) list;
}

let create database target toolchain cache settings =
  { database; context = Lower.context database target; toolchain; cache; settings; done_ = [] }

let environment (instance : Lir.t) n = instance.nested.(n).environment

let make t (key : Instance.key) : Lir.t =
  let glue = t.context.glue in
  let instance =
    match key with
    | Code _ -> (
        try Lower.instance t.context key
        with Invalid_argument message ->
          invalid_arg (message ^ ", lowering " ^ Instance.to_string key))
    | Drop ty -> Glue.drop glue ty
    | Copy ty -> Glue.copy glue ty
    | Debug ty -> Glue.debug glue ty
    | Constant _ | Cursor_next _ | Adapter _ ->
        invalid_arg ("Compile: not built yet: " ^ Instance.to_string key)
  in
  let needs_drop ty = not (Glue.trivial glue ty) in
  let elaborate f =
    Drops.elaborate t.context.env ~needs_drop ~environment:(environment instance) f
  in
  Lir.canonical_instance
    { instance with main = elaborate instance.main; nested = Array.map elaborate instance.nested }

let lir t key =
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

let run_tests t ~time_limit tests =
  let roots = List.map Lower.test_key tests in
  match Reachable.reachable t.context.env ~lir:(lir t) roots with
  | exception Invalid_argument message -> Error message
  | instances -> (
      let paths = List.sort_uniq Path.compare (List.concat_map anchored instances) in
      let anchors = List.filter_map (anchor t) paths in
      let target = Memory_layout.target t.context.env in
      let sources =
        [
          ("tests", Startup.tests_calling ~time_limit (List.map Instance.symbol roots));
          ("anchors", Positions.anchors_file target anchors);
        ]
      in
      let output =
        Filename.concat (Filename.get_temp_dir_name ())
          (Printf.sprintf "truss-tests-%d" (Unix.getpid ()))
      in
      match
        Build.program t.toolchain t.cache t.context.env t.settings
          ~files:(List.map (fun instance -> [ (instance, Emit_c.External) ]) instances)
          ~sources ~output
      with
      | Error message -> Error message
      | Ok () ->
          let status, out, _ = Toolchain.run output [] in
          (try Sys.remove output with Sys_error _ -> ());
          Ok (status, out))
