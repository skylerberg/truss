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
  | Encode ty -> code (Glue.encode glue ty)
  | Any_drop ty -> code (Glue.any_drop glue ty)
  | Evaluator path -> code (Lower.evaluator t.context path)
  | Template_check { from_template; texts } ->
      code (Lower.template_check t.context key ~from_template ~texts)
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

(* Builds what the roots reach into a program at [output], with the given
   startup code. *)
let build t ~roots ~startup ~output =
  match Reachable.reachable t.context.env ~lookup:(compiled t) roots with
  | exception Invalid_argument message -> Error message
  | units ->
      let code = List.filter_map (function Lir.Code i -> Some i | _ -> None) units in
      let paths = List.sort_uniq Path.compare (List.concat_map anchored code) in
      let anchors = List.filter_map (anchor t) paths in
      let target = Memory_layout.target t.context.env in
      let sources = [ ("startup", startup); ("anchors", Positions.anchors_file target anchors) ] in
      Build.program t.toolchain t.cache t.context.env t.settings
        ~files:(List.map (fun unit -> [ unit ]) units)
        ~sources ~output

(* Builds what the roots reach into a temporary program and runs it with
   [arguments], then removes it. *)
let build_and_run ?input ?time_limit t ~roots ~startup ~arguments =
  let output =
    Filename.concat (Filename.get_temp_dir_name ())
      (Printf.sprintf "truss-%d-%d" (Unix.getpid ()) (Hashtbl.hash roots))
  in
  match build t ~roots ~startup ~output with
  | Error message -> Error message
  | Ok () ->
      let result = Toolchain.run ?input ?time_limit output arguments in
      (try Sys.remove output with Sys_error _ -> ());
      Ok result

(* One test's part of the runner's report: its outcome, and its message
   and its echo output, if any. *)
type record = { outcome : string; message : string option; echo : string option }

let parse_report text =
  let length = String.length text in
  let line_at position =
    match String.index_from_opt text position '\n' with
    | Some stop -> (String.sub text position (stop - position), stop + 1)
    | None -> invalid_arg "Compile: a test report that ends in a line"
  in
  (* A block is its label and length on a line, then that many bytes and a
     newline. *)
  let rec blocks position record =
    if position >= length then (position, record)
    else
      let line, after = line_at position in
      match String.split_on_char ' ' line with
      | [ (("message" | "echo") as label); count ] ->
          let count = int_of_string count in
          let content = String.sub text after count in
          let record =
            if label = "message" then { record with message = Some content }
            else { record with echo = Some content }
          in
          blocks (after + count + 1) record
      | _ -> (position, record)
  in
  let rec records position acc =
    if position >= length then List.rev acc
    else
      let line, after = line_at position in
      match String.split_on_char ' ' line with
      | [ "test"; _; outcome ] ->
          let position, record = blocks after { outcome; message = None; echo = None } in
          records position (record :: acc)
      | _ -> invalid_arg ("Compile: a test report line " ^ line)
  in
  records 0 []

let render_report records =
  let block label = function
    | Some content -> Printf.sprintf "%s %d\n%s\n" label (String.length content) content
    | None -> ""
  in
  String.concat ""
    (List.mapi
       (fun i r ->
         Printf.sprintf "test %d %s\n" i r.outcome ^ block "message" r.message ^ block "echo" r.echo)
       records)

(* The results that are kept: a pass with nothing to show. A failure's
   message and any echo give positions, which the key leaves out so that
   moving code keeps its results, and a time limit or a crash may come from
   the machine, so those tests run again. *)
let keep record = record.outcome = "passed" && record.message = None && record.echo = None

let rec ensure_directory directory =
  if not (Sys.file_exists directory) then begin
    ensure_directory (Filename.dirname directory);
    try Unix.mkdir directory 0o755 with Unix.Unix_error (EEXIST, _, _) -> ()
  end

(* A key, which is a hash's bytes, as a file name. *)
let file_name key =
  String.concat ""
    (List.map (Printf.sprintf "%02x") (List.map Char.code (List.of_seq (String.to_seq key))))

(* What is kept under a key: a test's outcome, or a template check's
   results. *)
let stored_text directory key =
  let path = Filename.concat directory (file_name key) in
  if Sys.file_exists path then Some (In_channel.with_open_bin path In_channel.input_all) else None

(* Writes what is kept under a key, whole or not at all. *)
let store_text directory key text =
  ensure_directory directory;
  let path = Filename.concat directory (file_name key) in
  let temporary = Printf.sprintf "%s.%d" path (Unix.getpid ()) in
  Out_channel.with_open_bin temporary (fun channel -> output_string channel text);
  Sys.rename temporary path

let stored directory key =
  Option.map (fun outcome -> { outcome; message = None; echo = None }) (stored_text directory key)

(* Writes a kept result, a pass with nothing to show. *)
let store directory key record = store_text directory key record.outcome

let run_tests ?results t ~time_limit tests =
  let roots = List.map Lower.test_key tests in
  let run roots =
    match
      build_and_run t ~roots
        ~startup:(Startup.tests_calling ~time_limit (List.map Instance.symbol roots))
        ~arguments:[]
    with
    | Error message -> Error message
    | Ok (status, out, _) -> Ok (status, out)
  in
  match results with
  | None -> run roots
  | Some directory -> (
      (* Each test's result is kept under its key, which changes with any
         code it can run, and a test is run again only when it changes. *)
      match
        List.map
          (fun root -> (root, Reachable.test_key t.context.env ~lookup:(compiled t) root))
          roots
      with
      | exception Invalid_argument message -> Error message
      | keyed -> (
          let known = List.map (fun (root, key) -> (root, key, stored directory key)) keyed in
          let missing =
            List.filter_map
              (fun (root, key, r) -> if r = None then Some (root, key) else None)
              known
          in
          let fresh =
            if missing = [] then Ok []
            else
              match run (List.map fst missing) with
              | Error message -> Error message
              | Ok (_, out) -> (
                  match parse_report out with
                  | records when List.length records = List.length missing ->
                      List.iter2
                        (fun (_, key) record -> if keep record then store directory key record)
                        missing records;
                      Ok records
                  | _ -> Error ("Compile: a test report that is not one record a test:\n" ^ out))
          in
          match fresh with
          | Error message -> Error message
          | Ok fresh ->
              let rest = ref fresh in
              let records =
                List.map
                  (fun (_, _, record) ->
                    match record with
                    | Some r -> r
                    | None -> (
                        match !rest with
                        | r :: more ->
                            rest := more;
                            r
                        | [] -> invalid_arg "Compile: fewer results than tests"))
                  known
              in
              let status = if List.for_all (fun r -> r.outcome = "passed") records then 0 else 1 in
              Ok (status, render_report records)))

let run_program ?input t ~main ~arguments =
  let root = Instance.Program_main main in
  build_and_run ?input t ~roots:[ root ]
    ~startup:(Startup.program_calling (Instance.symbol root))
    ~arguments

let build_program t ~main ~output =
  let root = Instance.Program_main main in
  build t ~roots:[ root ] ~startup:(Startup.program_calling (Instance.symbol root)) ~output

(* A value read back from its binary form, as [Glue.encode] writes it, as
   static data. *)
let decode t ty text : Lir.static_value =
  let env = t.context.env in
  let monomorphic = t.context.monomorphic in
  let target = Memory_layout.target env in
  let at = ref 0 in
  let take n =
    if !at + n > String.length text then
      invalid_arg "Compile: a value written out while compiling ends early";
    let part = String.sub text !at n in
    at := !at + n;
    part
  in
  let unsigned bytes =
    let value = ref Z.zero in
    for i = String.length bytes - 1 downto 0 do
      value := Z.add (Z.shift_left !value 8) (Z.of_int (Char.code bytes.[i]))
    done;
    !value
  in
  let integer (kind : Memory_layout.integer) =
    let size = Memory_layout.integer_size target kind in
    let value = unsigned (take size) in
    match kind with
    | Int8 | Int16 | Int32 | Int64 | ISize ->
        if Z.testbit value ((8 * size) - 1) then Z.sub value (Z.shift_left Z.one (8 * size))
        else value
    | _ -> value
  in
  let rec value ty : Lir.static_value =
    if (Memory_layout.of_type env ty).size = 0 then empty ty
    else
      match Monomorphic.kind monomorphic ty with
      | Handle -> invalid_arg "Compile: a handle worked out while compiling"
      | Storage element ->
          let count = Z.to_int (integer USize) in
          Static_storage
            { element; elements = List.init count (fun _ -> value element); owned = true }
      | Shape (Scalar scalar) -> Static_scalar (scalar_value scalar)
      | Shape (Record members) -> Static_record (fields members)
      | Shape (Array (element, count)) -> Static_array (List.init count (fun _ -> value element))
      | Shape (Sum variants) ->
          let index = Z.to_int (unsigned (take 4)) in
          let variant = List.nth variants index in
          Static_variant (variant.name, fields variant.fields)
  and fields members =
    List.map
      (fun (name, (member : Memory_layout.member)) ->
        match member with
        | Typed field_ty -> (name, value field_ty)
        | Raw _ -> invalid_arg "Compile: a raw field worked out while compiling")
      members
  and scalar_value (scalar : Memory_layout.scalar) : Lir.constant =
    match scalar with
    | Integer kind -> Integer (kind, integer kind)
    | Float32 -> Float32 (Z.to_int32_unsigned (unsigned (take 4)))
    | Float64 -> Float64 (Z.to_int64_unsigned (unsigned (take 8)))
    | Bool -> Bool (unsigned (take 1) <> Z.zero)
    | Character -> Character (Z.to_int (unsigned (take 4)))
    | _ -> invalid_arg "Compile: a pointer worked out while compiling"
  (* A value of zero size, which is written as nothing. *)
  and empty ty : Lir.static_value =
    match Monomorphic.shape monomorphic ty with
    | Record members -> Static_record (List.map (fun (name, m) -> (name, empty_member m)) members)
    | Sum [ variant ] ->
        Static_variant
          (variant.name, List.map (fun (name, m) -> (name, empty_member m)) variant.fields)
    | Array (element, count) -> Static_array (List.init count (fun _ -> empty element))
    | _ -> invalid_arg ("Compile: " ^ Ground.to_string ty ^ " has no one value of zero size")
  and empty_member : Memory_layout.member -> Lir.static_value = function
    | Typed ty -> empty ty
    | Raw _ -> invalid_arg "Compile: a raw field of zero size"
  in
  let result = value ty in
  if !at <> String.length text then
    invalid_arg "Compile: a value written out while compiling has bytes left over";
  result

(* Runs a constant's evaluator and reads back its value. *)
let evaluate t path ty =
  let root = Instance.Evaluator path in
  match
    build_and_run t ~roots:[ root ]
      ~startup:(Startup.evaluator_calling (Instance.symbol root))
      ~arguments:[]
  with
  | Error message -> invalid_arg message
  | Ok (0, output, _) -> decode t ty output
  | Ok (status, _, errors) ->
      invalid_arg
        (Printf.sprintf "Compile: working out %s ended with status %d: %s" (Path.show path) status
           errors)

(* Works out a tagged template's check: each of the tag's [from_template]'s
   clauses that can run, for a template of these literal texts, by its
   position among the clauses, with whether it holds. Results are kept for
   the compiler's run. *)
type template_check = Ran of (int * bool) list | Ran_too_long

let checked_templates : (Instance.key, template_check) Hashtbl.t = Hashtbl.create 8

let check_template ?results t ~time_limit ~from_template ~texts =
  let root = Instance.Template_check { from_template; texts } in
  let run () =
    build_and_run t ~time_limit ~roots:[ root ]
      ~startup:(Startup.evaluator_calling (Instance.symbol root))
      ~arguments:[]
  in
  match Hashtbl.find_opt checked_templates root with
  | Some found -> Ok found
  | None -> (
      match Lower.template_checked t.context from_template with
      | exception Invalid_argument message -> Error message
      | [] -> Ok (Ran [])
      | positions -> (
          (* Results are kept under the key of the code that ran, which its
             texts are part of, so a check runs again only when they or its
             code change. *)
          let key =
            match results with
            | Some directory -> (
                match Reachable.test_key t.context.env ~lookup:(compiled t) root with
                | key -> Some (directory, key)
                | exception Invalid_argument _ -> None)
            | None -> None
          in
          let output =
            match Option.bind key (fun (directory, key) -> stored_text directory key) with
            | Some output -> Ok (0, output, "")
            | None -> run ()
          in
          match output with
          | Error message -> Error message
          | Ok (0, output, _) when String.length output = List.length positions ->
              Option.iter (fun (directory, key) -> store_text directory key output) key;
              let found =
                Ran
                  (List.mapi (fun index position -> (position, output.[index] <> '\000')) positions)
              in
              Hashtbl.replace checked_templates root found;
              Ok found
          | Ok (137, _, _) ->
              (* Killed at its time limit. *)
              Hashtbl.replace checked_templates root Ran_too_long;
              Ok Ran_too_long
          | Ok (status, _, errors) ->
              Error
                (Printf.sprintf "Compile: checking a template of %s ended with status %d: %s"
                   (Path.show from_template) status errors)))

let create ?(checks = true) database target toolchain cache settings =
  let t =
    {
      database;
      context = Lower.context ~checks database target;
      toolchain;
      cache;
      settings;
      done_ = [];
      pulled = [];
    }
  in
  (t.context.cursor_fields :=
     fun yielding -> Yields.cursor_fields t.context.env (fst (pulled t yielding)));
  (t.context.evaluate := fun path ty -> evaluate t path ty);
  t
