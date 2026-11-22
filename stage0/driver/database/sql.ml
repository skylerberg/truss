module Statement_table = Hashtbl.Make (String)

type t = {
  connection : Sqlite3.db;
  statements : Sqlite3.stmt Statement_table.t;
  mutable is_in_transaction : bool;
}

type row = Sqlite3.stmt
type argument = Blob of string | Text of string | Integer of int | Null

exception Failed of string

let raise_failed connection action =
  raise (Failed (Printf.sprintf "%s: %s" action (Sqlite3.errmsg connection)))

let check connection action (code : Sqlite3.Rc.t) =
  match code with OK | DONE | ROW -> () | _ -> raise_failed connection action

let run_script database script =
  check database.connection script (Sqlite3.exec database.connection script)

let wrap connection =
  { connection; statements = Statement_table.create 64; is_in_transaction = false }

let open_memory () =
  let database = wrap (Sqlite3.db_open ~uri:true ":memory:") in
  run_script database
    "PRAGMA temp_store = MEMORY; PRAGMA journal_mode = OFF; PRAGMA synchronous = OFF";
  database

let open_file path =
  let database = wrap (Sqlite3.db_open ~uri:true path) in
  run_script database
    "PRAGMA journal_mode = WAL; PRAGMA synchronous = NORMAL; PRAGMA temp_store = MEMORY; PRAGMA \
     cache_size = -262144";
  database

let encode_uri_path path =
  let buffer = Buffer.create (String.length path + 16) in
  String.iter
    (fun character ->
      match character with
      | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '/' | '.' | '-' | '_' | '~' ->
          Buffer.add_char buffer character
      | _ -> Buffer.add_string buffer (Printf.sprintf "%%%02X" (Char.code character)))
    path;
  Buffer.contents buffer

let open_immutable_file path =
  wrap
    (Sqlite3.db_open ~uri:true ~mode:`READONLY
       (Printf.sprintf "file:%s?immutable=1" (encode_uri_path path)))

let finalize_statements database =
  Statement_table.iter (fun _ statement -> ignore (Sqlite3.finalize statement)) database.statements;
  Statement_table.reset database.statements

let close database =
  finalize_statements database;
  ignore (Sqlite3.db_close database.connection)

let obtain_statement database sql =
  match Statement_table.find_opt database.statements sql with
  | Some statement -> statement
  | None ->
      let statement =
        try Sqlite3.prepare database.connection sql
        with Sqlite3.Error message | Sqlite3.SqliteError message ->
          raise (Failed (Printf.sprintf "%s: %s" sql message))
      in
      Statement_table.replace database.statements sql statement;
      statement

let bind database sql statement arguments =
  List.iteri
    (fun index argument ->
      check database.connection sql
        (match argument with
        | Blob bytes -> Sqlite3.bind_blob statement (index + 1) bytes
        | Text text -> Sqlite3.bind_text statement (index + 1) text
        | Integer value -> Sqlite3.bind_int statement (index + 1) value
        | Null -> Sqlite3.bind statement (index + 1) Sqlite3.Data.NULL))
    arguments

let observer : (string -> unit) ref = ref ignore

let with_observer observe run =
  let previous = !observer in
  observer := observe;
  Fun.protect ~finally:(fun () -> observer := previous) run

let with_statement database sql arguments step_through =
  !observer sql;
  let statement = obtain_statement database sql in
  Fun.protect
    ~finally:(fun () -> ignore (Sqlite3.reset statement))
    (fun () ->
      bind database sql statement arguments;
      step_through statement)

let run database sql arguments =
  with_statement database sql arguments (fun statement ->
      let rec step () =
        match Sqlite3.step statement with
        | ROW -> step ()
        | DONE -> ()
        | _ -> raise_failed database.connection sql
      in
      step ())

let list_rows database sql arguments read =
  with_statement database sql arguments (fun statement ->
      let rec step rows =
        match Sqlite3.step statement with
        | ROW -> step (read statement :: rows)
        | DONE -> List.rev rows
        | _ -> raise_failed database.connection sql
      in
      step [])

let find_row database sql arguments read =
  with_statement database sql arguments (fun statement ->
      match Sqlite3.step statement with
      | ROW -> Some (read statement)
      | DONE -> None
      | _ -> raise_failed database.connection sql)

let count_changes database = Sqlite3.changes database.connection
let has_row database sql arguments = Option.is_some (find_row database sql arguments ignore)
let read_blob = Sqlite3.column_blob
let read_text = Sqlite3.column_text
let read_integer = Sqlite3.column_int
let is_null = Sqlite3.column_is_null

let read_cell row index =
  match Sqlite3.column row index with
  | NULL | NONE -> Null
  | INT value -> Integer (Int64.to_int value)
  | TEXT text -> Text text
  | BLOB bytes -> Blob bytes
  | FLOAT _ -> raise (Failed "a column of the code database holds a float")

let begin_transaction database =
  if not database.is_in_transaction then begin
    run_script database "BEGIN";
    database.is_in_transaction <- true
  end

let commit_transaction database =
  if database.is_in_transaction then begin
    run_script database "COMMIT";
    database.is_in_transaction <- false
  end

let checkpoint database = run_script database "PRAGMA wal_checkpoint(TRUNCATE)"

let roll_back_transaction database =
  if database.is_in_transaction then begin
    run_script database "ROLLBACK";
    database.is_in_transaction <- false
  end

let run_outside_transaction database work =
  let was_in_transaction = database.is_in_transaction in
  commit_transaction database;
  finalize_statements database;
  work ();
  if was_in_transaction then begin_transaction database

let attach database ~schema name =
  run_outside_transaction database (fun () ->
      run database (Printf.sprintf "ATTACH DATABASE ?1 AS %s" schema) [ Text name ];
      finalize_statements database)

let attach_immutable_file database ~schema path =
  attach database ~schema (Printf.sprintf "file:%s?immutable=1" (encode_uri_path path));
  run_script database (Printf.sprintf "PRAGMA %s.mmap_size = 1073741824" schema)

let detach database ~schema =
  run_outside_transaction database (fun () ->
      run_script database (Printf.sprintf "DETACH DATABASE %s" schema))

let copy_into ~source ~schema target =
  let was_in_transaction = source.is_in_transaction in
  commit_transaction source;
  let backup =
    Sqlite3.Backup.init ~dst:target.connection ~dst_name:schema ~src:source.connection
      ~src_name:"main"
  in
  let code = Sqlite3.Backup.step backup (-1) in
  let finished = Sqlite3.Backup.finish backup in
  if was_in_transaction then begin_transaction source;
  check target.connection "copy a database" code;
  check target.connection "copy a database" finished
