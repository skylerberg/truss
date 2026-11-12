type t = { root : string }

let variable = "TRUSS_REGISTRY"

(* A process that answers for others, as the background process does, is
   told each one's registry, which is not its own environment's. *)
let configured : string option option ref = ref None
let configure directory = configured := Some directory

let current () =
  match match !configured with Some told -> told | None -> Sys.getenv_opt variable with
  | Some root when root <> "" -> Some { root }
  | _ -> None

let at root = { root }
let root registry = registry.root

let package_directory registry name =
  List.fold_left Filename.concat registry.root (Path.package_parts name)

let versions_file registry name = Filename.concat (package_directory registry name) "versions"

let versions registry name =
  match In_channel.with_open_bin (versions_file registry name) In_channel.input_lines with
  | exception Sys_error _ -> []
  | lines ->
      List.filter_map
        (fun line ->
          match List.filter (( <> ) "") (String.split_on_char ' ' (String.trim line)) with
          | [ version; hash ] when Content.is_hash hash ->
              Option.map (fun version -> (version, hash)) (Version.parse version)
          | _ -> None)
        lines

let newest registry name =
  List.fold_left
    (fun newest (version, hash) ->
      match newest with
      | Some (other, _) when Version.compare other version >= 0 -> newest
      | _ -> Some (version, hash))
    None (versions registry name)

let hash_of registry name version =
  List.find_map
    (fun (found, hash) -> if Version.compare found version = 0 then Some hash else None)
    (versions registry name)

let version_directory registry name version =
  Filename.concat (package_directory registry name) (Version.show version)

let write_files directory files =
  List.iter
    (fun (path, bytes) ->
      let path = Filename.concat directory path in
      File_system.make_directory (Filename.dirname path);
      File_system.write path bytes)
    files

let add registry name version files =
  write_files (version_directory registry name version) files;
  Out_channel.with_open_gen [ Open_append; Open_creat; Open_binary ]
    0o644 (versions_file registry name) (fun channel ->
      Printf.fprintf channel "%s %s\n" (Version.show version) (Content.hash files))

let fetch registry ~into name version ~hash =
  let target = Filename.concat into hash in
  if Sys.file_exists target then Ok target
  else
    let files = Content.files ~all:true (version_directory registry name version) in
    if files = [] then
      Error
        (Printf.sprintf "the registry at %s has no `%s` %s" registry.root (Path.show_package name)
           (Version.show version))
    else if Content.hash files <> hash then
      Error
        (Printf.sprintf
           "the files the registry at %s holds as `%s` %s do not have the hash the lock file names"
           registry.root (Path.show_package name) (Version.show version))
    else begin
      (* Written beside itself and renamed, so that a package in the store
         is always whole. *)
      let partial = Printf.sprintf "%s.%d.partial" target (Unix.getpid ()) in
      File_system.remove partial;
      write_files partial files;
      (try Sys.rename partial target with Sys_error _ -> File_system.remove partial);
      if Sys.file_exists target then Ok target else Error (Printf.sprintf "cannot write %s" target)
    end
