type entry = {
  name : Path.package;
  version : Version.t;
  hash : string;
  holds : Grant.capability list;
}

type t = entry list

exception Malformed of { line : int; problem : Project_catalog.lock_problem }

let raise_malformed line problem = raise (Malformed { line; problem })
let header = "format 1"

let sort_entries entries =
  List.sort (fun left right -> Path.compare_package left.name right.name) entries

let find entries name = List.find_opt (fun entry -> entry.name = name) entries

let parse_entry line text =
  let words = List.filter (( <> ) "") (String.split_on_char ' ' text) in
  match words with
  | written :: version :: hash :: rest ->
      let name =
        match Manifest.parse_name written with
        | Some ({ owner = Some _; _ } as name) -> name
        | _ -> raise_malformed line (Not_a_registry_name written)
      in
      let version =
        match Version.parse version with
        | Some ((major, _, _) as version) when major = Version.parse_major name -> version
        | Some _ ->
            raise_malformed line
              (Version_major_mismatch { written; major = Version.parse_major name })
        | None -> raise_malformed line (Not_a_version version)
      in
      if not (Content.is_hash hash) then raise_malformed line (Not_a_hash hash);
      let holds =
        match rest with
        | [] -> []
        | "holds" :: (_ :: _ as words) ->
            List.sort_uniq Grant.compare_capability
              (List.map
                 (fun item ->
                   let written = String.trim item in
                   match Grant.parse_capability written with
                   | Some capability -> capability
                   | None -> raise_malformed line (Not_a_capability written))
                 (String.split_on_char ',' (String.concat " " words)))
        | _ -> raise_malformed line Unexpected_after_hash
      in
      { name; version; hash; holds }
  | _ -> raise_malformed line Malformed_line

let parse text =
  let lines =
    List.filter
      (fun (_, line) -> String.trim line <> "")
      (List.mapi (fun index line -> (index + 1, line)) (String.split_on_char '\n' text))
  in
  match lines with
  | [] -> []
  | (_, first) :: rest when String.trim first = header ->
      let entries =
        List.map (fun (line, text) -> (line, parse_entry line (String.trim text))) rest
      in
      ignore
        (List.fold_left
           (fun seen (line, entry) ->
             if List.mem entry.name seen then raise_malformed line (Repeated_line entry.name);
             entry.name :: seen)
           [] entries);
      sort_entries (List.map snd entries)
  | (line, _) :: _ -> raise_malformed line (Missing_header header)

let print entries =
  String.concat ""
    ((header ^ "\n")
    :: List.map
         (fun entry ->
           Printf.sprintf "%s %s %s%s\n" (Path.show_package entry.name) (Version.show entry.version)
             entry.hash
             (match entry.holds with
             | [] -> ""
             | holds ->
                 " holds "
                 ^ String.concat ", "
                     (List.map Grant.show_capability
                        (List.sort_uniq Grant.compare_capability holds))))
         (sort_entries entries))
