type entry = { name : string; version : Version.t; hash : string; holds : string list }
type t = entry list

exception Malformed of int * string

let malformed line format =
  Printf.ksprintf (fun message -> raise (Malformed (line, message))) format

let header = "format 1"
let sorted entries = List.sort (fun left right -> String.compare left.name right.name) entries
let find entries name = List.find_opt (fun entry -> entry.name = name) entries

let entry_of_line line text =
  let words = List.filter (( <> ) "") (String.split_on_char ' ' text) in
  match words with
  | name :: version :: hash :: rest ->
      (match Manifest.name_parts name with
      | Some [ _; _ ] -> ()
      | _ ->
          malformed line
            "`%s` is not a registry package's name, which is an owner and a name joined by `::`."
            name);
      let version =
        match Version.parse version with
        | Some ((major, _, _) as version) when major = Version.major_of_name name -> version
        | Some _ ->
            malformed line
              "A version of `%s` starts with %d, the number at the end of its name, or 1 for a \
               name without one."
              name (Version.major_of_name name)
        | None ->
            malformed line "`%s` is not a version, which is three numbers, such as 1.4.2." version
      in
      if not (Content.is_hash hash) then
        malformed line "`%s` is not a hash, which is 64 hexadecimal digits." hash;
      let holds =
        match rest with
        | [] -> []
        | "holds" :: (_ :: _ as capabilities) ->
            List.map
              (fun capability ->
                let length = String.length capability in
                if length > 0 && capability.[length - 1] = ',' then
                  String.sub capability 0 (length - 1)
                else capability)
              capabilities
        | _ ->
            malformed line
              "After a package's hash comes nothing, or `holds` and the capabilities it holds."
      in
      { name; version; hash; holds }
  | _ -> malformed line "A line is a package's name, its version, and its hash."

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
        List.map (fun (line, text) -> (line, entry_of_line line (String.trim text))) rest
      in
      ignore
        (List.fold_left
           (fun seen (line, entry) ->
             if List.mem entry.name seen then
               malformed line "`%s` already has a line above." entry.name;
             entry.name :: seen)
           [] entries);
      sorted (List.map snd entries)
  | (line, _) :: _ -> malformed line "A lock file starts with the line `%s`." header

let print entries =
  String.concat ""
    ((header ^ "\n")
    :: List.map
         (fun entry ->
           Printf.sprintf "%s %s %s%s\n" entry.name (Version.show entry.version) entry.hash
             (match entry.holds with
             | [] -> ""
             | holds -> " holds " ^ String.concat ", " (List.sort String.compare holds)))
         (sorted entries))
