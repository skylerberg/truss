let data_directory = ref ""
let read_lines name = Ucd.read_lines !data_directory name
let records name = Ucd.records !data_directory name
let code_point = Ucd.code_point
let code_point_range = Ucd.code_point_range
let merge = Ucd.merge

let property_ranges file property =
  records file
  |> List.filter_map (function
    | range :: name :: _ when name = property -> Some (code_point_range range)
    | _ -> None)
  |> merge

let general_category_ranges categories =
  records "DerivedGeneralCategory.txt"
  |> List.filter_map (function
    | range :: category :: _ when List.mem category categories -> Some (code_point_range range)
    | _ -> None)
  |> merge

let contains ranges value =
  List.exists (fun (first, last) -> first <= value && value <= last) ranges

let subtract ranges removed =
  let rec cut (first, last) = function
    | [] -> [ (first, last) ]
    | (removed_first, removed_last) :: rest ->
        if removed_last < first || removed_first > last then cut (first, last) rest
        else
          (if removed_first > first then cut (first, removed_first - 1) rest else [])
          @ if removed_last < last then cut (removed_last + 1, last) rest else []
  in
  merge (List.concat_map (fun range -> cut range removed) ranges)

let output = Buffer.create (1 lsl 20)

let line text =
  Buffer.add_string output text;
  Buffer.add_char output '\n'

let emit_ints name values =
  Buffer.add_string output (Printf.sprintf "let %s = [|" name);
  List.iteri
    (fun index value ->
      if index mod 8 = 0 then Buffer.add_string output "\n ";
      Buffer.add_string output (Printf.sprintf " 0x%X;" value))
    values;
  line "\n|]\n"

let emit_ranges name ranges =
  emit_ints name (List.concat_map (fun (first, last) -> [ first; last ]) ranges)

let emit_strings name values =
  Buffer.add_string output (Printf.sprintf "let %s = [|" name);
  List.iter (fun value -> Buffer.add_string output (Printf.sprintf "\n  %S;" value)) values;
  line "\n|]\n"

let characters =
  lazy
    (records "UnicodeData.txt"
    |> List.map (function
      | value :: name :: _ -> (code_point value, name)
      | _ -> failwith "UnicodeData.txt: unexpected line"))

let unicode_version () =
  match read_lines "DerivedCoreProperties.txt" with
  | first :: _ ->
      let prefix = "# DerivedCoreProperties-" in
      let start = String.length prefix in
      String.sub first start (String.length first - start - String.length ".txt")
  | [] -> failwith "DerivedCoreProperties.txt is empty"

let () =
  data_directory := Sys.argv.(1);
  let characters = Lazy.force characters in
  line (Printf.sprintf "let unicode_version = %S\n" (unicode_version ()));

  emit_ranges "xid_start" (property_ranges "DerivedCoreProperties.txt" "XID_Start");
  emit_ranges "xid_continue" (property_ranges "DerivedCoreProperties.txt" "XID_Continue");

  let bidi_control = property_ranges "PropList.txt" "Bidi_Control" in
  let control = general_category_ranges [ "Cc" ] in
  let ignorable =
    subtract
      (property_ranges "DerivedCoreProperties.txt" "Default_Ignorable_Code_Point")
      ([ (0x200C, 0x200D) ] @ property_ranges "PropList.txt" "Variation_Selector")
  in
  let forbidden =
    merge (bidi_control @ subtract control [ (0x09, 0x0A); (0x0D, 0x0D) ] @ ignorable)
  in
  emit_ranges "forbidden" forbidden;
  emit_ranges "bidi_control" bidi_control;
  emit_ranges "control" control;

  let aliases = records "NameAliases.txt" in
  let alias value kind =
    List.find_map
      (function
        | [ code; name; alias_kind ] when code_point code = value && alias_kind = kind -> Some name
        | _ -> None)
      aliases
  in
  let names =
    List.filter_map
      (fun (value, name) ->
        if not (contains forbidden value) then None
        else
          let name =
            match List.find_map (alias value) [ "correction"; "control"; "figment" ] with
            | Some name -> Some name
            | None -> if name.[0] = '<' then None else Some name
          in
          Option.map (fun name -> (value, name)) name)
      characters
  in
  emit_ints "forbidden_name_keys" (List.map fst names);
  emit_strings "forbidden_name_values" (List.map snd names);

  print_string (Buffer.contents output)
