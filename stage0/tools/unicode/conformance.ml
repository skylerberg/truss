let data_directory = Sys.argv.(1)
let failures = ref 0

let fail format =
  Printf.ksprintf
    (fun message ->
      incr failures;
      if !failures <= 50 then prerr_endline message)
    format

let read_records name = Ucd.read_records data_directory name

let iter_range text visit =
  let first, last = Ucd.parse_code_point_range text in
  for value = first to last do
    visit value
  done

let check_property ~file ~name ~is_listed has_property =
  let expected = Array.make 0x110000 false in
  List.iter
    (function
      | range :: value :: _ when is_listed value ->
          iter_range range (fun character -> expected.(character) <- true)
      | _ -> ())
    (read_records file);
  for value = 0 to 0x10FFFF do
    if Uchar.is_valid value && has_property (Uchar.of_int value) <> expected.(value) then
      fail "%s: U+%04X: expected %b" name value expected.(value)
  done

let () =
  let core = "DerivedCoreProperties.txt" in
  check_property ~file:core ~name:"XID_Start" ~is_listed:(( = ) "XID_Start") Unicode.is_xid_start;
  check_property ~file:core ~name:"XID_Continue" ~is_listed:(( = ) "XID_Continue")
    Unicode.is_xid_continue;
  check_property ~file:"PropList.txt" ~name:"Bidi_Control" ~is_listed:(( = ) "Bidi_Control")
    Unicode.is_bidi_control;
  check_property ~file:"DerivedGeneralCategory.txt" ~name:"Cc" ~is_listed:(( = ) "Cc")
    Unicode.is_control;
  let read_listed file property =
    let set = Array.make 0x110000 false in
    List.iter
      (function
        | range :: value :: _ when value = property ->
            iter_range range (fun character -> set.(character) <- true)
        | _ -> ())
      (read_records file);
    set
  in
  let ignorable = read_listed core "Default_Ignorable_Code_Point" in
  let selector = read_listed "PropList.txt" "Variation_Selector" in
  let bidi = read_listed "PropList.txt" "Bidi_Control" in
  let control = read_listed "DerivedGeneralCategory.txt" "Cc" in
  for value = 0 to 0x10FFFF do
    if Uchar.is_valid value then begin
      let expected =
        bidi.(value)
        || (control.(value) && value <> 0x09 && value <> 0x0A && value <> 0x0D)
        || (ignorable.(value) && (not selector.(value)) && value <> 0x200C && value <> 0x200D)
      in
      let scalar_value = Uchar.of_int value in
      if Unicode.is_forbidden scalar_value <> expected then
        fail "forbidden: U+%04X: expected %b" value expected;
      if expected && control.(value) && Unicode.find_forbidden_name scalar_value = None then
        fail "forbidden control U+%04X has no name" value
    end
  done;
  if !failures > 0 then begin
    Printf.eprintf "%d failures\n" !failures;
    exit 1
  end
  else Printf.printf "Unicode %s tables conform to the data files\n" Unicode.version
