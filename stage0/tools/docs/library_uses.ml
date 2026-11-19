type library = { name : string; directory : string; area : string; page : string }
type kind = Value | Type | Constructor | Field | Module | Module_type | Exception | Extension
type item = { kind : kind; path : string list }
type use = { user : string; owner : string; item : item }

module Uses = Set.Make (struct
  type t = use

  let compare = compare
end)

type compilation_unit = { library : string; canonical_path : string list }
type inclusion = { included_path : string list; including_path : string list }

let read_lines path = In_channel.with_open_text path In_channel.input_lines

let read_libraries path =
  List.map
    (fun line ->
      match String.split_on_char ' ' line with
      | [ name; directory; area; page ] -> { name; directory; area; page }
      | _ ->
          failwith
            (Printf.sprintf "%s: expected a name, a directory, an area, and a page in %S" path line))
    (read_lines path)

let find_directory url =
  match String.index_opt url '/' with Some slash -> Some (String.sub url 0 slash) | None -> None

let to_index_kind = function
  | Value -> "Value"
  | Type -> "TypeDecl"
  | Constructor -> "Constructor"
  | Field -> "Field"
  | Module -> "Module"
  | Module_type -> "ModuleType"
  | Exception -> "Exception"
  | Extension -> "ExtensionConstructor"

let is_operator name = match name.[0] with 'a' .. 'z' | 'A' .. 'Z' | '_' -> false | _ -> true
let to_index_name name = if is_operator name then "(" ^ name ^ ")" else name

let read_index path libraries =
  let documented_directories =
    List.filter_map (fun library -> find_directory library.page) libraries
  in
  let index = Hashtbl.create 16384 in
  List.iter
    (fun line ->
      match String.split_on_char '\t' line with
      | kind :: url :: (_ :: _ as names) -> (
          match find_directory url with
          | Some directory when List.mem directory documented_directories -> (
              match Hashtbl.find_opt index (kind, names) with
              | Some other ->
                  failwith
                    (Printf.sprintf "%s: %s and %s document the same %s %s" path other url kind
                       (String.concat "." names))
              | None -> Hashtbl.add index (kind, names) url)
          | Some _ | None -> ())
      | _ -> failwith (Printf.sprintf "%s: expected a kind, a URL, and a path in %S" path line))
    (read_lines path);
  index

let find_url index item =
  Hashtbl.find_opt index (to_index_kind item.kind, List.map to_index_name item.path)

let list_annotation_files build_directory library =
  let object_directory =
    String.concat "/" [ build_directory; library.directory; "." ^ library.name ^ ".objs"; "byte" ]
  in
  Sys.readdir object_directory |> Array.to_list
  |> List.filter (fun file ->
      Filename.check_suffix file ".cmt" || Filename.check_suffix file ".cmti")
  |> List.sort String.compare
  |> List.map (Filename.concat object_directory)

let to_main_module library_name = String.capitalize_ascii library_name
let to_unit_name file = String.capitalize_ascii (Filename.remove_extension (Filename.basename file))

let to_canonical_path library unit_name =
  let main_module = to_main_module library.name in
  let prefix = main_module ^ "__" in
  if String.starts_with ~prefix unit_name then
    let inner_module =
      String.sub unit_name (String.length prefix) (String.length unit_name - String.length prefix)
    in
    if inner_module = "" then [ main_module ] else [ main_module; inner_module ]
  else [ unit_name ]

let add_compilation_unit units library file =
  let unit_name = to_unit_name file in
  match Hashtbl.find_opt units unit_name with
  | Some compilation_unit when compilation_unit.library = library.name -> ()
  | Some compilation_unit ->
      failwith
        (Printf.sprintf "%s is a module of both %s and %s" unit_name compilation_unit.library
           library.name)
  | None ->
      Hashtbl.add units unit_name
        { library = library.name; canonical_path = to_canonical_path library unit_name }

let flatten_path path =
  let rec flatten names (path : Path.t) =
    match path with
    | Pident head -> Some (head, names)
    | Pdot (parent, name) -> flatten (name :: names) parent
    | Papply _ | Pextra_ty _ -> None
  in
  flatten [] path

let find_canonical_path units path =
  match flatten_path path with
  | Some (head, names) when Ident.persistent head -> (
      match Hashtbl.find_opt units (Ident.name head) with
      | Some compilation_unit ->
          Some (compilation_unit.library, compilation_unit.canonical_path @ names)
      | None -> None)
  | Some _ | None -> None

let rec find_module_path (module_expr : Typedtree.module_expr) =
  match module_expr.mod_desc with
  | Tmod_ident (path, _) -> Some path
  | Tmod_constraint (constrained, _, _, _) -> find_module_path constrained
  | _ -> None

let list_included_modules (signature : Typedtree.signature) =
  List.concat_map
    (fun (item : Typedtree.signature_item) ->
      match item.sig_desc with
      | Tsig_include { incl_mod = { mty_desc = Tmty_typeof module_expr; _ }; _ } -> (
          match module_expr.mod_desc with
          | Tmod_structure structure ->
              List.filter_map
                (fun (item : Typedtree.structure_item) ->
                  match item.str_desc with
                  | Tstr_include { incl_mod; _ } -> find_module_path incl_mod
                  | _ -> None)
                structure.str_items
          | _ -> Option.to_list (find_module_path module_expr))
      | _ -> [])
    signature.sig_items

let list_inclusions units library file =
  match (Cmt_format.read_cmt file).cmt_annots with
  | Interface signature ->
      let including_path = (Hashtbl.find units (to_unit_name file)).canonical_path in
      List.filter_map
        (fun path ->
          match find_canonical_path units path with
          | Some (owner, included_path) when owner = library.name ->
              Some { included_path; including_path }
          | Some _ | None -> None)
        (list_included_modules signature)
  | Implementation _ | Packed _ | Partial_implementation _ | Partial_interface _ ->
      failwith (file ^ " holds no complete interface")

let rec find_suffix prefix path =
  match (prefix, path) with
  | [], rest -> Some rest
  | prefix_name :: prefix, path_name :: path when String.equal prefix_name path_name ->
      find_suffix prefix path
  | _ :: _, _ -> None

let to_documented_path inclusions path =
  match
    List.find_map
      (fun inclusion ->
        Option.map
          (fun rest -> inclusion.including_path @ rest)
          (find_suffix inclusion.included_path path))
      inclusions
  with
  | Some documented_path -> documented_path
  | None -> path

let to_extension_kind type_path =
  if Path.same type_path Predef.path_exn then Exception else Extension

let collect_uses units inclusions library files =
  let uses = ref Uses.empty in
  let record ?member kind path =
    match find_canonical_path units path with
    | Some (owner, path) when owner <> library.name ->
        let path = to_documented_path inclusions (path @ Option.to_list member) in
        uses := Uses.add { user = library.name; owner; item = { kind; path } } !uses
    | Some _ | None -> ()
  in
  let record_constructor (constructor : Data_types.constructor_description) =
    let type_path = Data_types.cstr_res_type_path constructor in
    match constructor.cstr_tag with
    | Cstr_extension (path, _) -> record (to_extension_kind type_path) path
    | Cstr_constant _ | Cstr_block _ | Cstr_unboxed ->
        record ~member:constructor.cstr_name Constructor type_path
  in
  let record_field (label : Data_types.label_description) =
    record ~member:label.lbl_name Field (Data_types.lbl_res_type_path label)
  in
  let default = Tast_iterator.default_iterator in
  let iterator =
    {
      default with
      expr =
        (fun iterator expression ->
          (match expression.exp_desc with
          | Texp_ident (path, _, _) -> record Value path
          | Texp_construct (_, constructor, _) -> record_constructor constructor
          | Texp_record { fields; _ } ->
              Array.iter
                (fun (label, (definition : Typedtree.record_label_definition)) ->
                  match definition with Overridden _ -> record_field label | Kept _ -> ())
                fields
          | Texp_field (_, _, label) | Texp_setfield (_, _, label, _) | Texp_atomic_loc (_, _, label)
            ->
              record_field label
          | _ -> ());
          default.expr iterator expression);
      pat =
        (fun (type k) iterator (pattern : k Typedtree.general_pattern) ->
          (match pattern.pat_desc with
          | Tpat_construct (_, constructor, _, _) -> record_constructor constructor
          | Tpat_record (fields, _) -> List.iter (fun (_, label, _) -> record_field label) fields
          | _ -> ());
          default.pat iterator pattern);
      typ =
        (fun iterator core_type ->
          (match core_type.ctyp_desc with
          | Ttyp_constr (path, _, _) -> record Type path
          | Ttyp_open (path, _, _) -> record Module path
          | _ -> ());
          default.typ iterator core_type);
      package_type =
        (fun iterator package ->
          record Module_type package.tpt_path;
          default.package_type iterator package);
      module_expr =
        (fun iterator module_expr ->
          (match module_expr.mod_desc with Tmod_ident (path, _) -> record Module path | _ -> ());
          default.module_expr iterator module_expr);
      module_type =
        (fun iterator module_type ->
          (match module_type.mty_desc with
          | Tmty_ident (path, _) -> record Module_type path
          | Tmty_alias (path, _) -> record Module path
          | _ -> ());
          default.module_type iterator module_type);
      with_constraint =
        (fun iterator with_constraint ->
          (match with_constraint with
          | Twith_module (path, _) | Twith_modsubst (path, _) -> record Module path
          | Twith_type _ | Twith_modtype _ | Twith_typesubst _ | Twith_modtypesubst _ -> ());
          default.with_constraint iterator with_constraint);
      extension_constructor =
        (fun iterator constructor ->
          (match constructor.ext_kind with
          | Text_rebind (path, _) ->
              record (to_extension_kind constructor.ext_type.ext_type_path) path
          | Text_decl _ -> ());
          default.extension_constructor iterator constructor);
      type_extension =
        (fun iterator extension ->
          record Type extension.tyext_path;
          default.type_extension iterator extension);
      open_description =
        (fun iterator description ->
          record Module (fst description.open_expr);
          default.open_description iterator description);
    }
  in
  List.iter
    (fun file ->
      match (Cmt_format.read_cmt file).cmt_annots with
      | Implementation structure -> iterator.structure iterator structure
      | Interface signature -> iterator.signature iterator signature
      | Packed _ | Partial_implementation _ | Partial_interface _ ->
          failwith (file ^ " holds no complete implementation or interface"))
    files;
  !uses

let escape text =
  let buffer = Buffer.create (String.length text) in
  String.iter
    (function
      | '&' -> Buffer.add_string buffer "&amp;"
      | '<' -> Buffer.add_string buffer "&lt;"
      | '>' -> Buffer.add_string buffer "&gt;"
      | '"' -> Buffer.add_string buffer "&quot;"
      | character -> Buffer.add_char buffer character)
    text;
  Buffer.contents buffer

let show_path path =
  String.concat "."
    (List.map (fun name -> if is_operator name then "( " ^ name ^ " )" else name) path)

let strip_main_module owner path =
  match path with
  | root :: (_ :: _ as inner_path) when root = to_main_module owner -> inner_path
  | path -> path

let show_item use = show_path (strip_main_module use.owner use.item.path)

let describe_kind = function
  | Value -> "value"
  | Type -> "type"
  | Constructor -> "constructor"
  | Field -> "field"
  | Module -> "module"
  | Module_type -> "module type"
  | Exception -> "exception"
  | Extension -> "extension constructor"

let show_count count ~singular ~plural =
  Printf.sprintf "%d %s" count (if count = 1 then singular else plural)

let group_uses key uses =
  List.fold_right
    (fun use groups ->
      match groups with
      | (name, group) :: rest when name = key use -> (name, use :: group) :: rest
      | groups -> (key use, [ use ]) :: groups)
    (Uses.elements uses) []

let render_tag ~root ~areas library =
  let area =
    match List.find_index (String.equal library.area) areas with
    | Some area -> area
    | None ->
        failwith (Printf.sprintf "%s is in %s, which is not an area" library.name library.area)
  in
  if library.page = "" then
    Printf.sprintf "<span class=\"library area-%d\">%s</span>" area (escape library.name)
  else
    Printf.sprintf "<a class=\"library area-%d\" href=\"%s%s\">%s</a>" area root
      (escape library.page) (escape library.name)

let render_item ~root ~index use =
  let label = Printf.sprintf "<code>%s</code>" (escape (show_item use)) in
  let title = describe_kind use.item.kind in
  match find_url index use.item with
  | Some url -> Printf.sprintf "<a href=\"%s%s\" title=\"%s\">%s</a>" root (escape url) title label
  | None ->
      Printf.sprintf
        "<span class=\"xref-unresolved\" title=\"%s, not in the documentation\">%s</span>" title
        label

let render_rows ~root ~areas ~index ~libraries groups =
  String.concat ""
    (List.map
       (fun (library_name, group) ->
         let sort_key use =
           let shown = show_item use in
           (String.lowercase_ascii shown, shown, use.item)
         in
         let group = List.sort (fun left right -> compare (sort_key left) (sort_key right)) group in
         Printf.sprintf "<dt>%s</dt><dd>%s</dd>"
           (render_tag ~root ~areas (Hashtbl.find libraries library_name))
           (String.concat "" (List.map (render_item ~root ~index) group)))
       groups)

let render_section ~id ~heading ~summary rows =
  Printf.sprintf "<h2 id=\"%s\"><a href=\"#%s\" class=\"anchor\"></a>%s</h2><p>%s</p>%s" id id
    heading summary
    (if rows = "" then "" else "<dl>" ^ rows ^ "</dl>")

let render_page ~areas ~index ~libraries uses library =
  let depth =
    String.fold_left
      (fun depth character -> if character = '/' then depth + 1 else depth)
      0 library.page
  in
  let root = String.concat "" (List.init depth (fun _ -> "../")) in
  let used = Uses.filter (fun use -> use.user = library.name) uses in
  let used_by = Uses.filter (fun use -> use.owner = library.name) uses in
  let used_groups = group_uses (fun use -> use.owner) used in
  let used_by_groups = group_uses (fun use -> use.user) used_by in
  let used_by_items =
    List.sort_uniq compare (List.map (fun use -> use.item) (Uses.elements used_by))
  in
  let uses_summary =
    if used_groups = [] then "No names from other libraries."
    else
      Printf.sprintf "%s from %s."
        (show_count (Uses.cardinal used) ~singular:"name" ~plural:"names")
        (show_count (List.length used_groups) ~singular:"library" ~plural:"libraries")
  in
  let used_by_summary =
    if used_by_groups = [] then "No names used by other libraries."
    else
      Printf.sprintf "%s used by %s."
        (show_count (List.length used_by_items) ~singular:"name" ~plural:"names")
        (show_count (List.length used_by_groups) ~singular:"library" ~plural:"libraries")
  in
  String.concat ""
    [
      Printf.sprintf "<link rel=\"stylesheet\" href=\"%sarea_colors.css\"/>" root;
      Printf.sprintf "<link rel=\"stylesheet\" href=\"%slibrary_uses.css\"/>" root;
      "<section class=\"library-uses\">";
      render_section ~id:"uses" ~heading:"Uses" ~summary:uses_summary
        (render_rows ~root ~areas ~index ~libraries used_groups);
      render_section ~id:"used-by" ~heading:"Used by" ~summary:used_by_summary
        (render_rows ~root ~areas ~index ~libraries used_by_groups);
      "</section>";
    ]

let () =
  match Sys.argv with
  | [| _; libraries_file; areas_file; index_file; build_directory; output_directory |] ->
      let libraries = read_libraries libraries_file in
      let areas = read_lines areas_file in
      let index = read_index index_file libraries in
      let annotation_files =
        List.map (fun library -> (library, list_annotation_files build_directory library)) libraries
      in
      let units = Hashtbl.create 1024 in
      List.iter
        (fun (library, files) -> List.iter (add_compilation_unit units library) files)
        annotation_files;
      let inclusions =
        List.concat_map
          (fun (library, files) ->
            List.concat_map (list_inclusions units library)
              (List.filter (fun file -> Filename.check_suffix file ".cmti") files))
          annotation_files
      in
      let uses =
        List.fold_left
          (fun uses (library, files) ->
            Uses.union uses (collect_uses units inclusions library files))
          Uses.empty annotation_files
      in
      let libraries_by_name = Hashtbl.create 128 in
      List.iter (fun library -> Hashtbl.add libraries_by_name library.name library) libraries;
      List.iter
        (fun library ->
          if library.page <> "" then
            Out_channel.with_open_text
              (Filename.concat output_directory (library.name ^ ".html"))
              (fun channel ->
                output_string channel
                  (render_page ~areas ~index ~libraries:libraries_by_name uses library)))
        libraries
  | _ ->
      prerr_endline "usage: library_uses LIBRARIES AREAS INDEX BUILD_DIRECTORY OUTPUT_DIRECTORY";
      exit 2
