type library = { name : string; directory : string; area : string; page : string }
type kind = Value | Type | Constructor | Field | Module | Module_type | Exception | Extension
type item = { kind : kind; path : string list }

type user =
  | Library_module of { library : string; module_path : string list }
  | Executable_module of { directory : string; area : string; module_name : string }

type use = { user : user; owner : string; item : item }

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

let read_executables path =
  List.map
    (fun line ->
      match String.split_on_char ' ' line with
      | [ object_directory; area ] -> (object_directory, area)
      | _ ->
          failwith (Printf.sprintf "%s: expected an object directory and an area in %S" path line))
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

let list_annotation_files object_directory =
  let byte_directory = Filename.concat object_directory "byte" in
  Sys.readdir byte_directory |> Array.to_list
  |> List.filter (fun file ->
      Filename.check_suffix file ".cmt" || Filename.check_suffix file ".cmti")
  |> List.sort String.compare
  |> List.map (Filename.concat byte_directory)

let to_main_module library_name = String.capitalize_ascii library_name
let to_unit_name file = String.capitalize_ascii (Filename.remove_extension (Filename.basename file))

let strip_prefix ~prefix name =
  if String.starts_with ~prefix name then
    String.sub name (String.length prefix) (String.length name - String.length prefix)
  else name

let find_text text ~start pattern =
  let text_length = String.length text and pattern_length = String.length pattern in
  let rec matches position offset =
    offset = pattern_length
    || (text.[position + offset] = pattern.[offset] && matches position (offset + 1))
  in
  let rec scan position =
    if position + pattern_length > text_length then None
    else if matches position 0 then Some position
    else scan (position + 1)
  in
  scan start

let rec split_unit_name unit_name =
  match find_text unit_name ~start:0 "__" with
  | Some separator ->
      String.sub unit_name 0 separator
      :: split_unit_name
           (String.sub unit_name (separator + 2) (String.length unit_name - separator - 2))
  | None -> [ unit_name ]

let to_canonical_path library unit_name =
  let main_module = to_main_module library.name in
  let prefix = main_module ^ "__" in
  if String.starts_with ~prefix unit_name then
    main_module
    :: List.filter (fun name -> name <> "") (split_unit_name (strip_prefix ~prefix unit_name))
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

let rec is_module_reexport (module_type : Typedtree.module_type) =
  match module_type.mty_desc with
  | Tmty_alias _ | Tmty_typeof _ -> true
  | Tmty_with (constrained, _) -> is_module_reexport constrained
  | Tmty_ident _ | Tmty_signature _ | Tmty_functor _ -> false

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

let collect_uses units inclusions ~user_library ~user file =
  let uses = ref Uses.empty in
  let is_reexporting = ref false in
  let while_reexporting traverse =
    let was_reexporting = !is_reexporting in
    is_reexporting := true;
    traverse ();
    is_reexporting := was_reexporting
  in
  let record ?member kind path =
    match find_canonical_path units path with
    | Some (owner, _) when !is_reexporting && Some owner = user_library -> ()
    | Some (owner, path) ->
        let path = to_documented_path inclusions (path @ Option.to_list member) in
        uses := Uses.add { user; owner; item = { kind; path } } !uses
    | None -> ()
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
      structure_item =
        (fun iterator item ->
          match item.str_desc with
          | (Tstr_module { mb_expr = module_expr; _ } | Tstr_include { incl_mod = module_expr; _ })
            when Option.is_some (find_module_path module_expr) ->
              while_reexporting (fun () -> default.structure_item iterator item)
          | _ -> default.structure_item iterator item);
      signature_item =
        (fun iterator item ->
          match item.sig_desc with
          | (Tsig_module { md_type = module_type; _ } | Tsig_include { incl_mod = module_type; _ })
            when is_module_reexport module_type ->
              while_reexporting (fun () -> default.signature_item iterator item)
          | _ -> default.signature_item iterator item);
      type_declaration =
        (fun iterator declaration ->
          match (declaration.typ_manifest, declaration.typ_kind) with
          | Some manifest, (Ttype_variant _ | Ttype_record _ | Ttype_open) ->
              while_reexporting (fun () -> iterator.typ iterator manifest);
              default.type_declaration iterator { declaration with typ_manifest = None }
          | Some _, (Ttype_abstract | Ttype_external _) | None, _ ->
              default.type_declaration iterator declaration);
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
              while_reexporting (fun () ->
                  record (to_extension_kind constructor.ext_type.ext_type_path) path)
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
  (match (Cmt_format.read_cmt file).cmt_annots with
  | Implementation structure -> iterator.structure iterator structure
  | Interface signature -> iterator.signature iterator signature
  | Packed _ | Partial_implementation _ | Partial_interface _ ->
      failwith (file ^ " holds no complete implementation or interface"));
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

let show_item owner item = show_path (strip_main_module owner item.path)

let show_user = function
  | Library_module { module_path; _ } -> show_path module_path
  | Executable_module { module_name; _ } -> module_name

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

let sort_by key values =
  List.sort
    (fun left right ->
      let left_key = key left and right_key = key right in
      compare
        (String.lowercase_ascii left_key, left_key)
        (String.lowercase_ascii right_key, right_key))
    values

let group_by_library uses =
  List.fold_right
    (fun (library, owned_item) groups ->
      match groups with
      | (name, owned_items) :: rest when name = library -> (name, owned_item :: owned_items) :: rest
      | groups -> (library, [ owned_item ]) :: groups)
    (List.sort_uniq compare uses) []

let read_area_class areas area =
  match List.find_index (String.equal area) areas with
  | Some index -> Printf.sprintf "area-%d" index
  | None -> failwith (Printf.sprintf "%s is not an area" area)

let render_library_tag ~root ~areas library =
  let area_class = read_area_class areas library.area in
  if library.page = "" then
    Printf.sprintf "<span class=\"tag %s\">%s</span>" area_class (escape library.name)
  else
    Printf.sprintf "<a class=\"tag %s\" href=\"%s%s\">%s</a>" area_class root (escape library.page)
      (escape library.name)

let render_user_tag ~root ~areas ~libraries ~index user =
  let label = escape (show_user user) in
  match user with
  | Library_module { library; module_path } -> (
      let area_class = read_area_class areas (Hashtbl.find libraries library).area in
      let title = "module of the library " ^ escape library in
      match find_url index { kind = Module; path = module_path } with
      | Some url ->
          Printf.sprintf "<a class=\"tag %s\" href=\"%s%s\" title=\"%s\">%s</a>" area_class root
            (escape url) title label
      | None ->
          Printf.sprintf "<span class=\"tag %s\" title=\"%s\">%s</span>" area_class title label)
  | Executable_module { directory; area; _ } ->
      Printf.sprintf "<span class=\"tag %s\" title=\"module of an executable in %s\">%s</span>"
        (read_area_class areas area) (escape directory) label

let render_item ~root ~index (owner, item) =
  let label = Printf.sprintf "<code>%s</code>" (escape (show_item owner item)) in
  let title = describe_kind item.kind in
  match find_url index item with
  | Some url -> Printf.sprintf "<a href=\"%s%s\" title=\"%s\">%s</a>" root (escape url) title label
  | None ->
      Printf.sprintf
        "<span class=\"xref-unresolved\" title=\"%s, not in the documentation\">%s</span>" title
        label

let render_rows ~root ~areas ~index ~libraries groups =
  String.concat ""
    (List.map
       (fun (library_name, owned_items) ->
         Printf.sprintf "<dt>%s</dt><dd>%s</dd>"
           (render_library_tag ~root ~areas (Hashtbl.find libraries library_name))
           (String.concat ""
              (List.map (render_item ~root ~index)
                 (sort_by (fun (owner, item) -> show_item owner item) owned_items))))
       groups)

let render_section ~id ~heading ~summary rows =
  Printf.sprintf "<h2 id=\"%s\"><a href=\"#%s\" class=\"anchor\"></a>%s</h2><p>%s</p>%s" id id
    heading summary
    (if rows = "" then "" else "<dl>" ^ rows ^ "</dl>")

let render_library_sections ~root ~areas ~index ~libraries uses library =
  let used =
    List.filter_map
      (fun use ->
        match use.user with
        | Library_module { library = user; _ } when user = library.name && use.owner <> user ->
            Some (use.owner, (use.owner, use.item))
        | Library_module _ | Executable_module _ -> None)
      (Uses.elements uses)
  in
  let used_by =
    List.filter_map
      (fun use ->
        match use.user with
        | Library_module { library = user; _ } when use.owner = library.name && user <> use.owner ->
            Some (user, (use.owner, use.item))
        | Library_module _ | Executable_module _ -> None)
      (Uses.elements uses)
  in
  let used_groups = group_by_library used in
  let used_by_groups = group_by_library used_by in
  let count_items groups = List.length (List.sort_uniq compare (List.concat_map snd groups)) in
  let uses_summary =
    if used_groups = [] then "No names from other libraries."
    else
      Printf.sprintf "%s from %s."
        (show_count (count_items used_groups) ~singular:"name" ~plural:"names")
        (show_count (List.length used_groups) ~singular:"library" ~plural:"libraries")
  in
  let used_by_summary =
    if used_by_groups = [] then "No names used by other libraries."
    else
      Printf.sprintf "%s used by %s."
        (show_count (count_items used_by_groups) ~singular:"name" ~plural:"names")
        (show_count (List.length used_by_groups) ~singular:"library" ~plural:"libraries")
  in
  String.concat ""
    [
      "<section class=\"library-uses\">";
      render_section ~id:"uses" ~heading:"Uses" ~summary:uses_summary
        (render_rows ~root ~areas ~index ~libraries used_groups);
      render_section ~id:"used-by" ~heading:"Used by" ~summary:used_by_summary
        (render_rows ~root ~areas ~index ~libraries used_by_groups);
      "</section>";
    ]

let render_item_users ~root ~areas ~libraries ~index ~is_inline users =
  let element = if is_inline then "span" else "div" in
  Printf.sprintf "<%s class=\"item-users\"><span class=\"label\">Used by</span>%s</%s>" element
    (String.concat "" (List.map (render_user_tag ~root ~areas ~libraries ~index) users))
    element

let read_unique_position page text pattern =
  match find_text text ~start:0 pattern with
  | Some position when Option.is_none (find_text text ~start:(position + 1) pattern) -> position
  | Some _ -> failwith (Printf.sprintf "%s has %s more than once" page pattern)
  | None -> failwith (Printf.sprintf "%s has no %s" page pattern)

let read_closing_tag page text ~tag_start tag =
  let opening = "<" ^ tag and closing = "</" ^ tag ^ ">" in
  let is_opening position =
    let name_end = position + String.length opening in
    name_end < String.length text && (text.[name_end] = ' ' || text.[name_end] = '>')
  in
  let rec scan position depth =
    match (find_text text ~start:position opening, find_text text ~start:position closing) with
    | Some opening_position, Some closing_position when opening_position < closing_position ->
        scan (opening_position + 1) (if is_opening opening_position then depth + 1 else depth)
    | _, Some closing_position ->
        if depth = 1 then closing_position else scan (closing_position + 1) (depth - 1)
    | _, None -> failwith (Printf.sprintf "%s has no %s after position %d" page closing tag_start)
  in
  scan tag_start 0

let read_item_end page text anchor =
  let id_position = read_unique_position page text (Printf.sprintf "id=\"%s\"" (escape anchor)) in
  let tag_start = String.rindex_from text id_position '<' in
  let tag_name_end = String.index_from text tag_start ' ' in
  match String.sub text (tag_start + 1) (tag_name_end - tag_start - 1) with
  | "div" ->
      let closing_position = read_closing_tag page text ~tag_start "div" in
      (closing_position + String.length "</div>", false)
  | "li" -> (read_closing_tag page text ~tag_start "li", true)
  | tag -> failwith (Printf.sprintf "%s: the element with id %s is a %s" page anchor tag)

let insert_texts text insertions =
  let buffer = Buffer.create (String.length text * 2) in
  let last =
    List.fold_left
      (fun last (position, inserted) ->
        Buffer.add_substring buffer text last (position - last);
        Buffer.add_string buffer inserted;
        position)
      0
      (List.stable_sort (fun (left, _) (right, _) -> compare left right) insertions)
  in
  Buffer.add_substring buffer text last (String.length text - last);
  Buffer.contents buffer

let to_root page =
  let depth =
    String.fold_left (fun depth character -> if character = '/' then depth + 1 else depth) 0 page
  in
  String.concat "" (List.init depth (fun _ -> "../"))

let edit_page ~docs_directory ~root ~areas ~index ~libraries ~section ~item_users page =
  let path = Filename.concat docs_directory page in
  let text = In_channel.with_open_bin path In_channel.input_all in
  let after pattern = read_unique_position page text pattern + String.length pattern in
  let stylesheets =
    Printf.sprintf
      "<link rel=\"stylesheet\" href=\"%sarea_colors.css\"/><link rel=\"stylesheet\" \
       href=\"%slibrary_uses.css\"/>"
      root root
  in
  let section_insertions =
    match section with
    | Some section -> [ (after "<div class=\"odoc-content\">", section) ]
    | None -> []
  in
  let item_insertions =
    List.map
      (fun (anchor, users) ->
        let position, is_inline = read_item_end page text anchor in
        (position, render_item_users ~root ~areas ~libraries ~index ~is_inline users))
      item_users
  in
  let edited =
    insert_texts text
      (((after "odoc.support/odoc.css\"/>", stylesheets) :: section_insertions) @ item_insertions)
  in
  Out_channel.with_open_bin path (fun channel -> output_string channel edited)

let collect_users_by_page index uses =
  let users_by_url = Hashtbl.create 4096 in
  Uses.iter
    (fun use ->
      match find_url index use.item with
      | Some url when String.contains url '#' ->
          Hashtbl.replace users_by_url url
            (use.user :: Option.value ~default:[] (Hashtbl.find_opt users_by_url url))
      | Some _ | None -> ())
    uses;
  let users_by_page = Hashtbl.create 512 in
  Hashtbl.iter
    (fun url users ->
      match String.split_on_char '#' url with
      | [ page; anchor ] ->
          let users = sort_by show_user (List.sort_uniq compare users) in
          Hashtbl.replace users_by_page page
            ((anchor, users) :: Option.value ~default:[] (Hashtbl.find_opt users_by_page page))
      | _ -> failwith (Printf.sprintf "%s has more than one anchor" url))
    users_by_url;
  users_by_page

let to_executable_module file =
  match to_unit_name file with
  | "Dune__exe" -> None
  | unit_name -> Some (strip_prefix ~prefix:"Dune__exe__" unit_name)

let () =
  match Sys.argv with
  | [|
   _; libraries_file; executables_file; areas_file; index_file; build_directory; docs_directory;
  |] ->
      let libraries = read_libraries libraries_file in
      let executables = read_executables executables_file in
      let areas = read_lines areas_file in
      let index = read_index index_file libraries in
      let library_files =
        List.map
          (fun library ->
            ( library,
              list_annotation_files
                (String.concat "/"
                   [ build_directory; library.directory; "." ^ library.name ^ ".objs" ]) ))
          libraries
      in
      let units = Hashtbl.create 1024 in
      List.iter
        (fun (library, files) -> List.iter (add_compilation_unit units library) files)
        library_files;
      let inclusions =
        List.concat_map
          (fun (library, files) ->
            List.concat_map (list_inclusions units library)
              (List.filter (fun file -> Filename.check_suffix file ".cmti") files))
          library_files
      in
      let library_uses =
        List.concat_map
          (fun (library, files) ->
            List.map
              (fun file ->
                let user =
                  Library_module
                    {
                      library = library.name;
                      module_path = to_canonical_path library (to_unit_name file);
                    }
                in
                collect_uses units inclusions ~user_library:(Some library.name) ~user file)
              files)
          library_files
      in
      let executable_uses =
        List.concat_map
          (fun (object_directory, area) ->
            List.filter_map
              (fun file ->
                Option.map
                  (fun module_name ->
                    let user =
                      Executable_module
                        { directory = Filename.dirname object_directory; area; module_name }
                    in
                    collect_uses units inclusions ~user_library:None ~user file)
                  (to_executable_module file))
              (list_annotation_files (Filename.concat build_directory object_directory)))
          executables
      in
      let uses = List.fold_left Uses.union Uses.empty (library_uses @ executable_uses) in
      let libraries_by_name = Hashtbl.create 128 in
      List.iter (fun library -> Hashtbl.add libraries_by_name library.name library) libraries;
      let users_by_page = collect_users_by_page index uses in
      let library_pages = List.filter (fun library -> library.page <> "") libraries in
      let pages =
        List.sort_uniq String.compare
          (List.map (fun library -> library.page) library_pages
          @ Hashtbl.fold (fun page _ pages -> page :: pages) users_by_page [])
      in
      List.iter
        (fun page ->
          let root = to_root page in
          let section =
            Option.map
              (render_library_sections ~root ~areas ~index ~libraries:libraries_by_name uses)
              (List.find_opt (fun library -> library.page = page) library_pages)
          in
          edit_page ~docs_directory ~root ~areas ~index ~libraries:libraries_by_name ~section
            ~item_users:(Option.value ~default:[] (Hashtbl.find_opt users_by_page page))
            page)
        pages
  | _ ->
      prerr_endline
        "usage: library_uses LIBRARIES EXECUTABLES AREAS INDEX BUILD_DIRECTORY DOCS_DIRECTORY";
      exit 2
