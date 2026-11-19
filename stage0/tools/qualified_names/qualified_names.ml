let operator_modules = [ [ "Logic" ]; [ "Cmdliner"; "Arg" ]; [ "Cmdliner"; "Term" ] ]

let operator_module_names =
  String.concat ", " (List.map (fun path -> "`" ^ String.concat "." path ^ "`") operator_modules)

let is_operator_module (name : Longident.t) =
  match name with Lapply _ -> false | _ -> List.mem (Longident.flatten name) operator_modules

let find_opened_module_name (declaration : Parsetree.open_declaration) =
  match declaration.popen_expr.pmod_desc with Pmod_ident name -> Some name.txt | _ -> None

let open_item = "qualify the names this open brings into scope, and remove it"

let local_open =
  Printf.sprintf
    "qualify the names this open brings into scope; an expression may open only an operator \
     module: %s"
    operator_module_names

let alias = "name the module by its path instead of this alias, and remove it"

let is_export (name : string option) (target : Longident.t) =
  match (name, target) with Some name, Lident target -> name = target | _ -> false

let list_rejected_names path =
  let text = In_channel.with_open_bin path In_channel.input_all in
  let lexbuf = Lexing.from_string text in
  Location.init lexbuf path;
  let rejections = ref [] in
  let reject (location : Location.t) message =
    rejections := (location.loc_start.pos_lnum, message) :: !rejections
  in
  let reject_unless_operator_module location name =
    if not (is_operator_module name) then reject location local_open
  in
  let default = Ast_iterator.default_iterator in
  let iterator =
    {
      default with
      structure_item =
        (fun iterator item ->
          (match item.pstr_desc with
          | Pstr_open _ -> reject item.pstr_loc open_item
          | Pstr_module { pmb_name; pmb_expr = { pmod_desc = Pmod_ident target; _ }; _ }
            when not (is_export pmb_name.txt target.txt) ->
              reject item.pstr_loc alias
          | _ -> ());
          default.structure_item iterator item);
      signature_item =
        (fun iterator item ->
          (match item.psig_desc with
          | Psig_open _ -> reject item.psig_loc open_item
          | Psig_module { pmd_name; pmd_type = { pmty_desc = Pmty_alias target; _ }; _ }
            when not (is_export pmd_name.txt target.txt) ->
              reject item.psig_loc alias
          | _ -> ());
          default.signature_item iterator item);
      expr =
        (fun iterator expression ->
          match expression.pexp_desc with
          | Pexp_struct_item ({ pstr_desc = Pstr_open declaration; _ }, body) ->
              (match find_opened_module_name declaration with
              | Some name -> reject_unless_operator_module expression.pexp_loc name
              | None -> reject expression.pexp_loc local_open);
              iterator.module_expr iterator declaration.popen_expr;
              iterator.expr iterator body
          | Pexp_struct_item
              ( { pstr_desc = Pstr_module { pmb_expr = { pmod_desc = Pmod_ident _; _ }; _ }; _ },
                body ) ->
              reject expression.pexp_loc alias;
              iterator.expr iterator body
          | _ -> default.expr iterator expression);
      pat =
        (fun iterator pattern ->
          (match pattern.ppat_desc with
          | Ppat_open (name, _) -> reject_unless_operator_module pattern.ppat_loc name.txt
          | _ -> ());
          default.pat iterator pattern);
      typ =
        (fun iterator core_type ->
          (match core_type.ptyp_desc with
          | Ptyp_open (name, _) -> reject_unless_operator_module core_type.ptyp_loc name.txt
          | _ -> ());
          default.typ iterator core_type);
      class_expr =
        (fun iterator class_expression ->
          (match class_expression.pcl_desc with
          | Pcl_open _ -> reject class_expression.pcl_loc local_open
          | _ -> ());
          default.class_expr iterator class_expression);
      class_type =
        (fun iterator class_type ->
          (match class_type.pcty_desc with
          | Pcty_open _ -> reject class_type.pcty_loc local_open
          | _ -> ());
          default.class_type iterator class_type);
    }
  in
  (match Filename.extension path with
  | ".ml" -> iterator.structure iterator (Parse.implementation lexbuf)
  | ".mli" -> iterator.signature iterator (Parse.interface lexbuf)
  | _ -> ());
  List.rev !rejections

let () =
  let failures =
    List.concat_map
      (fun path ->
        List.map
          (fun (line, message) -> Printf.sprintf "%s:%d: %s" path line message)
          (list_rejected_names path))
      (List.tl (Array.to_list Sys.argv))
  in
  List.iter print_endline failures;
  if failures <> [] then exit 1
