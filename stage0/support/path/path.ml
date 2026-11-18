type package = { owner : string option; name : string }

let list_package_parts package = Option.to_list package.owner @ [ package.name ]
let show_package package = String.concat "::" (list_package_parts package)
let compare_package left right = String.compare (show_package left) (show_package right)

let parse_package_parts = function
  | [ name ] -> Some { owner = None; name }
  | [ owner; name ] -> Some { owner = Some owner; name }
  | _ -> None

let parse_names text =
  let rec split_names = function
    | [ last ] when last <> "" -> Some [ last ]
    | name :: "" :: rest when name <> "" -> Option.map (fun rest -> name :: rest) (split_names rest)
    | _ -> None
  in
  split_names (String.split_on_char ':' text)

let parse_package text = Option.bind (parse_names text) parse_package_parts

type module_ = { package : package; modules : string list }

let list_module_parts module_ = list_package_parts module_.package @ module_.modules
let show_module module_ = String.concat "::" (list_module_parts module_)

let split_module ~is_package = function
  | owner :: name :: modules when is_package { owner = Some owner; name } ->
      Some { package = { owner = Some owner; name }; modules }
  | name :: modules when is_package { owner = None; name } ->
      Some { package = { owner = None; name }; modules }
  | _ -> None

type file = { module_ : module_; name : string }

let list_file_names file = file.module_.modules @ [ file.name ^ ".truss" ]

let show_file file =
  String.concat "/" (list_package_parts file.module_.package @ list_file_names file)

type receiver = Static | Read | Mut | Own

type t =
  | Top of { module_ : module_; name : string }
  | Method of { owner : t; name : string; receiver : receiver }
  | Member_constant of { owner : t; name : string }
  | Impl of { module_ : module_; trait : reference; for_type : t }
  | Derived of { type_ : t; trait : t }
  | Test of { module_ : module_; name : string }
  | Law_proof of { module_ : module_; trait : reference; law : string; for_type : t }
  | Unresolved of { file : file; names : string list }

and reference = { path : t; arguments : argument list; associated : (string * argument) list }

and argument =
  | Named of reference
  | Parameter of string
  | Any of reference
  | Count of Z.t
  | Constant of t

let standard_package = { owner = None; name = "standard" }
let make_standard_module modules = { package = standard_package; modules }
let make_standard_path modules name = Top { module_ = make_standard_module modules; name }
let make_capability_method capability name = Method { owner = capability; name; receiver = Static }

let is_entry_point = function
  | Top { module_ = { modules = []; _ }; name = "main" } -> true
  | _ -> false

let rec locate_package = function
  | Top { module_; _ } | Impl { module_; _ } | Test { module_; _ } | Law_proof { module_; _ } ->
      module_.package
  | Method { owner; _ } | Member_constant { owner; _ } -> locate_package owner
  | Derived { type_; _ } -> locate_package type_
  | Unresolved { file; _ } -> file.module_.package

let rec is_resolved = function
  | Top _ | Test _ -> true
  | Method { owner; _ } | Member_constant { owner; _ } -> is_resolved owner
  | Impl { trait; for_type; _ } | Law_proof { trait; for_type; _ } ->
      is_resolved_reference trait && is_resolved for_type
  | Derived { type_; trait } -> is_resolved type_ && is_resolved trait
  | Unresolved _ -> false

and is_resolved_reference { path; arguments; associated } =
  is_resolved path
  && List.for_all is_resolved_argument arguments
  && List.for_all (fun (_, argument) -> is_resolved_argument argument) associated

and is_resolved_argument = function
  | Named reference | Any reference -> is_resolved_reference reference
  | Constant path -> is_resolved path
  | Parameter _ | Count _ -> true

let show_receiver = function
  | Static -> "no `self`"
  | Read -> "`self`"
  | Mut -> "`mut self`"
  | Own -> "`own self`"

let rec show_name = function
  | Top { name; _ } | Test { name; _ } -> name
  | Impl { trait; for_type; _ } -> show_name trait.path ^ " for " ^ show_name for_type
  | Law_proof { trait; law; for_type; _ } ->
      show_name trait.path ^ "." ^ law ^ " for " ^ show_name for_type
  | Unresolved { names; _ } -> String.concat "::" names
  | Method { name; _ } | Member_constant { name; _ } -> name
  | Derived { trait; _ } -> show_name trait

let rec show = function
  | Top { module_; name } -> show_module module_ ^ "::" ^ name
  | Method { owner; name; receiver } -> (
      let base = show owner ^ "." ^ name in
      match receiver with
      | Static | Read -> base
      | Mut -> base ^ "(mut self)"
      | Own -> base ^ "(own self)")
  | Member_constant { owner; name } -> show owner ^ "." ^ name
  | Impl { module_; trait; for_type } ->
      Printf.sprintf "%s::impl %s for %s" (show_module module_) (show_reference trait)
        (show for_type)
  | Derived { type_; trait } -> Printf.sprintf "derived %s for %s" (show trait) (show type_)
  | Test { module_; name } -> Printf.sprintf "%s::test %S" (show_module module_) name
  | Law_proof { module_; trait; law; for_type } ->
      Printf.sprintf "%s::proof %s.%s for %s" (show_module module_) (show_reference trait) law
        (show for_type)
  | Unresolved { names; _ } -> String.concat "::" names

and show_reference { path; arguments; associated } =
  match
    List.map show_argument arguments
    @ List.map (fun (name, argument) -> name ^ " = " ^ show_argument argument) associated
  with
  | [] -> show path
  | shown -> Printf.sprintf "%s[%s]" (show path) (String.concat ", " shown)

and show_argument = function
  | Named reference -> show_reference reference
  | Parameter name -> name
  | Any reference -> "any " ^ show_reference reference
  | Count value -> Z.to_string value
  | Constant path -> show path

module Key = Structural_key.Make (struct
  type nonrec t = t
end)

let compare = Key.compare
let equal = Key.equal
let hash = Key.hash

module Ordered = struct
  type nonrec t = t

  let compare = compare
end

module Map = Map.Make (Ordered)
