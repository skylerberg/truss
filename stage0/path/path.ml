type package = { owner : string option; name : string }

let package_parts package = Option.to_list package.owner @ [ package.name ]
let show_package package = String.concat "::" (package_parts package)
let compare_package left right = String.compare (show_package left) (show_package right)

(* A package from one name, or an owner and a name; [None] from any other
   number of names. *)
let package_of_parts = function
  | [ name ] -> Some { owner = None; name }
  | [ owner; name ] -> Some { owner = Some owner; name }
  | _ -> None

let parse_names text =
  let rec names = function
    | [ last ] when last <> "" -> Some [ last ]
    | name :: "" :: rest when name <> "" -> Option.map (fun rest -> name :: rest) (names rest)
    | _ -> None
  in
  names (String.split_on_char ':' text)

let parse_package text = Option.bind (parse_names text) package_of_parts

type module_ = { package : package; modules : string list }

let module_parts module_ = package_parts module_.package @ module_.modules
let show_module module_ = String.concat "::" (module_parts module_)

let split_module ~is_package = function
  | owner :: name :: modules when is_package { owner = Some owner; name } ->
      Some { package = { owner = Some owner; name }; modules }
  | name :: modules when is_package { owner = None; name } ->
      Some { package = { owner = None; name }; modules }
  | _ -> None

type file = { module_ : module_; name : string }

let file_names file = file.module_.modules @ [ file.name ^ ".truss" ]
let show_file file = String.concat "/" (package_parts file.module_.package @ file_names file)

type type_head = { type_name : string; generics : string list }

let show_type_head head =
  match head.generics with
  | [] -> head.type_name
  | generics -> Printf.sprintf "%s[%s]" head.type_name (String.concat ", " generics)

type receiver = Static | Read | Mut | Own

type t =
  | Top of { module_ : module_; name : string }
  | Method of { owner : t; name : string; receiver : receiver }
  | Member_constant of { owner : t; name : string }
  | Impl of { module_ : module_; trait : string; for_type : type_head }
  | Derived of { type_ : t; trait : t }
  | Test of { module_ : module_; name : string }
  | Law_proof of { module_ : module_; trait : string; law : string; for_type : type_head }

let standard_package = { owner = None; name = "standard" }
let standard_module modules = { package = standard_package; modules }
let standard modules name = Top { module_ = standard_module modules; name }

let rec package = function
  | Top { module_; _ } | Impl { module_; _ } | Test { module_; _ } | Law_proof { module_; _ } ->
      module_.package
  | Method { owner; _ } | Member_constant { owner; _ } -> package owner
  | Derived { type_; _ } -> package type_

let show_receiver = function
  | Static -> "no `self`"
  | Read -> "`self`"
  | Mut -> "`mut self`"
  | Own -> "`own self`"

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
      Printf.sprintf "%s::impl %s for %s" (show_module module_) trait (show_type_head for_type)
  | Derived { type_; trait } -> Printf.sprintf "derived %s for %s" (show trait) (show type_)
  | Test { module_; name } -> Printf.sprintf "%s::test %S" (show_module module_) name
  | Law_proof { module_; trait; law; for_type } ->
      Printf.sprintf "%s::proof %s.%s for %s" (show_module module_) trait law
        (show_type_head for_type)

let compare = Stdlib.compare
let equal left right = compare left right = 0

module Ordered = struct
  type nonrec t = t

  let compare = compare
end

module Map = Map.Make (Ordered)
module Set = Set.Make (Ordered)
