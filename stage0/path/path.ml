type module_ = { package : string; modules : string list }

let show_module module_ = String.concat "::" (module_.package :: module_.modules)

type receiver = Static | Read | Mut | Own

type t =
  | Top of { module_ : module_; name : string }
  | Method of { owner : t; name : string; receiver : receiver }
  | Member_constant of { owner : t; name : string }
  | Impl of { module_ : module_; name : string }
  | Derived of { type_ : t; trait : t }
  | Test of { module_ : module_; name : string }
  | Law_proof of { module_ : module_; name : string }

let rec package = function
  | Top { module_; _ } | Impl { module_; _ } | Test { module_; _ } | Law_proof { module_; _ } ->
      module_.package
  | Method { owner; _ } | Member_constant { owner; _ } -> package owner
  | Derived { type_; _ } -> package type_

let rec show = function
  | Top { module_; name } -> show_module module_ ^ "::" ^ name
  | Method { owner; name; receiver } -> (
      let base = show owner ^ "." ^ name in
      match receiver with
      | Static | Read -> base
      | Mut -> base ^ "(mut self)"
      | Own -> base ^ "(own self)")
  | Member_constant { owner; name } -> show owner ^ "." ^ name
  | Impl { module_; name } -> Printf.sprintf "%s::impl %s" (show_module module_) name
  | Derived { type_; trait } -> Printf.sprintf "derived %s for %s" (show trait) (show type_)
  | Test { module_; name } -> Printf.sprintf "%s::test %S" (show_module module_) name
  | Law_proof { module_; name } -> Printf.sprintf "%s::proof %s" (show_module module_) name

let compare = Stdlib.compare
let equal left right = compare left right = 0
