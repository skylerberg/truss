module Environment = Environment
module Lookups = Lookups
module Elaborator = Elaborator
module Constants = Constants
module Integer_arithmetic = Integer_arithmetic
module Definition = Definition
module Properties = Properties
module Impls = Impls
module Grants = Grants
module Check = Check

type form_origin =
  | Written of Resolve.Names.key
  | Derived of Resolve.Names.key
  | Inherited of Resolve.Names.key

let find_form_origin (lookups : Lookups.t) ~is_derived (path : Path.t) =
  match (lookups.names.find_key path, path) with
  | Some key, _ -> Some (Written key, Types.no_substitution)
  | None, Method { owner = Derived { type_; _ }; _ } when is_derived path ->
      Option.map
        (fun type_key -> (Derived type_key, Types.no_substitution))
        (lookups.names.find_key type_)
  | None, Method { owner = Impl _ | Derived _; _ } ->
      Option.bind (Impls.find_implemented_method lookups path)
        (fun (implemented : Impls.implemented_method) ->
          Option.map
            (fun key -> (Inherited key, implemented.implementation.substitution))
            (lookups.names.find_key implemented.declaration))
  | None, _ -> None
