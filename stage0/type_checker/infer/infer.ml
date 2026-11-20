module Lookups = Lookups

type resolution = Tables.resolution =
  | Local_value of Syntax.id
  | Global of { path : Path.t; instantiation : Types.instantiation }
  | Field_access of { type_ : Types.ty; field : string }
  | Variant_value of { type_ : Types.ty; variant : string }
  | Type_name of Types.ty
  | Value_parameter of Types.parameter
  | Specification_value

type tables = Tables.published = {
  types : Types.ty option array;
  local_types : Types.ty option array;
  resolutions : resolution option array;
  callees : Path.t option array;
}

type checked = Body.checked = {
  form : Core.t;
  tables : tables;
  used_packages : Path.package list;
  places_without_keyword : (Syntax.id * Language.Mode.t) list;
  mode_keywords : Core.mode_keyword list;
}

let check lookups (key : Resolve.Names.key) ~checks_body =
  Compiler_bug.run_while_doing ~stage:"Infer" (Resolve.Names.show_key key) (fun () ->
      try
        Result.bind (Body.check lookups key ~checks_body) (fun (checked : checked) ->
            match Patterns.check lookups key checked.form with
            | [] -> Ok checked
            | diagnostics -> Error diagnostics)
      with Interface.Properties.Recursion_limit message ->
        let names = lookups.interface.names in
        Error
          [
            Diagnostic.make ~code:(Types Recursion_limit)
              (names.read_spans key).((names.read_definition key).id)
              message;
          ])

let check_contract (lookups : Lookups.t) key =
  check lookups key
    ~checks_body:(Resolve.Names.is_constant (lookups.interface.names.read_declaration key).kind)

let check_body (lookups : Lookups.t) key =
  ignore (lookups.read_contract key);
  check lookups key ~checks_body:true

let derive_form = Derived.derive_form
let is_derived_method = Derived.is_derived_method
let show_resolution = Tables.show_resolution

let statement_diverges (tables : tables) =
  State.diverges ~is_never:(fun (value : Syntax.expression) ->
      match tables.types.(value.id) with Some Types.Never -> true | _ -> false)

module For_testing = struct
  let is_written_expression = Form.For_testing.is_written_expression
  let is_written_statement = Form.For_testing.is_written_statement
end
