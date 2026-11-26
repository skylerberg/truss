let find_bounds (ty : Types.ty) =
  if Types.is_builtin Character ty then Some (Z.zero, Z.of_int 0x10FFFF)
  else Types.find_integer_range ty

let is_numeric (ty : Types.ty) = match ty with Types.Integer -> true | _ -> find_bounds ty <> None

let find_float_format (ty : Types.ty) =
  match Types.find_builtin ty with
  | Some Float32 -> Some (8, 24)
  | Some Float64 -> Some (11, 53)
  | _ -> None

let is_bool ty = Types.is_builtin Bool ty

let make_constructor_symbol (ty : Types.ty) variant =
  Logic.Symbol.Constructor { type_ = ty; variant }

let make_selector_symbol ty variant field = Logic.Symbol.Field { type_ = ty; variant; field }
let is_standard_equal = Well_known.is Equal

let find_visible_type (context : State.context) (ty : Types.ty) =
  match ty with
  | Named { path; arguments } when Types.find_builtin ty = None -> (
      match Tables.Type_table.find_opt context.visible_types ty with
      | Some visible -> visible
      | None ->
          let visible =
            match Interface.Definition.find_interface context.lookups.interface path with
            | Some (Interface.Environment.Type_interface interface)
              when (not interface.opaque)
                   || Path.locate_package path = Path.locate_package context.current ->
                Some (interface, Types.make_substitution interface.type_generics arguments)
            | _ -> None
          in
          Tables.Type_table.replace context.visible_types ty visible;
          visible)
  | _ -> None

let find_constructors context ty =
  match find_visible_type context ty with
  | Some (interface, substitution) -> (
      let list_fields (list : Types.field list) =
        List.sort compare
          (List.map
             (fun (field : Types.field) ->
               (field.field_name, Types.substitute_erased substitution field.field_type))
             list)
      in
      match interface.shape with
      | Record list -> Some [ (None, list_fields list) ]
      | Sum variants ->
          Some
            (List.sort compare
               (List.map
                  (fun (variant : Types.variant) ->
                    ( Some variant.variant_name,
                      match variant.fields with Some list -> list_fields list | None -> [] ))
                  variants))
      | Todo_type | Builtin_type _ -> None)
  | None -> None

let rec declare_sort (context : State.context) (ty : Types.ty) : Logic.sort =
  let ty = Types.erase_views ty in
  if is_numeric ty then Int
  else if is_bool ty then Bool
  else
    match (ty, find_float_format ty) with
    | _, Some (exponent, significand) -> Float (exponent, significand)
    | _ when Types.equal ty Types.unit ->
        if not (Query.has_datatype context.query ty) then
          Query.declare_datatype context.query ty (fun () -> [ (Logic.Symbol.Unit, []) ]);
        Type_sort ty
    | Function function_type, _ -> Function_sort (List.length function_type.inputs)
    | _ -> begin
        (if not (Query.has_datatype context.query ty) then
           match find_constructors context ty with
           | Some shape ->
               Query.declare_datatype context.query ty (fun () ->
                   List.map
                     (fun (variant, fields) ->
                       ( make_constructor_symbol ty variant,
                         List.map
                           (fun (field, field_type) ->
                             (make_selector_symbol ty variant field, declare_sort context field_type))
                           fields ))
                     shape)
           | None -> ());
        Type_sort ty
      end

let rec is_equality_identity context ?(seen = []) (ty : Types.ty) =
  is_numeric ty || is_bool ty || Types.is_builtin Character ty || Types.equal ty Types.unit
  || List.exists (Types.equal ty) seen
  ||
  match (find_visible_type context ty, find_constructors context ty) with
  | Some (interface, _), Some shape ->
      List.exists is_standard_equal interface.derives
      && List.for_all
           (fun (_, fields) ->
             List.for_all
               (fun (_, field_type) -> is_equality_identity context ~seen:(ty :: seen) field_type)
               fields)
           shape
  | _ -> false

let make_in_range ty term =
  match find_bounds ty with
  | Some (low, high) ->
      let in_bounds = Logic.(less_equal (Integer low) term &&& less_equal term (Integer high)) in
      if Types.is_builtin Character ty then
        Logic.(in_bounds &&& not_ (less_equal (int 0xD800) term &&& less_equal term (int 0xDFFF)))
      else in_bounds
  | None -> Logic.Boolean true

let arrive context frame prefix ty =
  let value = Facts.declare_fresh context frame prefix (declare_sort context ty) in
  Facts.assume context frame (make_in_range ty value);
  value

let list_definition_bounds (lookups : Lookups.t) ~(current : Path.t) ~(condition : Types.condition)
    : Interface.Impls.bounds =
  let list_impl_generics path =
    match Interface.Definition.find_impl_interface lookups.interface path with
    | Some interface -> interface.impl_generics
    | None -> []
  in
  let generics =
    match current with
    | Method { owner; _ } -> (
        list_impl_generics owner
        @
        match Interface.Impls.read_signature lookups.interface current with
        | Some signature -> signature.generics
        | None -> [])
    | _ -> (
        match Interface.Impls.read_signature lookups.interface current with
        | Some signature -> signature.generics
        | None -> list_impl_generics current)
  in
  let list_self_bounds (parameter : Types.parameter) =
    match
      if Types.is_self_parameter parameter then
        Interface.Definition.find_trait_interface lookups.interface parameter.owner
      else None
    with
    | Some interface ->
        [
          {
            Types.trait = parameter.owner;
            trait_arguments = Types.list_generic_arguments interface.trait_generics;
            associated = [];
          };
        ]
    | None -> []
  in
  Interface.Impls.add_condition_bounds lookups.interface
    (Interface.Properties.Bounds.close lookups.interface (fun parameter ->
         list_self_bounds parameter @ Types.list_bounds generics parameter))
    condition

let substitute_declared_type (context : State.context) (frame : State.frame) ty =
  (Interface.Impls.normalize context.lookups.interface ~list_bounds:context.bounds)
    (Types.substitute frame.substitution ty)

let substitute_type context frame ty = Types.erase_views (substitute_declared_type context frame ty)

let find_local_type context frame local =
  Option.map (substitute_type context frame) (Locals.find_opt local frame.types)

let find_impl (context : State.context) (trait : Types.trait_reference) (ty : Types.ty) =
  match
    Interface.Impls.resolve_evidence context.lookups.interface Types.no_substitution ~self_type:ty
      ~trait Bound
  with
  | Impl { impl; substitution } | Derived_for_view { viewed = impl; substitution } ->
      Some (impl, substitution)
  | Bound -> None

let select_field context ty variant field term =
  match (term, find_constructors context ty) with
  | Logic.Apply (name, arguments), Some shape when name = make_constructor_symbol ty variant -> (
      let fields = Option.value (List.assoc_opt variant shape) ~default:[] in
      match List.find_index (fun (named, _) -> named = field) fields with
      | Some index when index < List.length arguments -> List.nth arguments index
      | _ -> Logic.Apply (make_selector_symbol ty variant field, [ term ]))
  | _ -> Logic.Apply (make_selector_symbol ty variant field, [ term ])

let replace_field context ty variant field whole new_value =
  match Option.bind (find_constructors context ty) (List.assoc_opt variant) with
  | Some fields ->
      Logic.Apply
        ( make_constructor_symbol ty variant,
          List.map
            (fun (name, _) ->
              if name = field then new_value else select_field context ty variant name whole)
            fields )
  | None -> Facts.raise_unsupported Whole_definition (Fields_of ty)

let find_record_field_type context ty field =
  match find_constructors context ty with
  | Some [ (None, fields) ] -> List.assoc_opt field fields
  | Some _ | None -> None

let rec find_part context ty term = function
  | [] -> Some (ty, term)
  | field :: fields ->
      Option.bind (find_record_field_type context ty field) (fun field_type ->
          find_part context field_type (select_field context ty None field term) fields)

let find_root context (frame : State.frame) : Locals.local -> (Types.ty * Logic.term) option =
  function
  | Core_local Self -> (
      match (frame.self_type, frame.self) with Some ty, Some term -> Some (ty, term) | _ -> None)
  | root -> (
      match (find_local_type context frame root, Locals.find_opt root frame.locals) with
      | Some ty, Some term -> Some (ty, term)
      | _ -> None)

let find_changed_part context frame (part : State.changed_part) =
  Option.bind (find_root context frame part.root) (fun (ty, term) ->
      find_part context ty term part.fields)

let rec replace_part context ty whole fields make_part =
  match fields with
  | [] -> Some (make_part ty whole)
  | field :: fields ->
      Option.bind (find_record_field_type context ty field) (fun field_type ->
          Option.map
            (replace_field context ty None field whole)
            (replace_part context field_type
               (select_field context ty None field whole)
               fields make_part))
