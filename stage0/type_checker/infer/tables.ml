type local = Syntax.id

type callee =
  | Function of { path : Path.t; instantiation : Types.instantiation }
  | Trait_method of {
      trait : Types.trait_reference;
      name : string;
      receiver : Path.receiver;
      self_type : Types.ty;
      instantiation : Types.instantiation;
    }
  | Capability_method of { capability : Path.t; name : string }
  | Constructor of { type_ : Path.t; variant : string option; type_arguments : Types.argument list }
  | Indirect
  | Intrinsic of { operation : Intrinsic.operation; type_arguments : Types.argument list }

type argument = {
  expression : Syntax.expression;
  core_argument_index : int;
  mode : Language.Mode.t;
}

type call = {
  callee : callee;
  arguments : argument list;
  omitted_defaults : string list;
  callee_result : Types.ty;
}

type resolution =
  | Local_value of local
  | Global of { path : Path.t; instantiation : Types.instantiation }
  | Field_access of { type_ : Types.ty; field : string }
  | Variant_value of { type_ : Types.ty; variant : string }
  | Type_name of Types.ty
  | Value_parameter of Types.parameter
  | Specification_value

let show_resolution = function
  | Local_value local -> Printf.sprintf "local %d" local
  | Global { path; _ } -> Path.show path
  | Field_access { field; _ } -> "field " ^ field
  | Variant_value { variant; _ } -> "variant " ^ variant
  | Type_name type_ -> "type " ^ Types.show type_
  | Value_parameter parameter -> "generic " ^ parameter.name
  | Specification_value -> "specification"

type literal = Integer_value of Z.t | Float_value of float

type loop =
  | Integer_range of { element : Types.ty; inclusive : bool }
  | Elements of { count : call; element : call; lends : Language.Mode.t }
  | Pulled of {
      cursor : Types.ty;
      cursor_call : call option;
      remaining : (Types.condition * call) option;
    }

type pattern =
  | Variant_pattern of {
      type_ : Types.ty;
      variant : string;
      fields : (string * Syntax.pattern) list;
    }
  | Record_pattern of { type_ : Types.ty; fields : (string * Syntax.pattern) list }
  | Binding_pattern of { local : Syntax.id; is_var : bool; mode : Language.Mode.t }
  | Constant_pattern of Path.t
  | Literal_pattern of literal
  | Other_pattern

type template = {
  from_template : call option;
  part_conversions : call option list;
  interpolated : bool;
  part : Types.ty option;
}

type conversion =
  | From_never
  | Owned_to_view
  | View_to_owned
  | Function_widening
  | To_integer
  | From_integer

type specification_call =
  | Specification_function of Core.specification_function
  | Method_cost of {
      metric : Language.Metric.t;
      trait : Types.trait_reference;
      name : string;
      receiver : Path.receiver;
      self_type : Types.ty;
    }

type literal_elements =
  | List_element of Types.ty
  | Map_entry of { key : Types.ty; value : Types.ty }

type published = {
  types : Types.ty option array;
  local_types : Types.ty option array;
  resolutions : resolution option array;
  callees : Path.t option array;
}

type t = {
  types : Types.ty option array;
  local_types : Types.ty option array;
  resolutions : resolution option array;
  calls : call option array;
  literals : literal option array;
  patterns : pattern option array;
  scrutinee_types : Types.ty option array;
  loops : loop option array;
  templates : template option array;
  lend_modes : Language.Mode.t option array;
  conditions : Types.condition option array;
  conversions : (conversion * Types.ty) list array;
  update_paths : (Syntax.id * string list) list option array;
  specification_calls : specification_call option array;
  captures : (Syntax.id * Core.local) list option array;
  literal_elements : literal_elements option array;
  discarded : bool array;
}

let create size =
  {
    types = Array.make size None;
    local_types = Array.make size None;
    resolutions = Array.make size None;
    calls = Array.make size None;
    literals = Array.make size None;
    patterns = Array.make size None;
    scrutinee_types = Array.make size None;
    loops = Array.make size None;
    templates = Array.make size None;
    lend_modes = Array.make size None;
    conditions = Array.make size None;
    conversions = Array.make size [];
    update_paths = Array.make size None;
    specification_calls = Array.make size None;
    captures = Array.make size None;
    literal_elements = Array.make size None;
    discarded = Array.make size false;
  }

let map ~map_type ~map_argument ~map_capabilities (tables : t) : t =
  let map_trait (reference : Types.trait_reference) : Types.trait_reference =
    {
      reference with
      trait_arguments = List.map map_argument reference.trait_arguments;
      associated = List.map (fun (name, type_) -> (name, map_type type_)) reference.associated;
    }
  in
  let map_instantiation (instantiation : Types.instantiation) : Types.instantiation =
    {
      type_arguments = List.map map_argument instantiation.type_arguments;
      capability_arguments =
        List.map
          (fun (name, capabilities) -> (name, map_capabilities capabilities))
          instantiation.capability_arguments;
    }
  in
  let map_call (call : call) : call =
    {
      call with
      callee =
        (match call.callee with
        | Function { path; instantiation } ->
            Function { path; instantiation = map_instantiation instantiation }
        | Trait_method method_ ->
            Trait_method
              {
                method_ with
                trait = map_trait method_.trait;
                self_type = map_type method_.self_type;
                instantiation = map_instantiation method_.instantiation;
              }
        | Constructor constructor ->
            Constructor
              { constructor with type_arguments = List.map map_argument constructor.type_arguments }
        | Intrinsic intrinsic ->
            Intrinsic
              { intrinsic with type_arguments = List.map map_argument intrinsic.type_arguments }
        | (Capability_method _ | Indirect) as callee -> callee);
      callee_result = map_type call.callee_result;
    }
  in
  let map_entries table transform = Array.map (Option.map transform) table in
  {
    types = map_entries tables.types map_type;
    literals = tables.literals;
    lend_modes = tables.lend_modes;
    update_paths = tables.update_paths;
    captures = tables.captures;
    discarded = tables.discarded;
    local_types = map_entries tables.local_types map_type;
    scrutinee_types = map_entries tables.scrutinee_types map_type;
    calls = map_entries tables.calls map_call;
    resolutions =
      map_entries tables.resolutions (function
        | Global { path; instantiation } ->
            Global { path; instantiation = map_instantiation instantiation }
        | Field_access { type_; field } -> Field_access { type_ = map_type type_; field }
        | Variant_value { type_; variant } -> Variant_value { type_ = map_type type_; variant }
        | Type_name type_ -> Type_name (map_type type_)
        | (Local_value _ | Value_parameter _ | Specification_value) as resolution -> resolution);
    loops =
      map_entries tables.loops (function
        | Integer_range { element; inclusive } ->
            Integer_range { element = map_type element; inclusive }
        | Elements { count; element; lends } ->
            Elements { count = map_call count; element = map_call element; lends }
        | Pulled { cursor; cursor_call; remaining } ->
            Pulled
              {
                cursor = map_type cursor;
                cursor_call = Option.map map_call cursor_call;
                remaining =
                  Option.map
                    (fun (condition, remaining) ->
                      (Types.map_condition_types map_type map_trait condition, map_call remaining))
                    remaining;
              });
    patterns =
      map_entries tables.patterns (function
        | Variant_pattern pattern -> Variant_pattern { pattern with type_ = map_type pattern.type_ }
        | Record_pattern pattern -> Record_pattern { pattern with type_ = map_type pattern.type_ }
        | (Binding_pattern _ | Constant_pattern _ | Literal_pattern _ | Other_pattern) as pattern ->
            pattern);
    templates =
      map_entries tables.templates (fun template ->
          {
            template with
            from_template = Option.map map_call template.from_template;
            part_conversions = List.map (Option.map map_call) template.part_conversions;
            part = Option.map map_type template.part;
          });
    conditions = map_entries tables.conditions (Types.map_condition_types map_type map_trait);
    conversions =
      Array.map
        (List.map (fun (conversion, expected) -> (conversion, map_type expected)))
        tables.conversions;
    specification_calls =
      map_entries tables.specification_calls (function
        | Method_cost cost ->
            Method_cost
              { cost with trait = map_trait cost.trait; self_type = map_type cost.self_type }
        | Specification_function _ as call -> call);
    literal_elements =
      map_entries tables.literal_elements (function
        | List_element element -> List_element (map_type element)
        | Map_entry { key; value } -> Map_entry { key = map_type key; value = map_type value });
  }

let exists_type predicate (tables : t) =
  let contains table =
    Array.exists (function Some type_ -> Types.exists predicate type_ | None -> false) table
  in
  contains tables.types || contains tables.local_types || contains tables.scrutinee_types

let publish (tables : t) : published =
  {
    types = tables.types;
    local_types = tables.local_types;
    resolutions = tables.resolutions;
    callees =
      Array.map
        (function Some { callee = Function { path; _ }; _ } -> Some path | _ -> None)
        tables.calls;
  }
