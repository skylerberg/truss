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
  lends : Language.Mode.t option;
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
type element_access = Sequence_element | Lent_by_call of call

type loop =
  | Integer_range of { element : Types.ty; inclusive : bool }
  | Elements of { count : call; element : element_access; lends : Language.Mode.t }
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
  | Literal_pattern of Z.t

type template =
  | Interpolated of { displays : call list }
  | Tagged of { from_template : call; part : Types.ty; part_conversions : call option list }

type conversion =
  | From_never
  | Array_as_list
  | To_view
  | Function_widening
  | To_integer
  | From_integer

type specification_call =
  | Old
  | Identical
  | Final of { part : Types.ty }
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

type elaboration =
  | Literal of literal
  | Template of template
  | Call of call
  | Specification_call of specification_call
  | Converted_literal of { elements : literal_elements; call : call }
  | Record_update of { paths : (Syntax.id * string list) list }
  | Lambda of { captures : (Syntax.id * Core.local) list }
  | Loop of loop
  | Discarded

type published = {
  types : Types.ty option array;
  local_types : Types.ty option array;
  resolutions : resolution option array;
  callees : Path.t option array;
}

type t = {
  types : Types.ty option array;
  local_types : Types.ty option array;
  scrutinee_types : Types.ty option array;
  resolutions : resolution option array;
  conversions : (conversion * Types.ty) list array;
  conditions : Types.condition option array;
  patterns : pattern option array;
  elaborations : elaboration option array;
}

let create size =
  {
    types = Array.make size None;
    local_types = Array.make size None;
    scrutinee_types = Array.make size None;
    resolutions = Array.make size None;
    conversions = Array.make size [];
    conditions = Array.make size None;
    patterns = Array.make size None;
    elaborations = Array.make size None;
  }

let make_method_call ?lends trait (method_ : Well_known.method_) ~self_type ~result arguments : call
    =
  let { Well_known.name; receiver; _ } = Well_known.locate_method method_ in
  {
    callee =
      Trait_method { trait; name; receiver; self_type; instantiation = Types.no_instantiation };
    arguments =
      List.mapi
        (fun index (expression, mode) -> { expression; core_argument_index = index; mode })
        arguments;
    omitted_defaults = [];
    callee_result = result;
    lends;
  }

let find_call (tables : t) id =
  match tables.elaborations.(id) with Some (Call call) -> Some call | _ -> None

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
  let map_loop = function
    | Integer_range { element; inclusive } ->
        Integer_range { element = map_type element; inclusive }
    | Elements { count; element; lends } ->
        Elements
          {
            count = map_call count;
            element =
              (match element with
              | Sequence_element -> Sequence_element
              | Lent_by_call element -> Lent_by_call (map_call element));
            lends;
          }
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
          }
  in
  let map_elaboration = function
    | Call call -> Call (map_call call)
    | Converted_literal { elements; call } ->
        Converted_literal
          {
            elements =
              (match elements with
              | List_element element -> List_element (map_type element)
              | Map_entry { key; value } -> Map_entry { key = map_type key; value = map_type value });
            call = map_call call;
          }
    | Template (Interpolated { displays }) ->
        Template (Interpolated { displays = List.map map_call displays })
    | Template (Tagged { from_template; part; part_conversions }) ->
        Template
          (Tagged
             {
               from_template = map_call from_template;
               part = map_type part;
               part_conversions = List.map (Option.map map_call) part_conversions;
             })
    | Specification_call (Final { part }) -> Specification_call (Final { part = map_type part })
    | Specification_call (Method_cost cost) ->
        Specification_call
          (Method_cost
             { cost with trait = map_trait cost.trait; self_type = map_type cost.self_type })
    | Loop loop -> Loop (map_loop loop)
    | ( Literal _ | Record_update _ | Lambda _ | Discarded
      | Specification_call (Old | Identical | Specification_function _) ) as elaboration ->
        elaboration
  in
  let map_entries table transform = Array.map (Option.map transform) table in
  {
    types = map_entries tables.types map_type;
    local_types = map_entries tables.local_types map_type;
    scrutinee_types = map_entries tables.scrutinee_types map_type;
    resolutions =
      map_entries tables.resolutions (function
        | Global { path; instantiation } ->
            Global { path; instantiation = map_instantiation instantiation }
        | Field_access { type_; field } -> Field_access { type_ = map_type type_; field }
        | Variant_value { type_; variant } -> Variant_value { type_ = map_type type_; variant }
        | Type_name type_ -> Type_name (map_type type_)
        | (Local_value _ | Value_parameter _ | Specification_value) as resolution -> resolution);
    conversions =
      Array.map
        (List.map (fun (conversion, expected) -> (conversion, map_type expected)))
        tables.conversions;
    conditions = map_entries tables.conditions (Types.map_condition_types map_type map_trait);
    patterns =
      map_entries tables.patterns (function
        | Variant_pattern pattern -> Variant_pattern { pattern with type_ = map_type pattern.type_ }
        | Record_pattern pattern -> Record_pattern { pattern with type_ = map_type pattern.type_ }
        | (Binding_pattern _ | Constant_pattern _ | Literal_pattern _) as pattern -> pattern);
    elaborations = map_entries tables.elaborations map_elaboration;
  }

let list_arguments_at (tables : t) id =
  let {
    types;
    local_types;
    scrutinee_types;
    resolutions;
    conversions;
    conditions;
    patterns;
    elaborations;
  } =
    tables
  in
  let of_types = List.map (fun type_ -> Types.Type type_) in
  let list_trait (trait : Types.trait_reference) =
    trait.trait_arguments @ of_types (List.map snd trait.associated)
  in
  let list_call (call : call) =
    Types.Type call.callee_result
    ::
    (match call.callee with
    | Function { instantiation; _ } -> instantiation.type_arguments
    | Trait_method { trait; self_type; instantiation; _ } ->
        (Types.Type self_type :: list_trait trait) @ instantiation.type_arguments
    | Constructor { type_arguments; _ } | Intrinsic { type_arguments; _ } -> type_arguments
    | Capability_method _ | Indirect -> [])
  in
  let list_condition (condition : Types.condition) =
    List.concat_map
      (fun (bound : Types.bound_condition) -> Types.Type bound.subject :: list_trait bound.bound)
      condition
  in
  let list_loop = function
    | Integer_range { element; _ } -> [ Types.Type element ]
    | Elements { count; element = Sequence_element; _ } -> list_call count
    | Elements { count; element = Lent_by_call element; _ } -> list_call count @ list_call element
    | Pulled { cursor; cursor_call; remaining; _ } ->
        (Types.Type cursor :: Option.fold ~none:[] ~some:list_call cursor_call)
        @ Option.fold ~none:[]
            ~some:(fun (condition, call) -> list_condition condition @ list_call call)
            remaining
  in
  of_types
    (List.filter_map (fun table -> table.(id)) [ types; local_types; scrutinee_types ]
    @ List.map snd conversions.(id))
  @ (match resolutions.(id) with
    | Some (Global { instantiation; _ }) -> instantiation.type_arguments
    | Some (Field_access { type_; _ } | Variant_value { type_; _ } | Type_name type_) ->
        [ Types.Type type_ ]
    | Some (Local_value _ | Value_parameter _ | Specification_value) | None -> [])
  @ (match patterns.(id) with
    | Some (Variant_pattern { type_; _ } | Record_pattern { type_; _ }) -> [ Types.Type type_ ]
    | Some (Binding_pattern _ | Constant_pattern _ | Literal_pattern _) | None -> [])
  @ Option.fold ~none:[] ~some:list_condition conditions.(id)
  @
  match elaborations.(id) with
  | Some (Call call) -> list_call call
  | Some (Converted_literal { elements = List_element element; call }) ->
      Types.Type element :: list_call call
  | Some (Converted_literal { elements = Map_entry { key; value }; call }) ->
      Types.Type key :: Types.Type value :: list_call call
  | Some (Template (Interpolated { displays })) -> List.concat_map list_call displays
  | Some (Template (Tagged { from_template; part; part_conversions })) ->
      (Types.Type part :: list_call from_template)
      @ List.concat_map (Option.fold ~none:[] ~some:list_call) part_conversions
  | Some (Specification_call (Final { part })) -> [ Types.Type part ]
  | Some (Specification_call (Method_cost { trait; self_type; _ })) ->
      Types.Type self_type :: list_trait trait
  | Some (Loop loop) -> list_loop loop
  | Some
      ( Literal _ | Record_update _ | Lambda _ | Discarded
      | Specification_call (Old | Identical | Specification_function _) )
  | None ->
      []

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
        (function Some (Call { callee = Function { path; _ }; _ }) -> Some path | _ -> None)
        tables.elaborations;
  }
