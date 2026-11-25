let raise_bug format = Compiler_bug.raise_bug ~stage:"Infer" format

type constructor =
  | Variant of string
  | Record
  | Boolean of bool
  | Interval of Z.t * Z.t
  | Text of string
  | Opaque of string

type space = Wild | Constructed of constructor * space list | Alternatives of space list

type context = {
  lookups : Lookups.t;
  module_ : Path.module_;
  mutable diagnostics : Catalog.diagnostic list;
}

let report context diagnostic =
  context.diagnostics <- Catalog.Patterns diagnostic :: context.diagnostics

let compute_integer_range type_ =
  let compute_bounds signed width =
    if signed then
      Some (Z.neg (Z.shift_left Z.one (width - 1)), Z.pred (Z.shift_left Z.one (width - 1)))
    else Some (Z.zero, Z.pred (Z.shift_left Z.one width))
  in
  match Types.find_builtin type_ with
  | Some Int8 -> compute_bounds true 8
  | Some Int16 -> compute_bounds true 16
  | Some Int32 -> compute_bounds true 32
  | Some Int64 -> compute_bounds true 64
  | Some UInt8 -> compute_bounds false 8
  | Some UInt16 -> compute_bounds false 16
  | Some UInt32 -> compute_bounds false 32
  | Some UInt64 -> compute_bounds false 64
  | Some Character -> Some (Z.zero, Z.of_int 0x10FFFF)
  | _ -> None

let read_fields context path arguments =
  Option.bind (Interface.Definition.find_type_interface context.lookups.interface path)
    (fun interface -> Types.instantiate_fields interface arguments)

let read_variants context path arguments =
  Option.bind (Interface.Definition.find_type_interface context.lookups.interface path)
    (fun interface -> Types.instantiate_variants interface arguments)

let read_constructor_fields context type_ constructor =
  match (type_, constructor) with
  | Types.Named { path; arguments }, Variant name -> (
      match read_variants context path arguments with
      | Some variants -> (
          match
            List.find_opt (fun (variant : Types.variant) -> variant.variant_name = name) variants
          with
          | Some variant -> Option.value ~default:[] variant.fields
          | None -> [])
      | None -> [])
  | Types.Named { path; arguments }, Record ->
      Option.value ~default:[] (read_fields context path arguments)
  | _ -> []

let read_field_types context type_ constructor =
  List.map
    (fun (field : Types.field) -> field.field_type)
    (read_constructor_fields context type_ constructor)

let compute_arity context type_ constructor =
  List.length (read_constructor_fields context type_ constructor)

let list_constructors context type_ : (constructor * Types.ty list) list option =
  let list_types = List.map (fun (field : Types.field) -> field.field_type) in
  match type_ with
  | Types.Named { path; arguments } -> (
      match Interface.Definition.find_type_interface context.lookups.interface path with
      | Some ({ shape = Sum _; _ } as interface) ->
          Option.map
            (List.map (fun (variant : Types.variant) ->
                 (Variant variant.variant_name, list_types (Option.value ~default:[] variant.fields))))
            (Types.instantiate_variants interface arguments)
      | Some ({ shape = Record _; _ } as interface) ->
          Some
            [
              ( Record,
                list_types (Option.value ~default:[] (Types.instantiate_fields interface arguments))
              );
            ]
      | Some { shape = Builtin_type Bool; _ } -> Some [ (Boolean false, []); (Boolean true, []) ]
      | Some { shape = Builtin_type Unit; _ } -> Some [ (Record, []) ]
      | Some { shape = Builtin_type _ | Todo_type; _ } | None -> None)
  | _ -> None

let show_range_bound : Core.range_bound -> string = function
  | Integer_bound value -> Z.to_string value
  | Constant_bound path -> Path.show path

let show_range start stop ~inclusive =
  show_range_bound start ^ (if inclusive then "..=" else "..") ^ show_range_bound stop

let rec build_space ?replace context (written : Core.pattern) : space =
  match written.kind with
  | Wildcard | Bind _ -> Wild
  | Literal value | Equal_to { value; _ } -> evaluate_pattern_constant context value
  | Range { start; stop; inclusive } -> (
      match (evaluate_range_bound context start, evaluate_range_bound context stop) with
      | Some low, Some high ->
          let high = if inclusive then high else Z.pred high in
          if Z.gt low high then Alternatives [] else Constructed (Interval (low, high), [])
      | _ -> Constructed (Opaque (show_range start stop ~inclusive), []))
  | Variant { variant; fields } ->
      build_constructed_space ?replace context written.type_ (Variant variant) fields
  | Record fields -> build_constructed_space ?replace context written.type_ Record fields
  | Alternatives alternatives ->
      let alternatives =
        match replace with Some (id, only) when id = written.id -> only | _ -> alternatives
      in
      Alternatives (List.map (build_space ?replace context) alternatives)

and evaluate_pattern_constant context (value : Core.pattern_constant) : space =
  match value with
  | Boolean_constant value -> Constructed (Boolean value, [])
  | Integer_constant value -> Constructed (Interval (value, value), [])
  | String_constant text -> Constructed (Text text, [])
  | Named_constant path ->
      Option.value
        (evaluate_named_constant context path)
        ~default:(Constructed (Opaque (Path.show path), []))

and evaluate_named_constant ?(seen = []) context path : space option =
  if List.exists (Path.equal path) seen then None
  else
    match context.lookups.interface.names.find_key path with
    | None -> raise_bug "the constant `%s` in a pattern has no declaration" (Path.show path)
    | Some key -> (
        match
          ( (context.lookups.read_contract key).definition,
            context.lookups.interface.find_constant_value path )
        with
        | Constant (Some _), Some folded -> Some (Constructed (Interval (folded, folded), []))
        | Constant (Some value), None -> evaluate_constant_expression context (path :: seen) value
        | _ -> raise_bug "the contract of the constant `%s` holds no value" (Path.show path))

and evaluate_constant_expression context seen (value : Core.expression) : space option =
  match value.kind with
  | Use (Constant { path; _ }) -> evaluate_named_constant ~seen context path
  | Construct { variant; fields } ->
      let parts =
        List.map
          (fun (_, (field : Core.operand option)) ->
            match field with
            | Some (Value field) -> evaluate_constant_expression context seen field
            | Some (Place _) | None -> None)
          fields
      in
      if List.for_all Option.is_some parts then
        Some
          (Constructed
             ( (match variant with Some name -> Variant name | None -> Record),
               List.map Option.get parts ))
      else None
  | Boolean value -> Some (Constructed (Boolean value, []))
  | Integer value -> Some (Constructed (Interval (value, value), []))
  | Literal (Text text) -> Some (Constructed (Text text, []))
  | _ -> None

and evaluate_range_bound context (bound : Core.range_bound) : Z.t option =
  match bound with
  | Integer_bound value -> Some value
  | Constant_bound path -> (
      match evaluate_named_constant context path with
      | Some (Constructed (Interval (value, _), [])) -> Some value
      | _ -> None)

and build_constructed_space ?replace context type_ constructor
    (written : (string * Core.pattern) list) =
  Constructed
    ( constructor,
      List.map
        (fun (declared : Types.field) ->
          match List.assoc_opt declared.field_name written with
          | Some inner -> build_space ?replace context inner
          | None -> Wild)
        (read_constructor_fields context type_ constructor) )

type row = space list

let split_intervals (low, high) (column : space list) =
  let rec collect_intervals = function
    | Constructed (Interval (low, high), _) -> [ (low, high) ]
    | Alternatives alternatives -> List.concat_map collect_intervals alternatives
    | _ -> []
  in
  let bounds =
    List.sort_uniq Z.compare
      (low :: Z.succ high
      :: List.concat_map
           (fun (start, stop) -> [ Z.max low start; Z.min (Z.succ high) (Z.succ stop) ])
           (List.concat_map collect_intervals column))
  in
  let rec pair_bounds = function
    | first :: (second :: _ as rest) ->
        if Z.lt first second then (first, Z.pred second) :: pair_bounds rest else pair_bounds rest
    | _ -> []
  in
  List.map (fun (low, high) -> Interval (low, high)) (pair_bounds bounds)

let rec list_head_constructors = function
  | Constructed (constructor, _) -> [ constructor ]
  | Alternatives alternatives -> List.concat_map list_head_constructors alternatives
  | Wild -> []

let covers pattern_constructor constructor =
  match (pattern_constructor, constructor) with
  | Interval (low, high), Interval (part_low, part_high) ->
      Z.leq low part_low && Z.leq part_high high
  | left, right -> left = right

let rec specialize ~width constructor (rows : row list) =
  List.concat_map
    (fun row ->
      match row with
      | [] -> []
      | Wild :: rest -> [ List.init width (fun _ -> Wild) @ rest ]
      | Constructed (head_constructor, arguments) :: rest ->
          if covers head_constructor constructor then [ arguments @ rest ] else []
      | Alternatives alternatives :: rest ->
          specialize ~width constructor
            (List.map (fun alternative -> alternative :: rest) alternatives))
    rows

let rec build_default_matrix (rows : row list) =
  List.concat_map
    (fun row ->
      match row with
      | Wild :: rest -> [ rest ]
      | Alternatives alternatives :: rest ->
          build_default_matrix (List.map (fun alternative -> alternative :: rest) alternatives)
      | _ -> [])
    rows

let compute_signature context type_ (column : space list) =
  match compute_integer_range type_ with
  | Some range -> Some (List.map (fun interval -> (interval, [])) (split_intervals range column))
  | None -> list_constructors context type_

let rec find_witness context (types : Types.ty list) (rows : row list) : space list option =
  match types with
  | [] -> if rows = [] then Some [] else None
  | type_ :: rest_types -> (
      let column = List.filter_map (function first :: _ -> Some first | [] -> None) rows in
      let try_constructor (constructor, field_types) =
        let width = List.length field_types in
        match
          find_witness context (field_types @ rest_types) (specialize ~width constructor rows)
        with
        | Some witness ->
            Some (Constructed (constructor, List.take width witness) :: List.drop width witness)
        | None -> None
      in
      let present = List.concat_map list_head_constructors column in
      let is_present (constructor, _) =
        List.exists (fun other -> covers other constructor) present
      in
      match (type_, compute_signature context type_ column) with
      | (Types.Error _ | Types.Hole | Types.Never), _ -> None
      | _, Some all when all <> [] && List.for_all is_present all ->
          List.find_map try_constructor all
      | _, signature -> (
          match find_witness context rest_types (build_default_matrix rows) with
          | None -> None
          | Some witness -> (
              match Option.bind signature (List.find_opt (Fun.negate is_present)) with
              | Some (constructor, field_types) when present <> [] ->
                  Some (Constructed (constructor, List.map (fun _ -> Wild) field_types) :: witness)
              | _ -> Some (Wild :: witness))))

let rec is_useful context (types : Types.ty list) (rows : row list) (row : row) =
  match (types, row) with
  | [], [] -> rows = []
  | type_ :: rest_types, first :: rest -> (
      match first with
      | Alternatives alternatives ->
          List.exists
            (fun alternative -> is_useful context types rows (alternative :: rest))
            alternatives
      | Constructed (constructor, arguments) -> (
          match (constructor, compute_integer_range type_) with
          | Interval _, Some range ->
              List.exists
                (fun part ->
                  covers constructor part
                  && is_useful context rest_types (specialize ~width:0 part rows) rest)
                (split_intervals range
                   (first :: List.filter_map (function first :: _ -> Some first | [] -> None) rows))
          | _ ->
              let field_types = read_field_types context type_ constructor in
              is_useful context (field_types @ rest_types)
                (specialize ~width:(List.length field_types) constructor rows)
                (arguments @ rest))
      | Wild -> (
          let column = List.filter_map (function first :: _ -> Some first | [] -> None) rows in
          let present = List.concat_map list_head_constructors column in
          match compute_signature context type_ column with
          | Some all
            when all <> []
                 && List.for_all
                      (fun (constructor, _) ->
                        List.exists (fun other -> covers other constructor) present)
                      all ->
              List.exists
                (fun (constructor, field_types) ->
                  is_useful context (field_types @ rest_types)
                    (specialize ~width:(List.length field_types) constructor rows)
                    (List.map (fun _ -> Wild) field_types @ rest))
                all
          | _ -> is_useful context rest_types (build_default_matrix rows) rest))
  | _ -> false

let rec show context type_ (pattern : space) =
  match pattern with
  | Wild | Alternatives [] -> "_"
  | Alternatives (first :: _) -> show context type_ first
  | Constructed (Boolean value, _) -> if value then "true" else "false"
  | Constructed (Interval (low, high), _) when compute_integer_range type_ = Some (low, high) -> "_"
  | Constructed (Interval (low, high), _) ->
      if Z.equal low high then Z.to_string low
      else Printf.sprintf "%s..=%s" (Z.to_string low) (Z.to_string high)
  | Constructed (Text text, _) -> Printf.sprintf "%S" text
  | Constructed (Opaque shown, _) -> shown
  | Constructed (constructor, arguments) -> (
      let fields = read_constructor_fields context type_ constructor in
      let shown =
        List.map2
          (fun (field : Types.field) argument -> show context field.field_type argument)
          fields
          (if List.length arguments = List.length fields then arguments
           else List.map (fun _ -> Wild) fields)
      in
      let prefix = match constructor with Variant name -> name | _ -> "" in
      let is_wild = List.for_all (fun shown -> shown = "_") shown in
      match (constructor, fields, shown) with
      | Variant name, [], _ -> name
      | _, [], _ -> "()"
      | Variant name, [ _ ], [ "_" ] -> Printf.sprintf "%s(_)" name
      | Variant name, _, _ when is_wild -> Printf.sprintf "%s(..)" name
      | _, _, _ when is_wild -> "_"
      | _, [ _ ], [ only ] -> Printf.sprintf "%s(%s)" prefix only
      | _ ->
          Printf.sprintf "%s(%s)" prefix
            (String.concat ", "
               (List.map2
                  (fun (field : Types.field) shown ->
                    if shown = "_" then field.field_name ^ ": _"
                    else field.field_name ^ ": " ^ shown)
                  fields shown)))

let show_row context types row = String.concat ", " (List.map2 (show context) types row)

let read_operand_type : Core.operand -> Types.ty = function
  | Place core_place -> Core_walk.compute_place_type core_place
  | Value value -> value.type_

let has_error context type_ =
  let visited = ref [] in
  let rec contains_error = function
    | Types.Error _ | Types.Hole -> true
    | Types.Named { path; arguments } -> (
        List.exists (function Types.Type type_ -> contains_error type_ | _ -> false) arguments
        || (not (List.exists (Path.equal path) !visited))
           &&
           let () = visited := path :: !visited in
           let fields_have_error fields =
             List.exists (fun (field : Types.field) -> contains_error field.field_type) fields
           in
           match Interface.Definition.find_type_interface context.lookups.interface path with
           | Some ({ shape = Record _; _ } as interface) ->
               fields_have_error
                 (Option.value ~default:[] (Types.instantiate_fields interface arguments))
           | Some ({ shape = Sum _; _ } as interface) ->
               List.exists
                 (fun (variant : Types.variant) ->
                   fields_have_error (Option.value ~default:[] variant.fields))
                 (Option.value ~default:[] (Types.instantiate_variants interface arguments))
           | Some { shape = Builtin_type _ | Todo_type; _ } | None -> false)
    | _ -> false
  in
  contains_error type_

let rec list_or_patterns (written : Core.pattern) =
  match written.kind with
  | Alternatives alternatives ->
      (written, alternatives) :: List.concat_map list_or_patterns alternatives
  | Variant { fields; _ } | Record fields ->
      List.concat_map (fun (_, inner) -> list_or_patterns inner) fields
  | Wildcard | Bind _ | Literal _ | Range _ | Equal_to _ -> []

type shadowing = { name : string; constant : Path.t; bindings : Core.pattern list }

let list_shadowings context (patterns : Core.pattern list) =
  let rec list_bindings (written : Core.pattern) =
    match written.kind with
    | Bind { local = Declared { name; _ }; _ } -> [ (name, written) ]
    | Variant { variant; fields } -> list_field_bindings written.type_ (Variant variant) fields
    | Record fields -> list_field_bindings written.type_ Record fields
    | Alternatives alternatives -> List.concat_map list_bindings alternatives
    | Bind _ | Wildcard | Literal _ | Range _ | Equal_to _ -> []
  and list_field_bindings type_ constructor fields =
    let has_several_fields = compute_arity context type_ constructor > 1 in
    List.concat_map
      (fun (field, (inner : Core.pattern)) ->
        match inner.kind with
        | Bind { local = Declared { name; _ }; _ } when has_several_fields && name = field -> []
        | _ -> list_bindings inner)
      fields
  in
  let bindings = List.concat_map list_bindings patterns in
  let names =
    List.fold_left
      (fun names (name, _) -> if List.mem name names then names else names @ [ name ])
      [] bindings
  in
  List.filter_map
    (fun name ->
      match
        List.filter_map (fun (other, bound) -> if other = name then Some bound else None) bindings
      with
      | (first : Core.pattern) :: _ as named ->
          Option.map
            (fun constant -> { name; constant; bindings = named })
            (Interface.Definition.find_shadowed_constant context.lookups.interface context.module_
               ~name ~type_:first.type_)
      | [] -> None)
    names

let rec substitute_constant shadowing (written : Core.pattern) : Core.pattern =
  if List.exists (fun (bound : Core.pattern) -> bound.id = written.id) shadowing.bindings then
    { written with kind = Literal (Named_constant shadowing.constant) }
  else
    let substitute_fields =
      List.map (fun (field, inner) -> (field, substitute_constant shadowing inner))
    in
    match written.kind with
    | Variant { variant; fields } ->
        { written with kind = Variant { variant; fields = substitute_fields fields } }
    | Record fields -> { written with kind = Record (substitute_fields fields) }
    | Alternatives alternatives ->
        { written with kind = Alternatives (List.map (substitute_constant shadowing) alternatives) }
    | Wildcard | Bind _ | Literal _ | Range _ | Equal_to _ -> written

let find_shadowing context types covering_arms unreachable_row =
  let rows = List.map (List.map (build_space context)) covering_arms in
  List.find_mapi
    (fun index patterns ->
      List.find_opt
        (fun shadowing ->
          let row_with_constant =
            List.map
              (fun written -> build_space context (substitute_constant shadowing written))
              patterns
          in
          is_useful context types
            (List.mapi
               (fun other other_row -> if other = index then row_with_constant else other_row)
               rows)
            unreachable_row)
        (list_shadowings context patterns))
    covering_arms

let witness_limit = 8

let check_match context (node : Core.expression) scrutinees (arms : Core.arm list) =
  let types = List.map read_operand_type scrutinees in
  if not (List.exists (has_error context) types) then begin
    let rows = ref [] in
    let covering_arms = ref [] in
    List.iter
      (fun (arm : Core.arm) ->
        if List.length arm.patterns = List.length types then begin
          let row = List.map (build_space context) arm.patterns in
          let reachable = is_useful context types !rows row in
          if not reachable then
            begin match find_shadowing context types !covering_arms row with
            | Some shadowing ->
                report context
                  (Shadowing_arm
                     {
                       arm = arm.origin;
                       name = shadowing.name;
                       constant = shadowing.constant;
                       bindings =
                         List.map (fun (bound : Core.pattern) -> bound.origin) shadowing.bindings;
                     })
            | None -> report context (Unreachable_arm { arm = arm.origin })
            end
          else
            List.iter
              (fun ((group : Core.pattern), alternatives) ->
                List.iteri
                  (fun index (alternative : Core.pattern) ->
                    let build_row_with only =
                      List.map (build_space ~replace:(group.id, only) context) arm.patterns
                    in
                    let before = List.take index alternatives in
                    let prior = if before = [] then !rows else !rows @ [ build_row_with before ] in
                    if not (is_useful context types prior (build_row_with [ alternative ])) then
                      let origin_of (pattern : Core.pattern) = pattern.origin in
                      report context
                        (Unreachable_alternative
                           {
                             alternative = alternative.origin;
                             previous =
                               Option.map origin_of
                                 (if index > 0 then List.nth_opt alternatives (index - 1) else None);
                             next =
                               (if index > 0 then None
                                else Option.map origin_of (List.nth_opt alternatives 1));
                             is_after_alternatives = before <> [];
                           }))
                  alternatives)
              (List.concat_map list_or_patterns arm.patterns);
          if Option.is_none arm.guard then begin
            rows := !rows @ [ row ];
            covering_arms := !covering_arms @ [ arm.patterns ]
          end
        end)
      arms;
    let rec collect_witnesses rows witnesses_so_far =
      if List.length witnesses_so_far >= witness_limit then List.rev witnesses_so_far
      else
        match find_witness context types rows with
        | Some witness -> collect_witnesses (rows @ [ witness ]) (witness :: witnesses_so_far)
        | None -> List.rev witnesses_so_far
    in
    match collect_witnesses !rows [] with
    | [] -> ()
    | first :: others as all ->
        report context
          (Not_covered
             {
               match_ = node.origin;
               last_arm =
                 Option.map (fun (last : Core.arm) -> last.origin) (List.nth_opt (List.rev arms) 0);
               witness = show_row context types first;
               other_witnesses = List.map (show_row context types) others;
               may_have_more = List.length all >= witness_limit;
             })
  end

let check_irrefutable context (written : Core.pattern) =
  if not (has_error context written.type_) then
    match find_witness context [ written.type_ ] [ [ build_space context written ] ] with
    | Some witness ->
        report context
          (Refutable
             { pattern = written.origin; witness = show context written.type_ (List.hd witness) })
    | None -> ()

let check_definition context (definition : Core.definition) =
  Core_walk.walk_definition
    {
      Core_walk.ignore_all with
      expression =
        (fun (node : Core.expression) ->
          match node.kind with
          | Match { scrutinees; arms; _ } -> check_match context node scrutinees arms
          | Lambda { parameters; _ } -> List.iter (check_irrefutable context) parameters
          | _ -> ());
      statement =
        (fun (node : Core.statement) ->
          match node.kind with
          | Let { pattern; else_ = None; _ } | For { pattern; _ } ->
              check_irrefutable context pattern
          | Let { else_ = Some _; _ }
          | Evaluate _ | Assign _ | Compound_assign _ | While _ | Parallel _ | Concurrent _
          | Proof _ | Assert _ | Yield _ ->
              ());
    }
    definition

let check (lookups : Lookups.t) (key : Resolve.Names.key) (form : Core.t) =
  let context = { lookups; module_ = key.module_; diagnostics = [] } in
  check_definition context form.definition;
  List.rev context.diagnostics
