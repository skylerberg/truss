let raise_bug format = Compiler_bug.raise_bug ~stage:"Infer" format

type constructor =
  | Variant of string
  | Record
  | Boolean of bool
  | Interval of Z.t * Z.t
  | Text of string
  | Opaque_constant of Path.t
  | Opaque_range of { start : Core.range_bound; stop : Core.range_bound; is_inclusive : bool }

type space = Wild | Constructed of constructor * space list | Alternatives of space list

type context = {
  lookups : Lookups.t;
  module_ : Path.module_;
  mutable diagnostics : Catalog.diagnostic list;
}

let report context diagnostic =
  context.diagnostics <- Catalog.Patterns diagnostic :: context.diagnostics

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

let rec build_space ?replace context (written : Core.pattern) : space =
  match written.kind with
  | Wildcard | Bind _ -> Wild
  | Literal value | Equal_to { value; _ } -> evaluate_pattern_constant context value
  | Range { start; stop; inclusive } -> (
      match (evaluate_range_bound context start, evaluate_range_bound context stop) with
      | Some low, Some high ->
          let high = if inclusive then high else Z.pred high in
          if Z.gt low high then Alternatives [] else Constructed (Interval (low, high), [])
      | _ -> Constructed (Opaque_range { start; stop; is_inclusive = inclusive }, []))
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
        ~default:(Constructed (Opaque_constant path, []))

and evaluate_named_constant context path : space option =
  match context.lookups.interface.find_constant_value path with
  | Known value -> Some (build_value_space value)
  | Calls_function | Depends_on_itself | Unevaluated -> None

and build_value_space (value : Interface.Constants.value) : space =
  match value with
  | Integer value -> Constructed (Interval (value, value), [])
  | Boolean value -> Constructed (Boolean value, [])
  | Text text -> Constructed (Text text, [])
  | Constructed { variant; fields; _ } ->
      Constructed
        ( (match variant with Some name -> Variant name | None -> Record),
          List.map (fun (_, field) -> build_value_space field) fields )

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
  let clamp bound = Z.max low (Z.min (Z.succ high) bound) in
  let bounds =
    List.sort_uniq Z.compare
      (low :: Z.succ high
      :: List.concat_map
           (fun (start, stop) -> [ clamp start; clamp (Z.succ stop) ])
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

let split_value_ranges type_ (column : space list) =
  List.concat_map (fun range -> split_intervals range column) (Types.list_value_ranges type_)

let compute_signature context type_ (column : space list) =
  match split_value_ranges type_ column with
  | [] -> list_constructors context type_
  | intervals -> Some (List.map (fun interval -> (interval, [])) intervals)

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
          match
            ( constructor,
              split_value_ranges type_
                (first :: List.filter_map (function first :: _ -> Some first | [] -> None) rows) )
          with
          | Interval _, (_ :: _ as parts) ->
              List.exists
                (fun part ->
                  covers constructor part
                  && is_useful context rest_types (specialize ~width:0 part rows) rest)
                parts
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

let rec build_witness context type_ (pattern : space) : Catalog.Patterns.witness =
  match pattern with
  | Wild | Alternatives [] -> Any
  | Alternatives (first :: _) -> build_witness context type_ first
  | Constructed (Boolean value, _) -> Boolean value
  | Constructed (Interval (low, high), _) when Types.list_value_ranges type_ = [ (low, high) ] ->
      Any
  | Constructed (Interval (low, high), _) -> Integers { low; high }
  | Constructed ((Text _ | Opaque_constant _ | Opaque_range _), _) ->
      raise_bug "a witness holds a constructor that no type's signature lists"
  | Constructed (((Variant _ | Record) as constructor), arguments) -> (
      let declared = read_constructor_fields context type_ constructor in
      let fields =
        List.map2
          (fun (field : Types.field) argument : Catalog.Patterns.field_witness ->
            { field = field.field_name; witness = build_witness context field.field_type argument })
          declared
          (if List.length arguments = List.length declared then arguments
           else List.map (fun _ -> Wild) declared)
      in
      match constructor with Variant variant -> Variant { variant; fields } | _ -> Record fields)

let build_row context types row = List.map2 (build_witness context) types row

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

let rec names_unevaluated_constant context (written : Core.pattern) =
  let is_unevaluated path =
    match context.lookups.interface.find_constant_value path with
    | Unevaluated | Depends_on_itself -> true
    | Known _ | Calls_function -> false
  in
  match written.kind with
  | Literal (Named_constant path) | Equal_to { value = Named_constant path; _ } ->
      is_unevaluated path
  | Range { start; stop; _ } ->
      List.exists
        (function Core.Constant_bound path -> is_unevaluated path | Integer_bound _ -> false)
        [ start; stop ]
  | Variant { fields; _ } | Record fields ->
      List.exists (fun (_, inner) -> names_unevaluated_constant context inner) fields
  | Alternatives alternatives -> List.exists (names_unevaluated_constant context) alternatives
  | Wildcard | Bind _ | Literal _ | Equal_to _ -> false

let check_match context (node : Core.expression) scrutinees (arms : Core.arm list) =
  let types = List.map read_operand_type scrutinees in
  if
    not
      (List.exists (has_error context) types
      || List.exists
           (fun (arm : Core.arm) -> List.exists (names_unevaluated_constant context) arm.patterns)
           arms)
  then begin
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
               witness = build_row context types first;
               other_witnesses = List.map (build_row context types) others;
               may_have_more = List.length all >= witness_limit;
             })
  end

let check_irrefutable context (written : Core.pattern) =
  if not (has_error context written.type_) then
    match find_witness context [ written.type_ ] [ [ build_space context written ] ] with
    | Some witness ->
        report context
          (Refutable
             {
               pattern = written.origin;
               witness = build_witness context written.type_ (List.hd witness);
             })
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
