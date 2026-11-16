module Lookups = Lookups

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
  spans : Source.Definition_span.t array Lazy.t;
  text : string Lazy.t;
  mutable diagnostics : Diagnostic.in_definition list;
}

let read_span context (origin : Core.origin) : Source.Definition_span.t =
  Source.Definition_span.locate (Lazy.force context.spans) origin

let report context ?(fixes = []) code (span : Source.Definition_span.t) message =
  context.diagnostics <-
    Diagnostic.make ~fixes ~code:(Patterns code) span message :: context.diagnostics

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
  Option.bind (Interface.Definition.read_type_interface context.lookups.interface path)
    (fun interface -> Types.instantiate_fields interface arguments)

let read_variants context path arguments =
  Option.bind (Interface.Definition.read_type_interface context.lookups.interface path)
    (fun interface -> Types.instantiate_variants interface arguments)

let read_shape context path =
  Option.map
    (fun (interface : Types.type_interface) -> interface.shape)
    (Interface.Definition.read_type_interface context.lookups.interface path)

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
    match context.lookups.interface.find_constant_value path with
    | Some value -> Some (Constructed (Interval (value, value), []))
    | None -> (
        match
          Option.map context.lookups.read_core (context.lookups.interface.names.find_key path)
        with
        | Some { definition = Constant (Some value); _ } ->
            evaluate_constant_expression context (path :: seen) value
        | _ -> None)

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
  | String text -> Some (Constructed (Text text, []))
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

let find_constructors context type_ =
  match type_ with
  | Types.Named { path; arguments } -> (
      match read_shape context path with
      | Some (Sum _) -> (
          match read_variants context path arguments with
          | Some variants ->
              Some
                (List.map (fun (variant : Types.variant) -> Variant variant.variant_name) variants)
          | None -> None)
      | Some (Record _) -> Some [ Record ]
      | Some (Builtin_type Bool) -> Some [ Boolean false; Boolean true ]
      | Some (Builtin_type Unit) -> Some [ Record ]
      | _ -> None)
  | _ -> None

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

let rec specialize context type_ constructor (rows : row list) =
  let width = compute_arity context type_ constructor in
  List.concat_map
    (fun row ->
      match row with
      | [] -> []
      | Wild :: rest -> [ List.init width (fun _ -> Wild) @ rest ]
      | Constructed (head_constructor, arguments) :: rest ->
          if covers head_constructor constructor then [ arguments @ rest ] else []
      | Alternatives alternatives :: rest ->
          specialize context type_ constructor
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
  | Some range -> Some (split_intervals range column)
  | None -> find_constructors context type_

let rec find_witness context (types : Types.ty list) (rows : row list) : space list option =
  match types with
  | [] -> if rows = [] then Some [] else None
  | type_ :: rest_types -> (
      let column = List.filter_map (function first :: _ -> Some first | [] -> None) rows in
      let try_constructor constructor =
        let arguments = read_field_types context type_ constructor in
        match
          find_witness context (arguments @ rest_types) (specialize context type_ constructor rows)
        with
        | Some witness ->
            let count = List.length arguments in
            let fields = List.filteri (fun index _ -> index < count) witness
            and rest = List.filteri (fun index _ -> index >= count) witness in
            Some (Constructed (constructor, fields) :: rest)
        | None -> None
      in
      let present = List.concat_map list_head_constructors column in
      match (type_, compute_signature context type_ column) with
      | (Types.Error _ | Types.Hole | Types.Never), _ -> None
      | _, Some all
        when all <> []
             && List.for_all
                  (fun constructor -> List.exists (fun other -> covers other constructor) present)
                  all ->
          List.find_map try_constructor all
      | _, signature -> (
          match find_witness context rest_types (build_default_matrix rows) with
          | None -> None
          | Some witness -> (
              let absent =
                match signature with
                | Some all ->
                    List.find_opt
                      (fun constructor ->
                        not (List.exists (fun other -> covers other constructor) present))
                      all
                | None -> None
              in
              match absent with
              | Some constructor when present <> [] ->
                  let count = List.length (read_field_types context type_ constructor) in
                  Some (Constructed (constructor, List.init count (fun _ -> Wild)) :: witness)
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
                  && is_useful context rest_types (specialize context type_ part rows) rest)
                (split_intervals range
                   (first :: List.filter_map (function first :: _ -> Some first | [] -> None) rows))
          | _ ->
              is_useful context
                (read_field_types context type_ constructor @ rest_types)
                (specialize context type_ constructor rows)
                (arguments @ rest))
      | Wild -> (
          let column = List.filter_map (function first :: _ -> Some first | [] -> None) rows in
          match compute_signature context type_ column with
          | Some all
            when all <> []
                 && List.for_all
                      (fun constructor ->
                        List.exists
                          (fun other -> covers other constructor)
                          (List.concat_map list_head_constructors column))
                      all ->
              List.exists
                (fun constructor ->
                  is_useful context
                    (read_field_types context type_ constructor @ rest_types)
                    (specialize context type_ constructor rows)
                    (List.init
                       (List.length (read_field_types context type_ constructor))
                       (fun _ -> Wild)
                    @ rest))
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
  let rec contains_error seen = function
    | Types.Error _ | Types.Hole -> true
    | Types.Named { path; arguments } -> (
        List.exists
          (function Types.Type type_ -> contains_error seen type_ | _ -> false)
          arguments
        || (not (List.exists (Path.equal path) seen))
           &&
           let seen = path :: seen in
           let fields_have_error fields =
             List.exists (fun (field : Types.field) -> contains_error seen field.field_type) fields
           in
           match read_shape context path with
           | Some (Record _) ->
               fields_have_error (Option.value ~default:[] (read_fields context path arguments))
           | Some (Sum _) -> (
               match read_variants context path arguments with
               | Some variants ->
                   List.exists
                     (fun (variant : Types.variant) ->
                       fields_have_error (Option.value ~default:[] variant.fields))
                     variants
               | None -> false)
           | _ -> false)
    | _ -> false
  in
  contains_error [] type_

let read_indentation text (position : int) =
  let line_start = Source.fragment_line_start text position in
  let rec skip_spaces index =
    if index < String.length text && (text.[index] = ' ' || text.[index] = '\t') then
      skip_spaces (index + 1)
    else index
  in
  String.sub text line_start (skip_spaces line_start - line_start)

let rec list_or_patterns (written : Core.pattern) =
  match written.kind with
  | Alternatives alternatives ->
      (written, alternatives) :: List.concat_map list_or_patterns alternatives
  | Variant { fields; _ } | Record fields ->
      List.concat_map (fun (_, inner) -> list_or_patterns inner) fields
  | Wildcard | Bind _ | Literal _ | Range _ | Equal_to _ -> []

let witness_limit = 8

let check_match context (node : Core.expression) scrutinees (arms : Core.arm list) =
  let types = List.map read_operand_type scrutinees in
  if not (List.exists (has_error context) types) then begin
    let rows = ref [] in
    List.iter
      (fun (arm : Core.arm) ->
        if List.length arm.patterns = List.length types then begin
          let row = List.map (build_space context) arm.patterns in
          let arm_span = read_span context arm.origin in
          let reachable = is_useful context types !rows row in
          if not reachable then
            report context Unreachable_arm arm_span
              ~fixes:
                [
                  Diagnostic.fix "Delete the arm."
                    [
                      Diagnostic.delete
                        (Source.Definition_span.make
                           (arm_span.start
                           - String.length
                               (read_indentation (Lazy.force context.text) arm_span.start)
                           - 1)
                           arm_span.stop);
                    ];
                ]
              "Earlier arms already match everything this arm matches, so it is never reached."
          else
            List.iter
              (fun ((group : Core.pattern), alternatives) ->
                List.iteri
                  (fun index (alternative : Core.pattern) ->
                    let build_row_with only =
                      List.map (build_space ~replace:(group.id, only) context) arm.patterns
                    in
                    let before = List.filteri (fun other _ -> other < index) alternatives in
                    let prior = if before = [] then !rows else !rows @ [ build_row_with before ] in
                    if not (is_useful context types prior (build_row_with [ alternative ])) then
                      let read_pattern_span (pattern : Core.pattern) =
                        read_span context pattern.origin
                      in
                      let alternative_span = read_pattern_span alternative in
                      let deleted =
                        match if index > 0 then List.nth_opt alternatives (index - 1) else None with
                        | Some previous ->
                            Source.Definition_span.make (read_pattern_span previous).stop
                              alternative_span.stop
                        | None -> (
                            match List.nth_opt alternatives 1 with
                            | Some next ->
                                Source.Definition_span.make alternative_span.start
                                  (read_pattern_span next).start
                            | None -> alternative_span)
                      in
                      report context Unreachable_alternative alternative_span
                        ~fixes:
                          [ Diagnostic.fix "Delete the alternative." [ Diagnostic.delete deleted ] ]
                        (if before = [] then
                           "Earlier arms already match everything this alternative matches."
                         else
                           "The alternatives before this one already match everything it matches."))
                  alternatives)
              (List.concat_map list_or_patterns arm.patterns);
          if Option.is_none arm.guard then rows := !rows @ [ row ]
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
    | first :: _ as all ->
        let fixes =
          match List.rev arms with
          | last :: _ ->
              let last = read_span context last.origin in
              let indent = read_indentation (Lazy.force context.text) last.start in
              [
                Diagnostic.fix "Add an arm for each missing case."
                  [
                    Diagnostic.replace
                      (Source.Definition_span.zero_width last.stop)
                      (String.concat ""
                         (List.map
                            (fun witness ->
                              "\n" ^ indent ^ show_row context types witness ^ " => todo")
                            all));
                  ];
              ]
          | [] -> []
        in
        report context Not_covered (read_span context node.origin) ~fixes
          (Printf.sprintf "This `match` does not cover every case: `%s` is not covered%s."
             (show_row context types first)
             (match List.length all with
             | 1 -> ""
             | count when count >= witness_limit -> ", nor others"
             | count -> Printf.sprintf ", nor %d others" (count - 1)))
  end

let check_irrefutable context (written : Core.pattern) =
  if not (has_error context written.type_) then
    match find_witness context [ written.type_ ] [ [ build_space context written ] ] with
    | Some witness ->
        report context Refutable
          (read_span context written.origin)
          (Printf.sprintf
             "This pattern can fail: it does not match `%s`. Use `match`, an `is` test, or `let \
              ... else`."
             (show context written.type_ (List.hd witness)))
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

let check (lookups : Lookups.t) key =
  let context =
    {
      lookups;
      spans = lazy (lookups.interface.names.list_spans key);
      text = lazy (lookups.interface.names.read_text key);
      diagnostics = [];
    }
  in
  check_definition context (lookups.read_core key).definition;
  List.sort
    (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
      compare left.span right.span)
    context.diagnostics
