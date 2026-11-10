(* Exhaustiveness and reachability, by Maranget's usefulness algorithm
   ("Warnings for pattern matching", 2007), over the matched values as a
   vector, so a [match] over several values is checked as one.

   Constructors are the variants of a sum type, a record's one shape,
   [true] and [false], and for integers and [Character] the intervals that
   the patterns' literals and ranges split the type into. Strings have
   infinitely many values, so only a pattern that matches everything
   covers them. An arm with a guard never covers its pattern. *)

open Syntax
module T = Types
module C = Checked
module Members = Infer.Members

(* The space of patterns *)

type constructor =
  | Variant of string
  | Record
  | Boolean of bool
  | Interval of Z.t * Z.t  (** Inclusive. *)
  | Text of string  (** A string literal, one of infinitely many. *)
  | Opaque_constant of Path.t
      (** A constant whose value is not worked out, which covers nothing else. *)

type space = Wild | Constructed of constructor * space list | Alternatives of space list

type context = {
  database : Query.context;
  package : string;
  checked : C.t;
  mutable diagnostics : Diagnostic.t list;
}

let report context ?(fixes = []) code (span : span) message =
  context.diagnostics <-
    Diagnostic.make ~fixes ~code:(Patterns code) (Source.span span.start span.stop) message
    :: context.diagnostics

let integer_range type_ =
  let bits signed width =
    if signed then
      Some (Z.neg (Z.shift_left Z.one (width - 1)), Z.pred (Z.shift_left Z.one (width - 1)))
    else Some (Z.zero, Z.pred (Z.shift_left Z.one width))
  in
  match T.builtin_of type_ with
  | Some Int8 -> bits true 8
  | Some Int16 -> bits true 16
  | Some Int32 -> bits true 32
  | Some (Int64 | ISize) -> bits true 64
  | Some UInt8 -> bits false 8
  | Some UInt16 -> bits false 16
  | Some UInt32 -> bits false 32
  | Some (UInt64 | USize) -> bits false 64
  | Some Character -> Some (Z.zero, Z.of_int 0x10FFFF)
  | _ -> None

(* The fields of the shape a constructor makes, in declared order, with the
   type's arguments substituted. *)
let fields_of context type_ constructor =
  match (type_, constructor) with
  | T.Named { path; arguments }, Variant name -> (
      match Members.variants context.database path arguments with
      | Some variants -> (
          match
            List.find_opt (fun (variant : T.variant) -> variant.variant_name = name) variants
          with
          | Some variant -> Option.value ~default:[] variant.fields
          | None -> [])
      | None -> [])
  | T.Named { path; arguments }, Record ->
      Option.value ~default:[] (Members.fields context.database path arguments)
  | _ -> []

(* A constant, an interval, a [Bool], or a string has no fields, which
   [fields_of] gives as none. *)
let field_types context type_ constructor =
  List.map (fun (field : T.field) -> field.field_type) (fields_of context type_ constructor)

let arity context type_ constructor = List.length (fields_of context type_ constructor)

(* A written pattern as a space, its fields put in declared order, with
   fields it does not name as wildcards. *)
(* [replace] stands one or-pattern, by its id, for only some of its
   alternatives, to ask what those alone cover. *)
let rec space ?replace context type_ (written : pattern) : space =
  match written.kind with
  | Wildcard | Pattern_error -> Wild
  | Binding_or_constant _ | Qualified_constant _ -> (
      match context.checked.patterns.(written.id) with
      | Some (Constant_pattern path) -> constant context type_ path
      | _ -> Wild)
  | Literal literal -> literal_space context written.id literal
  | Pattern_range { start; stop; inclusive } -> (
      match (range_end context start, range_end context stop) with
      | Ok (Some low), Ok (Some high) ->
          let high = if inclusive then high else Z.pred high in
          if Z.gt low high then Alternatives [] else Constructed (Interval (low, high), [])
      (* An end whose value is not worked out here covers nothing else. *)
      | Error path, _ | _, Error path -> Constructed (Opaque_constant path, [])
      | _ -> Wild)
  | Variant { name; fields } ->
      fielded ?replace context type_ (Variant name.last.text) (Option.value ~default:[] fields)
  | Record fields -> fielded ?replace context type_ Record fields
  | Alternatives alternatives ->
      let alternatives =
        match replace with Some (id, only) when id = written.id -> only | _ -> alternatives
      in
      Alternatives (List.map (space ?replace context type_) alternatives)

(* A literal's value as body checking recorded it, so a character or byte
   is the integer it stands for. *)
and literal_space context id = function
  | Literal_true -> Constructed (Boolean true, [])
  | Literal_false -> Constructed (Boolean false, [])
  | literal -> (
      match (context.checked.literals.(id), literal) with
      | Some (Integer_value value), _ -> Constructed (Interval (value, value), [])
      | _, Literal_string literal -> Constructed (Text literal.first.value, [])
      | _ -> Wild)

(* A constant as the pattern of its value, so it covers exactly what that
   value does. A value that is not worked out here, such as one built by a
   function call, covers nothing else. *)
and constant ?(seen = []) context type_ path =
  let opaque = Constructed (Opaque_constant path, []) in
  if List.exists (Path.equal path) seen then opaque
  else
    match Query.demand context.database Interface.Constants.value_of path with
    | Some value -> Constructed (Interval (value, value), [])
    | None -> (
        match Interface.Summary.definition context.database path with
        | Some (key, { kind = Constant { value; _ }; _ }) -> (
            match Query.demand context.database Resolve.resolved key with
            | Some resolved -> (
                match constant_value context resolved type_ (path :: seen) value with
                | Some space -> space
                | None -> opaque)
            | None -> opaque)
        | _ -> opaque)

(* A constant's value expression as a space, or [None] if any part of it is
   not a literal, a variant, a record, or another constant. *)
and constant_value context (resolved : Resolve.resolved) type_ seen (value : expression) =
  let recurse = constant_value context resolved in
  let variant_named owner name =
    match type_ with
    | T.Named { path; arguments } when Path.equal path owner -> (
        match Members.variants context.database path arguments with
        | Some variants ->
            List.exists (fun (variant : T.variant) -> variant.variant_name = name) variants
        | None -> false)
    | _ -> false
  in
  (* The constructor a name or member before [(] builds, if any. *)
  let constructor_of (callee : expression) =
    match callee.kind with
    | Name path -> (
        match resolved.names.(path.last.id) with
        | Some (Variant (_, name)) -> Some (Variant name)
        | Some (Definition definition) -> (
            match type_ with
            | T.Named { path; _ } when Path.equal path definition -> Some Record
            | _ -> None)
        | _ -> None)
    | Member ({ kind = Name owner; _ }, member) -> (
        match resolved.names.(owner.last.id) with
        | Some (Definition owner) when variant_named owner member.text -> Some (Variant member.text)
        | _ -> None)
    | _ -> None
  in
  let built constructor (arguments : argument list) =
    let fields = fields_of context type_ constructor in
    let assigned =
      List.mapi
        (fun index (argument : argument) ->
          match (argument.label, argument.value.kind) with
          | Some label, _ -> Some label.text
          | None, Name { modules = []; last }
            when List.exists (fun (field : T.field) -> field.field_name = last.text) fields ->
              Some last.text
          | None, _ ->
              Option.map (fun (field : T.field) -> field.field_name) (List.nth_opt fields index))
        arguments
    in
    (* Every field must be given and worked out; a field left to its
       default is not worked out here. *)
    let parts =
      List.map
        (fun (field : T.field) ->
          match
            List.find_map
              (fun (name, (argument : argument)) ->
                if name = Some field.field_name then Some argument else None)
              (List.combine assigned arguments)
          with
          | Some argument -> recurse field.field_type seen argument.value
          | None -> None)
        fields
    in
    if List.for_all Option.is_some parts then
      Some (Constructed (constructor, List.map Option.get parts))
    else None
  in
  match value.kind with
  | Parenthesized inner -> recurse type_ seen inner
  | True -> Some (Constructed (Boolean true, []))
  | False -> Some (Constructed (Boolean false, []))
  | String { tag = None; rest = []; first; _ } -> Some (Constructed (Text first.value, []))
  | Integer _ | Prefix (Negate, _) | Binary _ -> (
      match Interface.Constants.expression context.database ~visiting:[] resolved value with
      | Some number -> Some (Constructed (Interval (number, number), []))
      | None -> None)
  | Name path -> (
      match resolved.names.(path.last.id) with
      | Some (Variant (_, name)) -> built (Variant name) []
      | Some (Definition definition) -> (
          match constant ~seen context type_ definition with
          | Constructed (Opaque_constant _, _) -> None
          | space -> Some space)
      | _ -> None)
  | Member ({ kind = Name owner; _ }, member) -> (
      match resolved.names.(owner.last.id) with
      | Some (Definition owner) -> (
          if variant_named owner member.text then built (Variant member.text) []
          else
            match constant ~seen context type_ (Member_constant { owner; name = member.text }) with
            | Constructed (Opaque_constant _, _) -> None
            | space -> Some space)
      | _ -> None)
  | Call (callee, arguments) -> (
      match constructor_of callee with
      | Some constructor -> built constructor arguments
      | None -> None)
  | _ -> None

(* A range's end: [Ok] its value, or [Ok None] for an end that failed to
   type, whose error is reported; [Error] a constant whose value is not
   worked out here. *)
and range_end context (written : range_end) =
  match written.kind with
  | End_literal _ -> (
      match context.checked.literals.(written.id) with
      | Some (Integer_value value) -> Ok (Some value)
      | _ -> Ok None)
  | End_name _ | End_constant _ -> (
      match context.checked.patterns.(written.id) with
      | Some (Constant_pattern path) -> (
          match Query.demand context.database Interface.Constants.value_of path with
          | Some value -> Ok (Some value)
          | None -> Error path)
      | _ -> Ok None)

and fielded ?replace context type_ constructor (written : pattern_field list) =
  let fields = fields_of context type_ constructor in
  let bare (inner : pattern) =
    match inner.kind with Binding_or_constant name -> Some name.text | _ -> None
  in
  let assigned =
    List.filter_map
      (fun (field : pattern_field) ->
        match field.kind with
        | Named_field (name, inner) -> Some (name.text, inner)
        | Field inner -> (
            match bare inner with
            | Some name
              when List.exists (fun (declared : T.field) -> declared.field_name = name) fields ->
                Some (name, inner)
            | _ -> ( match fields with [ only ] -> Some (only.field_name, inner) | _ -> None))
        | Rest -> None)
      written
  in
  Constructed
    ( constructor,
      List.map
        (fun (declared : T.field) ->
          match List.assoc_opt declared.field_name assigned with
          | Some inner -> space ?replace context declared.field_type inner
          | None -> Wild)
        fields )

(* Matrices *)

type row = space list

(* The constructors of a type, when there are finitely many to list. *)
let constructors context type_ =
  match type_ with
  | T.Named { path; arguments } -> (
      match Members.shape context.database path with
      | Some (Sum _) -> (
          match Members.variants context.database path arguments with
          | Some variants ->
              Some (List.map (fun (variant : T.variant) -> Variant variant.variant_name) variants)
          | None -> None)
      | Some (Record _) -> Some [ Record ]
      | Some (Builtin_type Bool) -> Some [ Boolean false; Boolean true ]
      | Some (Builtin_type Unit) -> Some [ Record ]
      | _ -> None)
  | _ -> None

(* The column's intervals split at every boundary the column's intervals
   draw, so each part is inside or outside each pattern. *)
let split_intervals (low, high) (column : space list) =
  let rec intervals = function
    | Constructed (Interval (low, high), _) -> [ (low, high) ]
    | Alternatives alternatives -> List.concat_map intervals alternatives
    | _ -> []
  in
  let bounds =
    List.sort_uniq Z.compare
      (low :: Z.succ high
      :: List.concat_map
           (fun (start, stop) -> [ Z.max low start; Z.min (Z.succ high) (Z.succ stop) ])
           (List.concat_map intervals column))
  in
  let rec parts = function
    | first :: (second :: _ as rest) ->
        if Z.lt first second then (first, Z.pred second) :: parts rest else parts rest
    | _ -> []
  in
  List.map (fun (low, high) -> Interval (low, high)) (parts bounds)

let rec head_constructors = function
  | Constructed (constructor, _) -> [ constructor ]
  | Alternatives alternatives -> List.concat_map head_constructors alternatives
  | Wild -> []

(* Whether a pattern's constructor covers a constructor of the split. *)
let covers pattern_constructor constructor =
  match (pattern_constructor, constructor) with
  | Interval (low, high), Interval (part_low, part_high) ->
      Z.leq low part_low && Z.leq part_high high
  | left, right -> left = right

let rec specialize context type_ constructor (rows : row list) =
  let width = arity context type_ constructor in
  List.concat_map
    (fun row ->
      match row with
      | [] -> []
      | Wild :: rest -> [ List.init width (fun _ -> Wild) @ rest ]
      | Constructed (found, arguments) :: rest ->
          if covers found constructor then [ arguments @ rest ] else []
      | Alternatives alternatives :: rest ->
          specialize context type_ constructor
            (List.map (fun alternative -> alternative :: rest) alternatives))
    rows

let rec default_matrix (rows : row list) =
  List.concat_map
    (fun row ->
      match row with
      | Wild :: rest -> [ rest ]
      | Alternatives alternatives :: rest ->
          default_matrix (List.map (fun alternative -> alternative :: rest) alternatives)
      | _ -> [])
    rows

(* The constructors to try for a column: every constructor of a type with
   finitely many, or the intervals of an integer type. [None] for a type
   whose values only a wildcard covers. *)
let signature context type_ (column : space list) =
  match integer_range type_ with
  | Some range -> Some (split_intervals range column)
  | None -> constructors context type_

(* A value the rows miss, as patterns, for one column of each type, or
   [None] if the rows cover every value. *)
let rec missing context (types : T.ty list) (rows : row list) : space list option =
  match types with
  | [] -> if rows = [] then Some [] else None
  | type_ :: rest_types -> (
      let column = List.filter_map (function first :: _ -> Some first | [] -> None) rows in
      let field_types = field_types context type_ in
      let try_constructor constructor =
        let arguments = field_types constructor in
        match
          missing context (arguments @ rest_types) (specialize context type_ constructor rows)
        with
        | Some witness ->
            let count = List.length arguments in
            let fields = List.filteri (fun index _ -> index < count) witness
            and rest = List.filteri (fun index _ -> index >= count) witness in
            Some (Constructed (constructor, fields) :: rest)
        | None -> None
      in
      (* Only when the column's constructors are complete is each one
         tried. Otherwise the rows that start with a wildcard decide, and
         a value the column has no constructor for is the witness, which
         keeps recursive types from being expanded without end. *)
      let present = List.concat_map head_constructors column in
      match (type_, signature context type_ column) with
      | (T.Error _ | T.Hole | T.Never), _ -> None
      | _, Some all
        when all <> []
             && List.for_all
                  (fun constructor -> List.exists (fun found -> covers found constructor) present)
                  all ->
          List.find_map try_constructor all
      | _, signature -> (
          match missing context rest_types (default_matrix rows) with
          | None -> None
          | Some witness -> (
              let absent =
                match signature with
                | Some all ->
                    List.find_opt
                      (fun constructor ->
                        not (List.exists (fun found -> covers found constructor) present))
                      all
                | None -> None
              in
              match absent with
              | Some constructor when present <> [] ->
                  let count = List.length (field_types constructor) in
                  Some (Constructed (constructor, List.init count (fun _ -> Wild)) :: witness)
              | _ -> Some (Wild :: witness))))

(* Whether a row is useful after the rows before it: whether some value it
   matches matches none of them. *)
let useful context types rows (row : row) =
  let rec go (types : T.ty list) (rows : row list) (row : row) =
    match (types, row) with
    | [], [] -> rows = []
    | type_ :: rest_types, first :: rest -> (
        let field_types = field_types context type_ in
        match first with
        | Alternatives alternatives ->
            List.exists (fun alternative -> go types rows (alternative :: rest)) alternatives
        | Constructed (constructor, arguments) -> (
            match (constructor, integer_range type_) with
            | Interval _, Some range ->
                (* An interval is useful if any part of it is. *)
                List.exists
                  (fun part ->
                    covers constructor part
                    && go rest_types (specialize context type_ part rows) rest)
                  (split_intervals range
                     (first
                     :: List.filter_map (function first :: _ -> Some first | [] -> None) rows))
            | _ ->
                go
                  (field_types constructor @ rest_types)
                  (specialize context type_ constructor rows)
                  (arguments @ rest))
        | Wild -> (
            let column = List.filter_map (function first :: _ -> Some first | [] -> None) rows in
            match signature context type_ column with
            | Some all
              when all <> []
                   && List.for_all
                        (fun constructor ->
                          List.exists
                            (fun found -> covers found constructor)
                            (List.concat_map head_constructors column))
                        all ->
                List.exists
                  (fun constructor ->
                    go
                      (field_types constructor @ rest_types)
                      (specialize context type_ constructor rows)
                      (List.init (List.length (field_types constructor)) (fun _ -> Wild) @ rest))
                  all
            | _ -> go rest_types (default_matrix rows) rest))
    | _ -> false
  in
  go types rows row

(* Showing a missing value as a pattern *)

let rec show context type_ (pattern : space) =
  match pattern with
  | Wild | Alternatives [] -> "_"
  | Alternatives (first :: _) -> show context type_ first
  | Constructed (Boolean value, _) -> if value then "true" else "false"
  | Constructed (Interval (low, high), _) when integer_range type_ = Some (low, high) -> "_"
  | Constructed (Interval (low, high), _) ->
      if Z.equal low high then Z.to_string low
      else Printf.sprintf "%s..=%s" (Z.to_string low) (Z.to_string high)
  | Constructed (Text text, _) -> Printf.sprintf "%S" text
  | Constructed (Opaque_constant path, _) -> Path.show path
  | Constructed (constructor, arguments) -> (
      let fields = fields_of context type_ constructor in
      let shown =
        List.map2
          (fun (field : T.field) argument -> show context field.field_type argument)
          fields
          (if List.length arguments = List.length fields then arguments
           else List.map (fun _ -> Wild) fields)
      in
      let name = match constructor with Variant name -> name | _ -> "" in
      match (fields, shown) with
      | [], _ -> if name = "" then "()" else name
      | [ _ ], [ "_" ] -> if name = "" then "_" else Printf.sprintf "%s(_)" name
      | _, _ when List.for_all (fun shown -> shown = "_") shown ->
          if name = "" then "_" else Printf.sprintf "%s(..)" name
      | [ _ ], [ only ] -> Printf.sprintf "%s(%s)" name only
      | _ ->
          Printf.sprintf "%s(%s)" name
            (String.concat ", "
               (List.map2
                  (fun (field : T.field) shown ->
                    if shown = "_" then field.field_name ^ ": _"
                    else field.field_name ^ ": " ^ shown)
                  fields shown)))

let show_row context types row = String.concat ", " (List.map2 (show context) types row)

(* Checking *)

let type_of context (value : expression) = Checked.type_of context.checked value

(* Whether a type, or a type it is built from, failed to check or parse:
   matching on it is accepted silently, since its error is reported where it
   is written. *)
let has_error context type_ =
  let rec go seen = function
    | T.Error _ | T.Hole -> true
    | T.Named { path; arguments } -> (
        List.exists (function T.Type type_ -> go seen type_ | _ -> false) arguments
        || (not (List.exists (Path.equal path) seen))
           &&
           let seen = path :: seen in
           let fields_fail fields =
             List.exists (fun (field : T.field) -> go seen field.field_type) fields
           in
           match Members.shape context.database path with
           | Some (Error_shape _) -> true
           | Some (Record _) ->
               fields_fail
                 (Option.value ~default:[] (Members.fields context.database path arguments))
           | Some (Sum _) -> (
               match Members.variants context.database path arguments with
               | Some variants ->
                   List.exists
                     (fun (variant : T.variant) ->
                       fields_fail (Option.value ~default:[] variant.fields))
                     variants
               | None -> false)
           | _ -> false)
    | _ -> false
  in
  go [] type_

let indentation text (position : int) =
  let line_start = Source.line_start (Source.create ~path:"" text) position in
  let rec spaces index =
    if index < String.length text && (text.[index] = ' ' || text.[index] = '\t') then
      spaces (index + 1)
    else index
  in
  String.sub text line_start (spaces line_start - line_start)

(* The or-patterns in a pattern, at any depth, each with its alternatives. *)
let rec or_patterns (written : pattern) =
  match written.kind with
  | Alternatives alternatives -> (written, alternatives) :: List.concat_map or_patterns alternatives
  | Variant { fields = Some fields; _ } | Record fields ->
      List.concat_map
        (fun (field : pattern_field) ->
          match field.kind with
          | Named_field (_, inner) | Field inner -> or_patterns inner
          | Rest -> [])
        fields
  | _ -> []

(* How many missing cases a [match]'s fix adds arms for. *)
let witness_limit = 8

let check_match context ~text (value : expression) scrutinees (arms : arm list) =
  let types = List.map (fun scrutinee -> type_of context scrutinee) scrutinees in
  if not (List.exists (has_error context) types) then begin
    let rows = ref [] in
    List.iter
      (fun (arm : arm) ->
        if List.length arm.patterns = List.length types then begin
          let row = List.map2 (space context) types arm.patterns in
          (* An or-pattern's alternative the ones before it cover is
             unreachable, as is an arm earlier arms cover. *)
          let reachable = useful context types !rows row in
          if not reachable then
            report context Unreachable_arm arm.span
              ~fixes:
                [
                  Diagnostic.fix "Delete the arm."
                    [
                      Diagnostic.delete
                        (Source.span
                           (arm.span.start - String.length (indentation text arm.span.start) - 1)
                           arm.span.stop);
                    ];
                ]
              "Earlier arms already match everything this arm matches, so it is never reached."
          else
            (* Each alternative, at any depth, against the arms before and
               the alternatives before it. *)
            List.iter
              (fun ((group : pattern), alternatives) ->
                List.iteri
                  (fun index (alternative : pattern) ->
                    let row_with only =
                      List.map2 (space ~replace:(group.id, only) context) types arm.patterns
                    in
                    let before = List.filteri (fun other _ -> other < index) alternatives in
                    let prior = if before = [] then !rows else !rows @ [ row_with before ] in
                    if not (useful context types prior (row_with [ alternative ])) then
                      let deleted =
                        match if index > 0 then List.nth_opt alternatives (index - 1) else None with
                        | Some previous -> Source.span previous.span.stop alternative.span.stop
                        | None -> (
                            match List.nth_opt alternatives 1 with
                            | Some next -> Source.span alternative.span.start next.span.start
                            | None -> Source.span alternative.span.start alternative.span.stop)
                      in
                      report context Unreachable_alternative alternative.span
                        ~fixes:
                          [ Diagnostic.fix "Delete the alternative." [ Diagnostic.delete deleted ] ]
                        (if before = [] then
                           "Earlier arms already match everything this alternative matches."
                         else
                           "The alternatives before this one already match everything it matches."))
                  alternatives)
              (List.concat_map or_patterns arm.patterns);
          if Option.is_none arm.guard then rows := !rows @ [ row ]
        end)
      arms;
    (* The cases no arm covers, one witness after another, so the fix can
       add an arm for each. *)
    let rec witnesses rows found =
      if List.length found >= witness_limit then List.rev found
      else
        match missing context types rows with
        | Some witness -> witnesses (rows @ [ witness ]) (witness :: found)
        | None -> List.rev found
    in
    match witnesses !rows [] with
    | [] -> ()
    | first :: _ as all ->
        let fixes =
          match List.rev arms with
          | last :: _ ->
              let indent = indentation text last.span.start in
              [
                Diagnostic.fix "Add an arm for each missing case."
                  [
                    Diagnostic.insert last.span.stop
                      (String.concat ""
                         (List.map
                            (fun witness ->
                              "\n" ^ indent ^ show_row context types witness ^ " => todo")
                            all));
                  ];
              ]
          | [] -> []
        in
        report context Not_covered value.span ~fixes
          (Printf.sprintf "This `match` does not cover every case: `%s` is not covered%s."
             (show_row context types first)
             (match List.length all with
             | 1 -> ""
             | count when count >= witness_limit -> ", nor others"
             | count -> Printf.sprintf ", nor %d others" (count - 1)))
  end

(* A pattern in a [let], a [for], or a lambda's parameters must cover its
   type alone. *)
let check_irrefutable context (written : pattern) =
  let type_ = Checked.pattern_type context.checked written in
  if not (has_error context type_) then
    match missing context [ type_ ] [ [ space context type_ written ] ] with
    | Some witness ->
        report context Refutable written.span
          (Printf.sprintf
             "This pattern can fail: it does not match `%s`. Use `match`, an `is` test, or `let \
              ... else`."
             (show context type_ (List.hd witness)))
    | None -> ()

let check_definition context ~text (definition : definition) =
  let rec expression (value : expression) =
    (match value.kind with
    | Match { scrutinees; arms } -> check_match context ~text value scrutinees arms
    | Lambda { parameters; _ } -> List.iter (check_irrefutable context) parameters
    | _ -> ());
    Syntax_walk.expression_parts ~expression ~statement value
  and statement (written : statement) =
    (match written.kind with
    | Let { pattern; else_ = None; _ } | For { pattern; _ } -> check_irrefutable context pattern
    | _ -> ());
    Syntax_walk.statement_parts ~expression ~statement written
  in
  Syntax_walk.definition ~statement expression definition

let definition_diagnostics =
  Query.query ~name:"pattern_diagnostics" ~phase:Bodies ~saved:true ~show:Resolve.Names.show_key
    (fun database key ->
      match
        ( Query.demand database Resolve.Names.definition key,
          Infer.clean database key,
          Query.demand database Resolve.Names.text key )
      with
      | Some definition, Some checked, Some text ->
          let context = { database; package = key.module_.package; checked; diagnostics = [] } in
          check_definition context ~text definition;
          List.sort
            (fun (left : Diagnostic.t) (right : Diagnostic.t) -> compare left.span right.span)
            context.diagnostics
      | _ -> [])

let diagnostics database module_ =
  Resolve.Names.per_definition database module_ (Query.demand database definition_diagnostics)
