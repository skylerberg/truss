(* Exhaustiveness and reachability, by Maranget's usefulness algorithm
   ("Warnings for pattern matching", 2007), over the matched values as a
   vector, so a [match] over several values is checked as one. See
   TYPECHECKER.md, "Exhaustiveness and reachability".

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
  database : Query.database;
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

let arity context type_ constructor = List.length (fields_of context type_ constructor)

(* A written pattern as a space, its fields put in declared order, with
   fields it does not name as wildcards. *)
let rec space context type_ (written : pattern) : space =
  match written.kind with
  | Wildcard | Pattern_error -> Wild
  | Binding_or_constant _ -> (
      match context.checked.patterns.(written.id) with
      | Some (Constant_pattern path) -> constant context path
      | _ -> Wild)
  | Qualified_constant _ -> Wild
  | Literal literal -> literal_space literal
  | Pattern_range { start; stop; inclusive } -> (
      match (range_end context start, range_end context stop) with
      | Some low, Some high ->
          let high = if inclusive then high else Z.pred high in
          if Z.gt low high then Alternatives [] else Constructed (Interval (low, high), [])
      | _ -> Wild)
  | Variant { name; fields } ->
      fielded context type_ (Variant name.last.text) (Option.value ~default:[] fields)
  | Record fields -> fielded context type_ Record fields
  | Alternatives alternatives -> Alternatives (List.map (space context type_) alternatives)

and literal_space = function
  | Literal_integer value -> Constructed (Interval (value, value), [])
  | Literal_true -> Constructed (Boolean true, [])
  | Literal_false -> Constructed (Boolean false, [])
  | Literal_string literal -> Constructed (Text literal.first.value, [])

and constant context path =
  match Query.demand context.database Interface.Constants.value_of path with
  | Some value -> Constructed (Interval (value, value), [])
  | None -> Constructed (Opaque_constant path, [])

and range_end context (written : range_end) =
  match written.kind with
  | End_literal (Literal_integer value) -> Some value
  | End_literal _ -> None
  | End_name _ | End_constant _ -> (
      match context.checked.patterns.(written.id) with
      | Some (Constant_pattern path) ->
          Query.demand context.database Interface.Constants.value_of path
      | _ -> None)

and fielded context type_ constructor (written : pattern_field list) =
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
          | Some inner -> space context declared.field_type inner
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
  let width =
    match constructor with
    | Interval _ | Boolean _ | Text _ | Opaque_constant _ -> 0
    | _ -> arity context type_ constructor
  in
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
      let field_types constructor =
        List.map (fun (field : T.field) -> field.field_type) (fields_of context type_ constructor)
      in
      let try_constructor constructor =
        let arguments =
          match constructor with
          | Interval _ | Boolean _ | Text _ | Opaque_constant _ -> []
          | _ -> field_types constructor
        in
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
      | (T.Error | T.Hole | T.Never), _ -> None
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
                  let count =
                    match constructor with
                    | Interval _ | Boolean _ | Text _ | Opaque_constant _ -> 0
                    | _ -> List.length (field_types constructor)
                  in
                  Some (Constructed (constructor, List.init count (fun _ -> Wild)) :: witness)
              | _ -> Some (Wild :: witness))))

(* Whether a row is useful after the rows before it: whether some value it
   matches matches none of them. *)
let useful context types rows (row : row) =
  let rec go (types : T.ty list) (rows : row list) (row : row) =
    match (types, row) with
    | [], [] -> rows = []
    | type_ :: rest_types, first :: rest -> (
        let field_types constructor =
          match constructor with
          | Interval _ | Boolean _ | Text _ | Opaque_constant _ -> []
          | _ ->
              List.map
                (fun (field : T.field) -> field.field_type)
                (fields_of context type_ constructor)
        in
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

let type_of context (value : expression) =
  Option.value ~default:T.Error context.checked.types.(value.id)

let has_error type_ =
  let rec go = function
    | T.Error | T.Hole -> true
    | T.Named { arguments; _ } ->
        List.exists (function T.Type type_ -> go type_ | _ -> false) arguments
    | _ -> false
  in
  go type_

let indentation text (position : int) =
  let rec start index =
    if index > 0 && text.[index - 1] <> '\n' then start (index - 1) else index
  in
  let line_start = start position in
  let rec spaces index =
    if index < String.length text && (text.[index] = ' ' || text.[index] = '\t') then
      spaces (index + 1)
    else index
  in
  String.sub text line_start (spaces line_start - line_start)

let check_match context ~text (value : expression) scrutinees (arms : arm list) =
  let types = List.map (fun scrutinee -> type_of context scrutinee) scrutinees in
  if not (List.exists has_error types) then begin
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
            List.iteri
              (fun position (written : pattern) ->
                match written.kind with
                | Alternatives alternatives ->
                    ignore
                      (List.fold_left
                         (fun (seen, index) (alternative : pattern) ->
                           let before =
                             List.mapi
                               (fun other written ->
                                 if other = position then Wild
                                 else space context (List.nth types other) written)
                               arm.patterns
                           in
                           let alternative_row =
                             List.mapi
                               (fun other existing ->
                                 if other = position then
                                   space context (List.nth types position) alternative
                                 else existing)
                               before
                           in
                           let prior =
                             !rows
                             @ List.map
                                 (fun seen_space ->
                                   List.mapi
                                     (fun other existing ->
                                       if other = position then seen_space else existing)
                                     before)
                                 seen
                           in
                           if index > 0 && not (useful context types prior alternative_row) then begin
                             let previous = List.nth alternatives (index - 1) in
                             report context Unreachable_alternative alternative.span
                               ~fixes:
                                 [
                                   Diagnostic.fix "Delete the alternative."
                                     [
                                       Diagnostic.delete
                                         (Source.span previous.span.stop alternative.span.stop);
                                     ];
                                 ]
                               "The alternatives before this one already match everything it \
                                matches."
                           end;
                           ( seen @ [ space context (List.nth types position) alternative ],
                             index + 1 ))
                         ([], 0) alternatives)
                | _ -> ())
              arm.patterns;
          if Option.is_none arm.guard then rows := !rows @ [ row ]
        end)
      arms;
    (* The cases no arm covers, one witness after another, so the fix can
       add an arm for each. *)
    let rec witnesses rows found =
      if List.length found >= 8 then List.rev found
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
             | count -> Printf.sprintf ", nor %d others" (count - 1)))
  end

(* A pattern in a [let], a [for], or a lambda's parameters must cover its
   type alone. *)
let check_irrefutable context (written : pattern) =
  let type_ = Option.value ~default:T.Error context.checked.pattern_types.(written.id) in
  if not (has_error type_) then
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

let diagnostics =
  Query.query ~name:"pattern_diagnostics" ~show:Resolve.Names.show_key (fun database key ->
      match
        ( Query.demand database Resolve.Names.definition key,
          Query.demand database Infer.checked key,
          Query.demand database Resolve.Names.text key )
      with
      | Some definition, Some result, Some text ->
          let context =
            { database; package = key.module_.package; checked = result.checked; diagnostics = [] }
          in
          check_definition context ~text definition;
          List.sort
            (fun (left : Diagnostic.t) (right : Diagnostic.t) -> compare left.span right.span)
            context.diagnostics
      | _ -> [])

let file_diagnostics database module_ =
  List.concat_map
    (fun (declaration : Resolve.Names.declaration) ->
      let key = Resolve.Names.key_of declaration in
      match Query.demand database Resolve.Names.base key with
      | Some (_, base) -> List.map (Diagnostic.move base) (Query.demand database diagnostics key)
      | None -> [])
    (Query.demand database Resolve.Names.declarations module_)
  |> List.sort (fun (left : Diagnostic.t) (right : Diagnostic.t) -> compare left.span right.span)
