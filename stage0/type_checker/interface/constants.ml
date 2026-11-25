type value = Constant_value.t =
  | Integer of Z.t
  | Boolean of bool
  | Text of string
  | Constructed of { type_ : Path.t; variant : string option; fields : (string * value) list }

type outcome = Constant_value.outcome =
  | Known of value
  | Calls_function
  | Depends_on_itself
  | Unevaluated

type integer = { bits : int; is_signed : bool }

let ( let* ) outcome continue =
  match outcome with
  | Known value -> continue value
  | (Calls_function | Depends_on_itself | Unevaluated) as stopped -> stopped

let find_builtin_type (resolved : Resolve.resolved) (name : Syntax.name) =
  match resolved.names.(name.id) with
  | Some (Definition (Type, path)) -> Well_known.find_builtin_type path
  | _ -> None

let find_integer resolved (written : Syntax.type_expression) =
  match written.kind with
  | Path_type { path; arguments = []; _ } ->
      Option.bind (find_builtin_type resolved path.last) (fun builtin ->
          Option.map
            (fun (bits, is_signed) -> { bits; is_signed })
            (Types.find_integer_bits
               (Types.make_named (Well_known.make_builtin_type_path builtin) [])))
  | _ -> None

let fits (resolved : Resolve.resolved) (written : Syntax.type_expression) value =
  match written.kind with
  | Path_type { path; _ } -> (
      match (resolved.names.(path.last.id), value) with
      | Some (Type_parameter _), _ -> true
      | Some (Definition (Type, type_)), Integer _ -> (
          match Well_known.find_builtin_type type_ with
          | Some Character -> true
          | Some builtin ->
              Types.find_integer_bits
                (Types.make_named (Well_known.make_builtin_type_path builtin) [])
              <> None
          | None -> false)
      | Some (Definition (Type, type_)), Boolean _ ->
          Path.equal type_ (Well_known.make_builtin_type_path Bool)
      | Some (Definition (Type, type_)), Text _ -> Path.equal type_ (Well_known.make_path String)
      | Some (Definition (Type, type_)), Constructed constructed ->
          Path.equal type_ constructed.type_
      | _ -> false)
  | Self_type _ | Associated _ | Function_type _ | View_type _ | Type_error -> false

let complement integer value =
  if integer.is_signed then Z.lognot value
  else Z.logxor value (Z.pred (Z.shift_left Z.one integer.bits))

let compare_values (comparison : Language.Comparison.t) left right =
  let ordered = Z.compare left right in
  match comparison with
  | Equal -> ordered = 0
  | Not_equal -> ordered <> 0
  | Less -> ordered < 0
  | Less_equal -> ordered <= 0
  | Greater -> ordered > 0
  | Greater_equal -> ordered >= 0

let apply_arithmetic (arithmetic : Syntax.arithmetic) left right =
  match arithmetic with
  | Add -> Known (Integer (Z.add left right))
  | Subtract -> Known (Integer (Z.sub left right))
  | Multiply -> Known (Integer (Z.mul left right))
  | Divide -> if Z.equal right Z.zero then Unevaluated else Known (Integer (Z.div left right))
  | Remainder -> if Z.equal right Z.zero then Unevaluated else Known (Integer (Z.rem left right))

let apply_bitwise (bitwise : Syntax.bitwise) left right =
  match bitwise with
  | Bit_and -> Z.logand left right
  | Bit_or -> Z.logor left right
  | Bit_xor -> Z.logxor left right

let stop_at_operator = function
  | Text _ | Constructed _ -> Calls_function
  | Integer _ | Boolean _ -> Unevaluated

type scope = { lookups : Lookups.t; visiting : Path.t list; resolved : Resolve.resolved }

let rec evaluate scope ~integer (expression : Syntax.expression) : outcome =
  match expression.kind with
  | Integer value -> Known (Integer value)
  | True -> Known (Boolean true)
  | False -> Known (Boolean false)
  | String literal -> evaluate_string scope literal
  | Parenthesized inner -> evaluate scope ~integer inner
  | Prefix (prefix, inner) -> (
      let* value = evaluate scope ~integer inner in
      match (prefix, value, integer) with
      | Negate, Integer value, _ -> Known (Integer (Z.neg value))
      | Not, Boolean value, _ -> Known (Boolean (not value))
      | Complement, Integer value, Some integer -> Known (Integer (complement integer value))
      | _, value, _ -> stop_at_operator value)
  | Binary { operator; left; right; _ } -> evaluate_binary scope ~integer operator left right
  | Name _ | Member _ -> evaluate_name scope expression
  | Bracket (base, _) when scope.resolved.brackets.(expression.id) = Some Type_arguments ->
      evaluate scope ~integer base
  | Call (callee, arguments) -> evaluate_call scope callee arguments
  | Bracket _ | Quantified _ | Range _ | List _ | Map _ -> Calls_function
  | Float _ | Todo | Unreachable | Break | Continue | Self_value | Self_type_value | Try _ | With _
  | Mode _ | Is _ | Echo _ | Return _ | Lambda _ | If _ | Match _ | Provide _ | Block _
  | Expression_error ->
      Unevaluated

and evaluate_string scope (literal : Syntax.string_literal) =
  match (literal.tag, literal.rest) with
  | None, [] -> Known (Text literal.first.value)
  | None, _ :: _ -> Calls_function
  | Some tag, rest -> (
      match (find_builtin_type scope.resolved tag.last, rest) with
      | Some ((Character | UInt8) as builtin), [] -> (
          match Language.Builtin_type.find_scalar_literal builtin literal.first.value with
          | Some scalar -> Known (Integer (Z.of_int scalar))
          | None -> Unevaluated)
      | _ -> Calls_function)

and evaluate_binary scope ~integer (operator : Syntax.binary) left right =
  match operator with
  | Connective connective -> (
      let* left = evaluate scope ~integer:None left in
      match (connective, left) with
      | And, Boolean false -> Known (Boolean false)
      | Or, Boolean true -> Known (Boolean true)
      | Implies, Boolean false -> Known (Boolean true)
      | (And | Or | Implies), Boolean _ -> (
          let* right = evaluate scope ~integer:None right in
          match right with Boolean _ -> Known right | value -> stop_at_operator value)
      | _, value -> stop_at_operator value)
  | Comparison comparison -> (
      let* left = evaluate scope ~integer:None left in
      let* right = evaluate scope ~integer:None right in
      match (comparison, left, right) with
      | _, Integer left, Integer right -> Known (Boolean (compare_values comparison left right))
      | Equal, Boolean left, Boolean right -> Known (Boolean (left = right))
      | Not_equal, Boolean left, Boolean right -> Known (Boolean (left <> right))
      | _, value, _ -> stop_at_operator value)
  | Operation operation -> (
      let* left = evaluate scope ~integer left in
      let* right =
        evaluate scope ~integer:(match operation with Shift _ -> None | _ -> integer) right
      in
      match (operation, left, right, integer) with
      | Arithmetic arithmetic, Integer left, Integer right, _ ->
          apply_arithmetic arithmetic left right
      | Bitwise bitwise, Integer left, Integer right, _ ->
          Known (Integer (apply_bitwise bitwise left right))
      | Shift shift, Integer value, Integer amount, Some integer ->
          if Z.sign amount < 0 || Z.geq amount (Z.of_int integer.bits) then Unevaluated
          else
            Known
              (Integer
                 (match shift with
                 | Shift_left -> Z.shift_left value (Z.to_int amount)
                 | Shift_right -> Z.shift_right value (Z.to_int amount)))
      | _, value, _, _ -> stop_at_operator value)

and evaluate_name scope (expression : Syntax.expression) =
  match (Resolve.find_head scope.resolved expression, expression.kind) with
  | Some { target = Definition (Constant, path); _ }, _ ->
      evaluate_path scope.lookups ~visiting:scope.visiting path
  | Some { target = Variant (type_, variant); _ }, _ -> construct_variant scope type_ variant
  | None, Member (base, member) -> (
      match (Resolve.find_head scope.resolved base, member.case) with
      | Some { target = Definition (Type, type_); _ }, Upper ->
          construct_variant scope type_ member.text
      | Some { target = Definition (Type, owner); _ }, Lower ->
          evaluate_path scope.lookups ~visiting:scope.visiting
            (Member_constant { owner; name = member.text })
      | _ -> (
          let* base = evaluate scope ~integer:None base in
          match base with
          | Constructed { fields; _ } -> (
              match List.assoc_opt member.text fields with
              | Some field -> Known field
              | None -> Unevaluated)
          | Integer _ | Boolean _ | Text _ -> Unevaluated))
  | _ -> Unevaluated

and construct_variant scope type_ variant =
  match find_constructor_fields scope.lookups type_ (Some variant) with
  | Some ([], _) -> Known (Constructed { type_; variant = Some variant; fields = [] })
  | Some (_ :: _, _) | None -> Unevaluated

and evaluate_call scope callee arguments =
  match (Resolve.find_head scope.resolved callee, callee.kind) with
  | Some { target = Definition (Type, type_); _ }, _ -> construct scope type_ None arguments
  | Some { target = Variant (type_, variant); _ }, _ ->
      construct scope type_ (Some variant) arguments
  | None, Member (base, ({ case = Upper; _ } as variant)) -> (
      match Resolve.find_head scope.resolved base with
      | Some { target = Definition (Type, type_); _ } ->
          construct scope type_ (Some variant.text) arguments
      | _ -> Calls_function)
  | _ -> Calls_function

and construct scope type_ variant (arguments : Syntax.argument list) =
  match find_constructor_fields scope.lookups type_ variant with
  | None -> Unevaluated
  | Some (declared, type_key) ->
      let field_types = scope.lookups.read_resolved Interface type_key in
      let find_argument position (field : Syntax.name) =
        List.find_opt
          (fun (index, (argument : Syntax.argument)) ->
            match argument.label with
            | Some label -> label.text = field.text
            | None -> index = position)
          (List.mapi (fun index argument -> (index, argument)) arguments)
      in
      let rec build position fields = function
        | [] -> Known (Constructed { type_; variant; fields = List.rev fields })
        | (name, written, default) :: rest -> (
            let integer = find_integer field_types written in
            let field =
              match (find_argument position name, default) with
              | Some (_, argument), _ -> evaluate scope ~integer argument.value
              | None, Some default ->
                  let path = Path.Default { owner = type_; variant; name = name.text } in
                  if List.exists (Path.equal path) scope.visiting then Depends_on_itself
                  else
                    evaluate
                      {
                        scope with
                        visiting = path :: scope.visiting;
                        resolved = scope.lookups.read_resolved Contract type_key;
                      }
                      ~integer default
              | None, None -> Unevaluated
            in
            match field with
            | Known value when fits field_types written value ->
                build (position + 1) ((name.text, value) :: fields) rest
            | Known _ -> Unevaluated
            | (Calls_function | Depends_on_itself | Unevaluated) as stopped -> stopped)
      in
      build 0 [] declared

and find_constructor_fields (lookups : Lookups.t) type_ variant =
  match Resolve.Names.find_definition lookups.names type_ with
  | Some (key, { kind = Type_definition { body; _ }; _ }) -> (
      let list_declared (fields : Syntax.field list) =
        List.filter_map
          (fun (field : Syntax.field) ->
            match field.kind with
            | Field_declaration { name; type_; default } -> Some (name, type_, default)
            | Field_error -> None)
          fields
      in
      match (body, variant) with
      | Fields fields, None -> Some (list_declared fields, key)
      | Variants variants, Some name -> (
          match
            List.find_opt (fun (declared : Syntax.variant) -> declared.name.text = name) variants
          with
          | Some { fields; _ } -> Some (list_declared (Option.value fields ~default:[]), key)
          | None -> None)
      | (Fields _ | Variants _ | Type_todo), _ -> None)
  | _ -> None

and evaluate_path lookups ~visiting path =
  if List.exists (Path.equal path) visiting then Depends_on_itself
  else
    match Resolve.Names.find_definition lookups.names path with
    | Some (key, { kind = Constant { value; type_; _ }; _ }) -> (
        let declared = lookups.read_resolved Interface key in
        match
          evaluate
            { lookups; visiting = path :: visiting; resolved = lookups.read_resolved Body key }
            ~integer:(find_integer declared type_) value
        with
        | Known value when not (fits declared type_ value) -> Unevaluated
        | outcome -> outcome)
    | _ -> Unevaluated

let evaluate_expression lookups resolved ~integer expression =
  evaluate { lookups; visiting = []; resolved } ~integer expression

let evaluate_constant lookups path = evaluate_path lookups ~visiting:[] path

let is_uint64 (lookups : Lookups.t) path =
  match Resolve.Names.find_definition lookups.names path with
  | Some (key, { kind = Constant { type_ = { kind = Path_type written; _ }; _ }; _ }) ->
      (lookups.read_resolved Interface key).names.(written.path.last.id)
      = Some (Definition (Type, Well_known.make_builtin_type_path UInt64))
  | _ -> false

type count = Count of Z.t | Invalid_count of Catalog.Typing.count_error | Unevaluated_count

let evaluate_count (lookups : Lookups.t) path =
  if not (is_uint64 lookups path) then Invalid_count Not_uint64
  else
    match lookups.find_constant_value path with
    | Known (Integer value) when Z.sign value >= 0 && Z.numbits value <= 64 -> Count value
    | Calls_function -> Invalid_count Computed_by_call
    | Depends_on_itself -> Invalid_count Computed_from_itself
    | Known _ | Unevaluated -> Unevaluated_count
