let raise_bug format = Compiler_bug.raise_bug ~stage:"Infer" format

type counters = { mutable next_node_id : int; mutable next_synthetic_local : int }

type t = {
  lookups : Lookups.t;
  resolved : Resolve.resolved;
  tables : Tables.t;
  tables_with_holes : Tables.t option;
  context : Interface.Elaborator.t;
  law_parameters : (string * Types.ty) list;
  package : Path.package;
  text : string Lazy.t;
  counters : counters;
}

type env = { output : Types.result option; self : Types.ty option }

let read_span form id = Interface.Elaborator.read_span form.context id
let quote form id = Source.Definition_span.quote (Lazy.force form.text) (read_span form id)

let allocate_node_id form =
  let id = form.counters.next_node_id in
  form.counters.next_node_id <- id + 1;
  id

let allocate_synthetic_local form : Core.local =
  let number = form.counters.next_synthetic_local in
  form.counters.next_synthetic_local <- number + 1;
  Synthetic number

let make_synthetic_expression form ~origin type_ kind : Core.expression =
  { id = allocate_node_id form; origin; type_; kind }

let make_pattern form ~origin type_ kind : Core.pattern =
  { id = allocate_node_id form; origin; type_; kind }

let make_statement form ~origin kind : Core.statement = { id = allocate_node_id form; origin; kind }

let make_local_use form ~origin type_ local =
  make_synthetic_expression form ~origin type_ (Use (Local { local; type_; origin }))

let make_binding_match ~origin scrutinee pattern body : Core.kind =
  Match
    {
      scrutinees = [ scrutinee ];
      arms = [ { patterns = [ pattern ]; guard = None; body; origin } ];
    }

let is_written_expression (written : Syntax.expression) (kind : Core.kind) =
  match (kind, written.kind) with
  | Match _, Match _ | Call _, Call _ | Lambda _, Lambda _ | If _, If _ | Return _, Return _ -> true
  | (Match _ | Call _ | Lambda _ | If _ | Return _), _ -> false
  | _ -> true

let compute_expression_origin (written : Syntax.expression) kind : Core.origin =
  if is_written_expression written kind then Written written.id
  else
    Desugared
      {
        construct = written.id;
        desugaring =
          (match written.kind with Try _ -> Try | Quantified _ -> Quantifier | _ -> Rewrite);
      }

let make_rewrite_origin (construct : Syntax.id) : Core.origin =
  Desugared { construct; desugaring = Rewrite }

let rewrite_origin : Core.origin -> Core.origin = function
  | Written construct -> make_rewrite_origin construct
  | Desugared _ as origin -> origin

let make_place (node : Core.expression) : Core.place =
  match node.kind with Use place -> place | _ -> Temporary node

let list_bounds form = Interface.Elaborator.list_bounds form.context

let with_condition form condition =
  { form with context = Interface.Elaborator.add_condition form.context condition }

let normalize form type_ =
  Interface.Impls.normalize form.lookups.interface ~list_bounds:(list_bounds form) type_

let find_evidence form type_ trait =
  Interface.Impls.find_evidence form.lookups.interface ~list_bounds:(list_bounds form)
    (normalize form type_)
    (Types.map_trait (normalize form) trait)

let make_callee form (target : Core.operand Core.target) =
  Callee_uses.make_callee form.lookups.interface ~list_bounds:(list_bounds form) target

let make_call form ~callee ~arguments ~lends =
  Callee_uses.make_call form.lookups.interface ~list_bounds:(list_bounds form) ~callee ~arguments
    ~lends

let is_plain form type_ =
  Interface.Impls.is_plain form.lookups.interface ~list_bounds:(list_bounds form) type_

let binding_may_alias form mode type_ =
  Interface.Impls.binding_may_alias form.lookups.interface ~list_bounds:(list_bounds form) mode
    type_

let make_binding form ~origin ~is_var ~mode type_ local =
  make_pattern form ~origin type_
    (Bind { local; is_var; mode; may_alias = binding_may_alias form mode type_ })

let is_within form type_ set =
  match
    match type_ with
    | Types.Parameter _ | Projection _ ->
        Interface.Properties.list_rigid_members form.lookups.interface
          ~list_bounds:(list_bounds form) type_
    | _ -> Types.list_scalar_members type_
  with
  | [] -> false
  | members -> List.for_all (fun member -> List.mem member set) members

let decide_binding_mode form (mode : Language.Mode.t) type_ : Language.Mode.t =
  match mode with Read when is_plain form type_ -> Own | Read | Mut | Own -> mode

let rec copy_plain_bindings form (pattern : Core.pattern) : Core.pattern =
  let copy_fields = List.map (fun (field, inner) -> (field, copy_plain_bindings form inner)) in
  match pattern.kind with
  | Bind bound ->
      let mode = decide_binding_mode form bound.mode pattern.type_ in
      { pattern with kind = Bind { bound with mode } }
  | Variant { variant; fields } ->
      { pattern with kind = Variant { variant; fields = copy_fields fields } }
  | Record fields -> { pattern with kind = Record (copy_fields fields) }
  | Alternatives alternatives ->
      { pattern with kind = Alternatives (List.map (copy_plain_bindings form) alternatives) }
  | Wildcard | Literal _ | Range _ | Equal_to _ -> pattern

let make_range form ~origin (base : Core.place) ~start ~stop ~inclusive : Core.kind =
  let make = make_synthetic_expression form ~origin in
  let base_type = Core_walk.compute_place_type base in
  let element =
    match base_type with
    | Types.Named { arguments = Types.Type element :: _; _ } -> element
    | type_ -> raise_bug "a range of `%s`" (Types.show type_)
  in
  let bound_type, path =
    match Types.find_specification_sequence_element base_type with
    | Some _ -> (Types.Integer, Well_known.make_path Sequence)
    | None -> (Types.make_builtin UInt64, Well_known.make_path Slice)
  in
  let stop =
    Option.map
      (fun stop ->
        if inclusive then
          make bound_type
            (Operator { operation = Add; arguments = [ stop; make bound_type (Integer Z.one) ] })
        else stop)
      stop
  in
  Use
    (Range
       {
         id = allocate_node_id form;
         base;
         start = (match start with Some start -> start | None -> make bound_type (Integer Z.zero));
         stop;
         type_ = Types.Named { path; arguments = [ Types.Type element ] };
         origin;
       })

let was_hole form (select_table : Tables.t -> Types.ty option array) (id : Syntax.id) =
  match form.tables_with_holes with
  | Some tables -> (select_table tables).(id) = Some Types.Hole
  | None -> false

let read_evidence form self_type trait : Core.evidence =
  match find_evidence form self_type trait with
  | Some (From_impl { impl; substitution }) -> Impl { impl; substitution }
  | Some From_bound -> Bound
  | Some From_any -> Dynamic
  | Some (Built_in | Accepted _) | None ->
      raise_bug "`%s` does not implement `%s` by an impl, a bound, or `any`" (Types.show self_type)
        (Types.show_trait trait)

let make_method_target form (method_ : Well_known.method_) ~self_type : Core.operand Core.target =
  let { Well_known.owner; name; receiver } = Well_known.locate_method method_ in
  let trait = Types.make_trait_reference ~arguments:[] (Well_known.make_path owner) in
  Trait_method
    {
      trait;
      name;
      receiver;
      self_type;
      instantiation = Types.no_instantiation;
      evidence = read_evidence form self_type trait;
    }

let convert_callee form (callee : Tables.callee) : Core.operand Core.target =
  match callee with
  | Function { path; instantiation } -> Function { path; instantiation }
  | Trait_method { trait; name; receiver; self_type; instantiation } ->
      let evidence = read_evidence form self_type trait in
      Trait_method { trait; name; receiver; self_type; instantiation; evidence }
  | Capability_method { capability; name } -> Capability_method { capability; name }
  | Intrinsic { operation; type_arguments } -> Intrinsic { operation; type_arguments }
  | Constructor _ | Indirect -> raise_bug "this callee has no core callee"

let arithmetic_methods : (Well_known.method_ * Intrinsic.scalar) list =
  [
    (Add_add, Add);
    (Subtract_subtract, Subtract);
    (Multiply_multiply, Multiply);
    (Divide_divide, Divide);
    (Remainder_remainder, Remainder);
    (Negate_negate, Negate);
  ]

let is_number type_ = Types.is_integer_type type_ || Types.is_float_type type_

let is_built_in_scalar type_ =
  is_number type_ || Types.is_builtin Bool type_ || Types.is_builtin Character type_

let find_built_in_operation (trait : Types.trait_reference) name receiver self_type =
  if
    is_number self_type
    && List.for_all (fun argument -> argument = Types.Type self_type) trait.trait_arguments
  then
    Option.bind
      (Well_known.find_method (Method { owner = trait.trait; name; receiver }))
      (fun method_ -> List.assoc_opt method_ arithmetic_methods)
  else None

let read_constructor_fields form type_ variant type_arguments =
  let fields =
    match variant with
    | None -> Members.find_fields form.lookups type_ type_arguments
    | Some variant ->
        Option.bind (Members.find_variants form.lookups type_ type_arguments) (fun variants ->
            Option.bind
              (List.find_opt
                 (fun (written : Types.variant) -> written.variant_name = variant)
                 variants)
              (fun (written : Types.variant) -> written.fields))
  in
  match fields with
  | Some fields -> fields
  | None -> raise_bug "`%s` is constructed but has no fields" (Path.show type_)

let read_type form (value : Syntax.expression) =
  match form.tables.types.(value.id) with
  | Some type_ -> type_
  | None -> raise_bug "`%s` has a core node but no recorded type" (quote form value.id)

let read_local_type form (id : Syntax.id) =
  match form.tables.local_types.(id) with
  | Some type_ -> type_
  | None -> raise_bug "a local has no recorded type"

let read_pattern_type form (id : Syntax.id) =
  match form.tables.scrutinee_types.(id) with
  | Some type_ -> type_
  | None -> raise_bug "a pattern has no recorded type"

let build_literal : Tables.literal -> Core.kind = function
  | Integer_value number -> Integer number
  | Float_value number -> Float number

let build_function_value form (value : Syntax.expression) : Core.kind =
  match form.tables.resolutions.(value.id) with
  | Some (Global { path; instantiation }) -> Function_value { path; instantiation }
  | _ -> raise_bug "`%s` is not recorded as a function" (quote form value.id)

let build_variant_value form (value : Syntax.expression) type_path variant : Core.kind =
  match read_type form value with
  | Types.Function { output = Types.Named { arguments; _ } as variant_type; _ } ->
      let origin = make_rewrite_origin value.id in
      let fields =
        List.map
          (fun (field : Types.field) -> (field, allocate_synthetic_local form))
          (read_constructor_fields form type_path (Some variant) arguments)
      in
      Lambda
        {
          parameters =
            List.map
              (fun ((field : Types.field), local) ->
                make_binding form ~origin ~is_var:false ~mode:Own field.field_type local)
              fields;
          captures = [];
          body =
            {
              statements = [];
              value =
                Some
                  (make_synthetic_expression form ~origin variant_type
                     (Construct
                        {
                          variant = Some variant;
                          fields =
                            List.map
                              (fun ((field : Types.field), local) ->
                                ( field.field_name,
                                  Some
                                    (Core.Value (make_local_use form ~origin field.field_type local))
                                ))
                              fields;
                        }));
            };
          result = variant_type;
        }
  | _ -> Construct { variant = Some variant; fields = [] }

let read_self_type (env : env) =
  match env.self with Some type_ -> type_ | None -> raise_bug "`self` is used outside a method"

let build_self_local env ~origin : Core.place =
  Local { local = Self; type_ = read_self_type env; origin }

let build_constant_place form ~origin (path : Path.t) : Core.place =
  Constant
    { path; type_ = Interface.Definition.read_constant_type form.lookups.interface path; origin }

let build_record fields : Core.kind =
  Construct
    {
      variant = None;
      fields =
        List.map
          (fun (field, value) -> (Well_known.show_field field, Some (Operands.build Own value)))
          fields;
    }

let list_capability_impls (lookups : Lookups.t) ~list_bounds ~package (type_ : Types.ty) =
  match type_ with
  | Types.Named { path; _ } ->
      List.filter_map
        (fun (trait, _) ->
          if Resolve.Names.find_kind lookups.interface.names trait = Some Capability then
            match
              Interface.Impls.find_evidence lookups.interface ~list_bounds type_
                (Types.make_trait_reference ~arguments:[] trait)
            with
            | Some (Interface.Impls.From_impl { impl; substitution }) ->
                Option.map
                  (fun interface ->
                    ({ Core.capability = trait; impl; arguments = substitution }, interface))
                  (Interface.Definition.find_impl_interface lookups.interface impl)
            | _ -> None
          else None)
        (List.concat_map
           (fun package -> Interface.Impls.list_impls_for_type lookups.interface path package)
           (List.sort_uniq compare [ Path.locate_package path; package; Path.standard_package ]))
  | _ -> []

let push_target : Core.operand Core.target =
  Function
    { path = Well_known.make_method_path String_push; instantiation = Types.no_instantiation }

let build_list_literal form ~origin (element : Types.ty) (elements : Core.expression list) :
    Core.kind =
  let make = make_synthetic_expression form ~origin in
  let storage_type = Types.make_builtin Storage ~arguments:[ Type element ] in
  let make_storage operation ~type_arguments arguments =
    make storage_type
      (Call
         (make_call form ~callee:(Intrinsic { operation; type_arguments }) ~arguments ~lends:None))
  in
  let storage =
    match elements with
    | [] ->
        make_storage (Buffer Storage_with_capacity) ~type_arguments:[ Types.Type element ]
          [ Operands.build_argument Read (make (Types.make_builtin UInt64) (Integer Z.zero)) ]
    | _ ->
        let count = Types.Value (Known (Z.of_int (List.length elements))) in
        let array =
          make
            (Types.make_builtin Array ~arguments:[ Type element; count ])
            (Collection_literal { elements; construction = Array })
        in
        make_storage (Buffer Storage_from_array) ~type_arguments:[ Types.Type element; count ]
          [ Operands.build_argument Own array ]
  in
  Call
    (make_call form
       ~callee:
         (Function
            {
              path = Well_known.make_method_path List_from_storage;
              instantiation =
                { Types.no_instantiation with type_arguments = [ Types.Type element ] };
            })
       ~arguments:[ Passed { mode = Own; value = Value storage } ]
       ~lends:None)

let build_constant_pattern form (id : Syntax.id) (value : Core.pattern_constant) : Core.pattern_kind
    =
  let type_ = read_pattern_type form id in
  if is_built_in_scalar type_ || type_ = Types.Integer then Literal value
  else
    Equal_to
      { value; equal = make_callee form (make_method_target form Equal_equal ~self_type:type_) }

let build_literal_constant form (id : Syntax.id) (written : Syntax.literal) : Core.pattern_constant
    =
  match (written, form.tables.patterns.(id)) with
  | _, Some (Literal_pattern number) -> Integer_constant number
  | Literal_true, _ -> Boolean_constant true
  | Literal_false, _ -> Boolean_constant false
  | Literal_string text, _ -> String_constant text.first.value
  | Literal_integer _, _ -> raise_bug "an integer pattern has no value"

let build_range_bound form (bound : Syntax.range_end) : Core.range_bound =
  match (bound.kind, form.tables.patterns.(bound.id)) with
  | End_literal _, Some (Literal_pattern number) -> Integer_bound number
  | End_constant _, Some (Constant_pattern constant) -> Constant_bound constant
  | (End_literal _ | End_constant _), _ -> raise_bug "a range bound was not recorded"

let convert_to_integer form (node : Core.expression) : Core.expression =
  if not (is_within form node.type_ Types.integer_types) then node
  else
    make_synthetic_expression form ~origin:(rewrite_origin node.origin) Types.Integer
      (Convert { conversion = To_integer; value = node })

let convert_to_operation : Syntax.operation -> Intrinsic.scalar = function
  | Arithmetic Add -> Add
  | Arithmetic Subtract -> Subtract
  | Arithmetic Multiply -> Multiply
  | Arithmetic Divide -> Divide
  | Arithmetic Remainder -> Remainder
  | Bitwise Bit_and -> Bit_and
  | Bitwise Bit_or -> Bit_or
  | Bitwise Bit_xor -> Bit_xor
  | Shift Shift_left -> Shift_left
  | Shift Shift_right -> Shift_right

let is_executable form (condition : Core.expression) =
  let executable = ref true in
  let is_specification_only (callee : Core.callee) =
    match callee.target with
    | Function { path; _ } -> (
        match Instantiation.find_function_signature form.lookups path with
        | Some signature -> signature.specification_only
        | _ -> false)
    | Trait_method { trait; name; receiver; _ } ->
        List.exists
          (fun (method_ : Types.trait_method) ->
            method_.method_receiver = receiver
            && (Members.read_method_signature form.lookups trait.trait method_).specification_only)
          (Members.list_trait_methods form.lookups trait.trait name)
    | Capability_method _ | Intrinsic _ | Indirect _ -> false
  in
  Core_walk.walk_expression
    {
      Core_walk.ignore_all with
      expression =
        (fun (node : Core.expression) ->
          if node.type_ = Types.Integer then executable := false;
          match node.kind with
          | Quantified { binder = Over_type _; _ }
          | Result | Old _ | Yielded | Identical _ | Specification_function _ | Method_cost _
          | Convert { conversion = To_integer | From_integer; _ } ->
              executable := false
          | _ -> ());
      callee = (fun callee -> if is_specification_only callee then executable := false);
    }
    condition;
  !executable

let rec lend_statements form (mode : Language.Mode.t) (value : Core.expression) :
    Core.statement list =
  let make_statements kind = [ make_statement form ~origin:(rewrite_origin value.origin) kind ] in
  let make_branching kind =
    let type_ = if value.type_ = Types.Never then Types.Never else Types.unit in
    make_statements (Evaluate { value with type_; kind })
  in
  match value.kind with
  | If { condition; then_; else_ = Some else_ } ->
      make_branching
        (If
           {
             condition;
             then_ = lend_block form mode then_;
             else_ = Some (lend_block form mode else_);
           })
  | Match { scrutinees; arms } ->
      make_branching
        (Match
           {
             scrutinees;
             arms =
               List.map
                 (fun (arm : Core.arm) -> { arm with body = lend_block form mode arm.body })
                 arms;
           })
  | Block body -> make_branching (Block (lend_block form mode body))
  | _ when value.type_ = Types.Never -> make_statements (Evaluate value)
  | _ -> make_statements (Yield { mode; part = Operands.build mode value })

and lend_block form mode (body : Core.block) : Core.block =
  match body.value with
  | None -> body
  | Some value -> { statements = body.statements @ lend_statements form mode value; value = None }

let rec is_fixed_place : Core.place -> bool = function
  | Local _ | Constant _ -> true
  | Field { base; _ } -> is_fixed_place base
  | Element _ | Range _ | Lent _ | Temporary _ -> false

let build_cursor_next form (cursor : Types.ty) : Core.callee =
  make_callee form (make_method_target form Cursor_next ~self_type:cursor)

let convert_resource form (written : Syntax.resource) : Core.resource =
  let resolve_capability (path : Syntax.path_type) =
    match Places.find_target form.resolved path.path.last with
    | Some (Definition (Capability, capability)) -> capability
    | _ -> raise_bug "`calls` names something that is not a capability"
  in
  match written with
  | Metric metric -> Metric metric
  | Calls (Call_parameter name) -> (
      match Places.find_target form.resolved name with
      | Some (Local id) -> Calls (Function_parameter (Declared { origin = id; name = name.text }))
      | _ -> raise_bug "`calls(%s)` names no parameter" name.text)
  | Calls (Call_capability path) -> Calls (Capability (resolve_capability path))
  | Calls (Call_method (path, method_)) ->
      Calls (Capability_method (resolve_capability path, method_.text))

let build_under_condition form ~id (written : Syntax.condition option) build :
    'clause Core.conditional option =
  match (form.tables.conditions.(id), written) with
  | Some holds_when, _ -> Some { holds_when; clause = build (with_condition form holds_when) }
  | None, None -> Some { holds_when = []; clause = build form }
  | None, Some _ -> None

let apply_conversion form (id : Syntax.id) (inner : Core.expression) (conversion, expected) =
  let origin = make_rewrite_origin id in
  let make kind = make_synthetic_expression form ~origin expected kind in
  let convert conversion = make (Convert { conversion; value = inner }) in
  match (conversion : Tables.conversion) with
  | From_never -> inner
  | Function_widening -> if Types.equal inner.type_ expected then inner else convert Widen
  | To_integer -> convert To_integer
  | From_integer -> convert From_integer
  | View_to_owned -> convert View_to_owned
  | Owned_to_view when Types.is_well_known List inner.type_ || Types.is_builtin Array inner.type_ ->
      let base : Core.place = match inner.kind with Use place -> place | _ -> Temporary inner in
      make (make_range form ~origin base ~start:None ~stop:None ~inclusive:false)
  | Owned_to_view -> (
      match inner.type_ with
      | Types.Named { path; arguments } ->
          make
            (Call
               (make_call form
                  ~callee:
                    (Function
                       {
                         path = Method { owner = path; name = "slice"; receiver = Instance Read };
                         instantiation = { Types.no_instantiation with type_arguments = arguments };
                       })
                  ~arguments:[ Operands.build_argument Read inner ]
                  ~lends:None))
      | other -> raise_bug "`%s` is viewed and has no view" (Types.show other))

let has_node form (value : Syntax.expression) = Option.is_some form.tables.types.(value.id)

let rec list_operands form (value : Syntax.expression) : Syntax.expression list =
  let list_checked (part : Syntax.expression) =
    if has_node form part then [ part ] else list_operands form part
  in
  match value.kind with
  | Match { scrutinees; _ } -> List.concat_map list_checked scrutinees
  | Quantified { binder = Binder_in (_, collection); _ } -> list_checked collection
  | Quantified { binder = Binder_type _; _ } -> []
  | If _ | Parenthesized _ | Mode _ -> []
  | Bracket (base, [ Item { kind = Range { start; stop; _ }; _ } ]) ->
      List.concat_map list_checked (base :: (Option.to_list start @ Option.to_list stop))
  | _ ->
      let checked_parts = ref [] in
      Syntax_walk.visit_expression_parts ~on_statement:ignore value ~on_expression:(fun part ->
          checked_parts := list_checked part :: !checked_parts);
      List.concat (List.rev !checked_parts)

let rec build_expression form env (value : Syntax.expression) : Core.expression =
  let evaluated = if Option.is_some form.tables_with_holes then list_operands form value else [] in
  if
    List.exists
      (fun (operand : Syntax.expression) -> was_hole form (fun tables -> tables.types) operand.id)
      evaluated
  then begin
    let evaluate (operand : Syntax.expression) : Core.statement option =
      match operand.kind with
      | Lambda _ -> None
      | _ ->
          let node = build_expression form env operand in
          let origin = make_rewrite_origin operand.id in
          Some
            (make_statement form ~origin
               (Let
                  {
                    pattern = make_pattern form ~origin node.type_ Wildcard;
                    value = Operands.build Read node;
                    else_ = None;
                  }))
    in
    let statements = List.filter_map evaluate evaluated in
    let origin = make_rewrite_origin value.id in
    let todo = make_synthetic_expression form ~origin Types.Never Todo in
    make_synthetic_expression form ~origin Types.Never (Block { statements; value = Some todo })
  end
  else
    let built =
      match value.kind with
      | Parenthesized inner | Mode (_, inner) -> build_expression form env inner
      | _ -> (
          let id = allocate_node_id form in
          match form.tables.types.(value.id) with
          | Some type_ ->
              let kind = build_kind form env value in
              { Core.id; origin = compute_expression_origin value kind; type_; kind }
          | None -> raise_bug "`%s` has a node and no type" (quote form value.id))
    in
    List.fold_left (apply_conversion form value.id) built form.tables.conversions.(value.id)

and build_kind form env (value : Syntax.expression) : Core.kind =
  let elaboration = form.tables.elaborations.(value.id) in
  let raise_unexpected () = raise_bug "`%s` has no elaboration of its form" (quote form value.id) in
  match value.kind with
  | Integer _ | Float _ -> (
      match elaboration with
      | Some (Literal literal) -> build_literal literal
      | _ -> raise_unexpected ())
  | String literal -> (
      match elaboration with
      | Some (Literal literal) -> build_literal literal
      | Some (Template (Tagged { from_template; part; part_conversions })) ->
          build_tagged_string form env value literal ~from_template ~part ~part_conversions
      | Some (Template (Interpolated { displays })) ->
          build_interpolated_string form env ~origin:(make_rewrite_origin value.id) literal displays
      | None when Option.is_none literal.tag && literal.rest = [] -> String literal.first.value
      | _ -> raise_unexpected ())
  | True | False -> Boolean (value.kind = True)
  | Todo -> Todo
  | Unreachable -> Unreachable
  | Break -> Break
  | Continue -> Continue
  | Self_value -> Use (build_self_local env ~origin:(Written value.id))
  | Name _ -> build_name form env value
  | Member (base, member) -> build_member form env value base member
  | Bracket (base, items) -> (
      match form.resolved.brackets.(value.id) with
      | Some Type_arguments -> build_name form env value
      | Some (Method_bracket | Index) | None -> build_index form env value base items)
  | Call (callee, arguments) -> (
      match elaboration with
      | Some (Call ({ callee = Indirect; _ } as call)) ->
          build_call_kind ~function_value:callee form env value call
      | Some (Call call) -> build_call_kind form env value call
      | Some (Specification_call specification) ->
          build_specification_call form env value arguments specification
      | _ -> raise_unexpected ())
  | Try inner -> (
      match env.output with
      | Some (Returns output) -> build_try form env value inner ~output
      | _ -> raise_bug "`?` where nothing is returned")
  | With (base, written) ->
      let paths =
        match elaboration with Some (Record_update { paths }) -> paths | _ -> raise_unexpected ()
      in
      Record_update
        {
          base = build_expression form env base;
          updates =
            List.filter_map
              (fun (update : Syntax.update) ->
                match update.kind with
                | Update { value = written; _ } -> (
                    match List.assoc_opt written.id paths with
                    | Some path -> Some (path, build_expression form env written)
                    | None -> raise_bug "an update that names no field is built")
                | Update_error -> None)
              written;
        }
  | Prefix (Not, inner) -> Not (build_expression form env inner)
  | Prefix (Complement, inner) -> build_operator form env value Intrinsic.Complement [ inner ]
  | Prefix (Negate, inner) -> (
      match elaboration with
      | Some (Literal literal) -> build_literal literal
      | Some (Call call) -> build_call_kind form env value call
      | None -> build_operator form env value Intrinsic.Negate [ inner ]
      | Some _ -> raise_unexpected ())
  | Any inner -> (
      let inner = build_expression form env inner in
      match read_type form value with
      | Types.Any trait ->
          To_any { value = inner; trait; evidence = read_evidence form inner.type_ trait }
      | converted -> raise_bug "an `any` conversion has the type `%s`" (Types.show converted))
  | Binary { operator = Connective connective; left; right; _ } ->
      let left = build_expression form env left in
      let right = build_expression form env right in
      Connective { connective; left; right }
  | Binary { operator = Operation ((Bitwise _ | Shift _) as operation); left; right; _ } ->
      build_operator form env value (convert_to_operation operation) [ left; right ]
  | Binary { operator = Comparison comparison; left; right; _ } -> (
      match elaboration with
      | Some (Call call) -> build_comparison form env value comparison left right call
      | None -> build_built_in_comparison form env comparison left right
      | Some _ -> raise_unexpected ())
  | Binary { operator = Operation (Arithmetic _ as operation); left; right; _ } -> (
      match elaboration with
      | Some (Call call) -> build_call_kind form env value call
      | None -> build_operator form env value (convert_to_operation operation) [ left; right ]
      | Some _ -> raise_unexpected ())
  | Is { value = tested; pattern = written; _ } ->
      Matches
        {
          value =
            Operands.build
              (Places.classify_scrutinee_mode form.resolved form.tables tested)
              (build_expression form env tested);
          pattern = build_scrutinee_pattern form written;
        }
  | Range { start; stop; inclusive; _ } -> build_range_record form env value start stop ~inclusive
  | Quantified { quantifier; binder; body } -> (
      let make_quantified binder : Core.kind =
        Quantified { quantifier; binder; body = build_expression form env body }
      in
      match (binder, elaboration) with
      | Binder_type (bound, _), _ ->
          make_quantified
            (Over_type
               {
                 local = Declared { origin = bound.id; name = bound.text };
                 type_ = read_local_type form bound.id;
               })
      | Binder_in (written, collection), Some (Loop (Elements { count; element; lends })) ->
          let pattern = build_pattern form written in
          quantify_over_elements form env value collection ~count ~element ~lends (fun elements ->
              make_quantified (Over_elements { pattern; elements }))
      | ( Binder_in (written, { kind = Range { start = Some start; stop = Some stop; _ }; _ }),
          Some (Loop (Integer_range { inclusive; _ })) ) ->
          let pattern = build_pattern form written in
          let start = build_expression form env start in
          make_quantified
            (Over_range { pattern; start; stop = build_expression form env stop; inclusive })
      | Binder_in _, _ ->
          raise_bug "the checker recorded no iteration for a quantifier over a collection")
  | Echo inner -> Echo (build_expression form env inner)
  | Return inner -> (
      match (inner, env.output) with
      | Some inner, Some (Lends (mode, _)) ->
          let origin = make_rewrite_origin value.id in
          let returned = make_synthetic_expression form ~origin Types.Never (Return None) in
          Block
            {
              statements =
                lend_statements form mode (build_expression form env inner)
                @ [ make_statement form ~origin (Evaluate returned) ];
              value = None;
            }
      | _ -> Return (Option.map (build_expression form env) inner))
  | List items -> (
      match elaboration with
      | Some (Converted_literal { elements = List_element element; call }) ->
          build_converted_literal form value ~element call
            (List.map (build_expression form env) items)
      | None -> build_collection_literal form value (List.map (build_expression form env) items)
      | Some _ -> raise_unexpected ())
  | Map entries -> (
      let build_entries () =
        List.map
          (fun (entry_key, entry_value) ->
            let entry_key = build_expression form env entry_key in
            (entry_key, build_expression form env entry_value))
          entries
      in
      match elaboration with
      | Some (Converted_literal { elements = Map_entry { key; value = value_type }; call }) ->
          build_converted_map_literal form value ~key ~value_type call (build_entries ())
      | None -> Map_literal { entries = build_entries () }
      | Some _ -> raise_unexpected ())
  | Lambda { parameters; body } ->
      let captures =
        match elaboration with Some (Lambda { captures }) -> captures | _ -> raise_unexpected ()
      in
      let parameters = List.map (build_pattern form) parameters in
      let result =
        match read_type form value with
        | Types.Function function_type -> function_type.output
        | type_ -> raise_bug "a lambda of type `%s`" (Types.show type_)
      in
      Lambda
        {
          parameters;
          captures =
            List.filter_map
              (fun (id, (local : Core.local)) : Core.capture option ->
                match local with
                | Self -> Some { local = Self; type_ = read_self_type env }
                | _ when was_hole form (fun tables -> tables.local_types) id -> None
                | _ -> Some { local; type_ = read_local_type form id })
              captures;
          body = build_block form { env with output = Some (Returns result) } body;
          result;
        }
  | If { condition = test; then_; else_ } ->
      let condition = build_expression form env test in
      let then_ = build_block form env then_ in
      If
        {
          condition;
          then_;
          else_ =
            Option.map
              (function
                | Syntax.Else block -> build_block form env block
                | Else_if branch ->
                    let branch = build_expression form env branch in
                    { Core.statements = []; value = Some branch })
              else_;
        }
  | Match { scrutinees; arms } ->
      let scrutinees =
        List.map
          (fun scrutinee ->
            Operands.build
              (Places.classify_scrutinee_mode form.resolved form.tables scrutinee)
              (build_expression form env scrutinee))
          scrutinees
      in
      Match
        {
          scrutinees;
          arms =
            List.map
              (fun (arm : Syntax.arm) : Core.arm ->
                let patterns = List.map (build_scrutinee_pattern form) arm.patterns in
                let guard = Option.map (build_expression form env) arm.guard in
                {
                  patterns;
                  guard;
                  body = build_block form env { statements = [ arm.body ]; id = arm.body.id };
                  origin = Written arm.id;
                })
              arms;
        }
  | Provide { implementations; body } -> build_provide form env implementations body
  | Block body -> Block (build_block form env body)
  | Parenthesized _ | Mode _ -> raise_bug "a wrapper has no node of its own"
  | Self_type_value | Expression_error ->
      raise_bug "`%s` is not a value and has no core node" (quote form value.id)

and build_name form env (value : Syntax.expression) : Core.kind =
  match Resolve.find_head form.resolved value with
  | Some { target = Local id; name; _ } ->
      if was_hole form (fun tables -> tables.local_types) id then Todo
      else
        Use
          (Local
             {
               local = Declared { origin = id; name = name.text };
               type_ = read_local_type form id;
               origin = Written value.id;
             })
  | Some { target = Law_parameter index; _ } -> (
      match List.nth_opt form.law_parameters index with
      | Some (name, type_) ->
          Use (Local { local = Trait_parameter { index; name }; type_; origin = Written value.id })
      | None -> raise_bug "the law has no parameter `%s`" (quote form value.id))
  | Some { target = Value_parameter parameter; _ } -> Value_parameter parameter
  | Some { target = Definition (Function, _); _ } -> build_function_value form value
  | Some { target = Definition (Constant, path); _ } ->
      Use (build_constant_place form ~origin:(Written value.id) path)
  | Some { target = Definition (Type, _); _ } -> Construct { variant = None; fields = [] }
  | Some { target = Variant (type_path, variant); _ } ->
      build_variant_value form value type_path variant
  | Some { target = Field field; _ } ->
      Use
        (Field
           {
             base = build_self_local env ~origin:(Written value.id);
             field;
             type_ = read_type form value;
             origin = Written value.id;
           })
  | Some { target = Result_value; _ } -> Result
  | Some { target = Visited; _ } -> Yielded
  | Some _ | None -> raise_bug "`%s` is not a value and has no core node" (quote form value.id)

and build_member form env (value : Syntax.expression) base (member : Syntax.name) : Core.kind =
  match form.tables.resolutions.(value.id) with
  | Some (Field_access _) ->
      Use
        (Field
           {
             base = make_place (build_expression form env base);
             field = member.text;
             type_ = read_type form value;
             origin = Written value.id;
           })
  | Some (Global { path = Member_constant _ as constant; _ }) ->
      Use (build_constant_place form ~origin:(Written value.id) constant)
  | Some (Variant_value { type_ = Types.Named { path; _ }; variant }) ->
      build_variant_value form value path variant
  | Some (Global _) -> build_function_value form value
  | _ -> raise_bug "`%s` is a member with no recorded resolution" (quote form value.id)

and build_index form env (value : Syntax.expression) base items : Core.kind =
  match items with
  | [ Item { kind = Range { start; stop; inclusive; _ }; _ } ] ->
      let base = make_place (build_expression form env base) in
      let start = Option.map (build_expression form env) start in
      let stop = Option.map (build_expression form env) stop in
      make_range form ~origin:(Written value.id) base ~start ~stop ~inclusive
  | [ Item key ] -> (
      match
        (Tables.find_call form.tables value.id, Types.find_sequence_element (read_type form base))
      with
      | Some call, _ -> build_call_kind form env value call
      | None, Some element ->
          Use
            (Element
               {
                 id = allocate_node_id form;
                 base = make_place (build_expression form env base);
                 index = build_expression form env key;
                 type_ = element;
                 origin = Written value.id;
               })
      | None, None -> raise_bug "`%s` is indexed and has no elements" (quote form value.id))
  | _ -> raise_bug "`%s` is indexed with other than one item" (quote form value.id)

and build_specification_call form env (value : Syntax.expression) (arguments : Syntax.argument list)
    (specification : Tables.specification_call) : Core.kind =
  match specification with
  | Specification_function function_ ->
      let operands =
        match (function_, value.kind) with
        | Callback_ensures, Call ({ kind = Member (callback, _); _ }, _) ->
            [ build_expression form env callback ]
        | _ -> []
      in
      Specification_function
        {
          function_;
          arguments =
            operands
            @ List.map
                (fun (argument : Syntax.argument) -> build_expression form env argument.value)
                arguments;
        }
  | Method_cost { metric; trait; name; receiver; self_type } ->
      Method_cost
        {
          metric;
          method_ =
            Trait_method
              {
                trait;
                name;
                receiver;
                self_type;
                instantiation = Types.no_instantiation;
                evidence = Bound;
              };
        }
  | Old -> (
      match arguments with
      | [ argument ] -> Old (build_expression form env argument.value)
      | _ -> raise_bug "`old` does not have one argument")
  | Identical -> (
      match arguments with
      | [ first; second ] ->
          let first = build_expression form env first.value in
          Identical (first, build_expression form env second.value)
      | _ -> raise_bug "`identical` does not have two arguments")
  | Final { part } -> build_final form value ~part

and build_final form (value : Syntax.expression) ~part : Core.kind =
  let parts : Types.ty =
    Named { path = Well_known.make_path Sequence; arguments = [ Types.Type part ] }
  in
  let make = make_synthetic_expression form ~origin:(make_rewrite_origin value.id) in
  let build_read_argument = Operands.build_argument Read in
  let first =
    make part
      (Call
         (make_call form
            ~callee:(make_method_target form Index_at ~self_type:parts)
            ~arguments:
              [
                build_read_argument (make parts Yielded);
                build_read_argument (make Types.Integer (Integer Z.zero));
              ]
            ~lends:(Some Read)))
  in
  Use (Lent first)

and build_arguments form env (call : Tables.call) : Core.argument list =
  List.init
    (List.length call.arguments + List.length call.omitted_defaults)
    (fun index ->
      match
        List.find_opt
          (fun (argument : Tables.argument) -> argument.core_argument_index = index)
          call.arguments
      with
      | Some argument ->
          Core.Passed
            {
              mode = argument.mode;
              value = Operands.build argument.mode (build_expression form env argument.expression);
            }
      | None -> Default)

and build_call form env ~lends ?function_value (call : Tables.call) : Core.call =
  make_call form
    ~callee:
      (match (call.callee, function_value) with
      | Indirect, Some function_value -> Indirect (Operands.build Read function_value)
      | direct, _ -> convert_callee form direct)
    ~arguments:(build_arguments form env call) ~lends

and build_argument_expressions form env (call : Tables.call) =
  List.map
    (fun (argument : Tables.argument) -> build_expression form env argument.expression)
    (List.sort
       (fun (left : Tables.argument) (right : Tables.argument) ->
         compare left.core_argument_index right.core_argument_index)
       call.arguments)

and build_call_kind ?function_value form env (value : Syntax.expression) (recorded : Tables.call) :
    Core.kind =
  let lends = recorded.lends in
  match recorded.callee with
  | Trait_method { trait; _ } when Well_known.is Copyable trait.trait -> (
      match recorded.arguments with
      | [ receiver ] -> Copy (Operands.build Read (build_expression form env receiver.expression))
      | _ -> raise_bug "`copy` does not have exactly one argument")
  | Trait_method { trait; name; receiver; self_type; _ }
    when Option.is_some (find_built_in_operation trait name receiver self_type) ->
      Operator
        {
          operation = Option.get (find_built_in_operation trait name receiver self_type);
          arguments = build_argument_expressions form env recorded;
        }
  | Trait_method { trait; name; receiver; self_type; _ }
    when is_built_in_scalar self_type
         && Well_known.is_method Equal_equal (Method { owner = trait.trait; name; receiver }) -> (
      match build_argument_expressions form env recorded with
      | [ left; right ] -> Compare { comparison = Equal; left; right }
      | _ -> raise_bug "`equal` does not have exactly two arguments")
  | Constructor { type_; variant; type_arguments } ->
      let declared = read_constructor_fields form type_ variant type_arguments in
      let written =
        List.map
          (fun (argument : Tables.argument) ->
            ( (List.nth declared argument.core_argument_index).field_name,
              Some (Operands.build argument.mode (build_expression form env argument.expression)) ))
          recorded.arguments
      in
      let defaulted =
        List.filter_map
          (fun (field : Types.field) ->
            if List.mem_assoc field.field_name written then None else Some (field.field_name, None))
          declared
      in
      Construct { variant; fields = written @ defaulted }
  | Indirect | Function _ | Trait_method _ | Capability_method _ | Intrinsic _ -> (
      let function_value = Option.map (build_expression form env) function_value in
      let call = Core.Call (build_call form env ~lends ?function_value recorded) in
      match lends with
      | Some _ ->
          Use
            (Lent
               (make_synthetic_expression form
                  ~origin:(compute_expression_origin value call)
                  recorded.callee_result call))
      | None -> call)

and build_operator form env (value : Syntax.expression) operation
    (operands : Syntax.expression list) : Core.kind =
  let arguments = List.map (build_expression form env) operands in
  Operator
    {
      operation;
      arguments =
        (if read_type form value = Types.Integer then List.map (convert_to_integer form) arguments
         else arguments);
    }

and build_built_in_comparison form env comparison (left : Syntax.expression)
    (right : Syntax.expression) : Core.kind =
  let left = build_expression form env left in
  let right = build_expression form env right in
  let left, right =
    if Types.equal left.type_ right.type_ then (left, right)
    else (convert_to_integer form left, convert_to_integer form right)
  in
  Compare { comparison; left; right }

and build_comparison form env (value : Syntax.expression) comparison (left : Syntax.expression)
    (right : Syntax.expression) (recorded : Tables.call) : Core.kind =
  match recorded.callee with
  | Trait_method { self_type; _ } when is_built_in_scalar self_type ->
      build_built_in_comparison form env comparison left right
  | _ -> (
      let origin = make_rewrite_origin value.id in
      let call =
        make_synthetic_expression form ~origin recorded.callee_result
          (Call (build_call form env ~lends:None recorded))
      in
      let make_matches_variant variant : Core.kind =
        Matches
          {
            value = Operands.build Own call;
            pattern =
              make_pattern form ~origin recorded.callee_result
                (Variant { variant = Well_known.show_variant variant; fields = [] });
          }
      in
      let make_not kind : Core.kind =
        Not (make_synthetic_expression form ~origin Types.bool kind)
      in
      match comparison with
      | Equal -> call.kind
      | Not_equal -> Not call
      | Less -> make_matches_variant Ordering_less
      | Less_equal -> make_not (make_matches_variant Ordering_greater)
      | Greater -> make_matches_variant Ordering_greater
      | Greater_equal -> make_not (make_matches_variant Ordering_less))

and build_range_record form env (value : Syntax.expression) start stop ~inclusive : Core.kind =
  match (start, stop) with
  | Some start, Some stop ->
      let start = build_expression form env start in
      let stop = build_expression form env stop in
      let inclusive =
        make_synthetic_expression form ~origin:(make_rewrite_origin value.id) Types.bool
          (Core.Boolean inclusive)
      in
      build_record [ (Range_start, start); (Range_stop, stop); (Range_inclusive, inclusive) ]
  | _ -> raise_bug "a range without both bounds is valid only inside a slice"

and build_provide form env (implementations : Syntax.expression list) (body : Syntax.block) :
    Core.kind =
  let implementations =
    List.map
      (fun (implementation : Syntax.expression) : Core.implementation ->
        let mode : Language.Mode.t =
          match implementation.kind with Mode (Mut, _) -> Mut | _ -> Read
        in
        let node = build_expression form env implementation in
        {
          origin = Written implementation.id;
          mode;
          value = Operands.build mode node;
          type_ = node.type_;
          provides =
            List.map fst
              (list_capability_impls form.lookups ~list_bounds:(list_bounds form)
                 ~package:form.package node.type_);
        })
      implementations
  in
  Provide { implementations; body = build_block form env body }

and build_interpolated_string form env ~origin (literal : Syntax.string_literal)
    (displays : Tables.call list) : Core.kind =
  let make = make_synthetic_expression form ~origin in
  let make_statement = make_statement form ~origin in
  let text = allocate_synthetic_local form in
  let text_place : Core.place = Local { local = text; type_ = Types.string_type; origin } in
  let let_text =
    make_statement
      (Let
         {
           pattern = make_binding form ~origin ~is_var:true ~mode:Own Types.string_type text;
           value = Operands.build Own (make Types.string_type (String literal.first.value));
           else_ = None;
         })
  in
  let push (pushed : Syntax.text) =
    if pushed.value = "" then []
    else
      [
        make_statement
          (Evaluate
             (make Types.unit
                (Call
                   (make_call form ~callee:push_target
                      ~arguments:
                        [
                          Passed { mode = Mut; value = Place text_place };
                          Passed
                            {
                              mode = Read;
                              value =
                                Value
                                  (make
                                     (Types.make_named (Well_known.make_path String_slice) [])
                                     (String pushed.value));
                            };
                        ]
                      ~lends:None))));
      ]
  in
  let make_display part (display : Tables.call) =
    make_statement
      (Evaluate
         (make Types.unit
            (Call
               (make_call form
                  ~callee:(convert_callee form display.callee)
                  ~arguments:
                    [
                      Operands.build_argument Read (build_expression form env part);
                      Passed { mode = Mut; value = Place text_place };
                    ]
                  ~lends:None))))
  in
  Block
    {
      statements =
        let_text
        :: List.concat
             (List.map2
                (fun (part, after) display -> make_display part display :: push after)
                literal.rest displays);
      value = Some (make Types.string_type (Use text_place));
    }

and build_tagged_string form env (value : Syntax.expression) (literal : Syntax.string_literal)
    ~(from_template : Tables.call) ~(part : Types.ty) ~(part_conversions : Tables.call option list)
    : Core.kind =
  let origin = make_rewrite_origin value.id in
  let make = make_synthetic_expression form ~origin in
  let make_list element elements =
    make
      (Types.make_named (Well_known.make_path List) [ element ])
      (build_list_literal form ~origin element elements)
  in
  let literal_type = Types.make_named (Well_known.make_path Literal) [] in
  let texts =
    List.map
      (fun (written : Syntax.text) ->
        make literal_type
          (build_record
             [
               ( Literal_text,
                 make
                   (Types.make_named (Well_known.make_path String_slice) [])
                   (String written.value) );
             ]))
      (literal.first :: List.map snd literal.rest)
  in
  let parts =
    List.map2
      (fun ((written : Syntax.expression), _) (conversion : Tables.call option) ->
        match conversion with
        | Some call ->
            make_synthetic_expression form ~origin:(make_rewrite_origin written.id)
              call.callee_result
              (Call (build_call form env ~lends:None call))
        | None -> build_expression form env written)
      literal.rest part_conversions
  in
  let texts = make_list literal_type texts in
  let template =
    make
      (Types.make_named (Well_known.make_path Template) [ part ])
      (build_record [ (Template_literals, texts); (Template_parts, make_list part parts) ])
  in
  Template
    {
      literals =
        List.map
          (fun (written : Syntax.text) -> written.value)
          (literal.first :: List.map snd literal.rest);
      call =
        make from_template.callee_result
          (Call
             (make_call form
                ~callee:(convert_callee form from_template.callee)
                ~arguments:[ Operands.build_argument Read template ]
                ~lends:None));
    }

and build_collection_literal form (value : Syntax.expression) (elements : Core.expression list) :
    Core.kind =
  match read_type form value with
  | Types.Named { path; arguments = [ Types.Type element ] } when Well_known.is List path ->
      build_list_literal form ~origin:(make_rewrite_origin value.id) element elements
  | Types.Named { path; _ } when Well_known.find_builtin_type path = Some Array ->
      Collection_literal { elements; construction = Array }
  | Types.Named { path; _ } when Well_known.is Sequence path || Well_known.is Finite_set path ->
      Collection_literal { elements; construction = Specification_only }
  | type_ -> raise_bug "a collection literal of type `%s`" (Types.show type_)

and build_converted_literal form (value : Syntax.expression) ~(element : Types.ty)
    (recorded : Tables.call) (elements : Core.expression list) : Core.kind =
  let origin = make_rewrite_origin value.id in
  let list =
    make_synthetic_expression form ~origin
      (Types.make_named (Well_known.make_path List) [ element ])
      (build_list_literal form ~origin element elements)
  in
  Call
    (make_call form
       ~callee:(convert_callee form recorded.callee)
       ~arguments:[ Operands.build_argument Own list ]
       ~lends:None)

and build_converted_map_literal form (value : Syntax.expression) ~(key : Types.ty)
    ~(value_type : Types.ty) (recorded : Tables.call)
    (entries : (Core.expression * Core.expression) list) : Core.kind =
  let entry = Types.make_named (Well_known.make_path Entry) [ key; value_type ] in
  build_converted_literal form value ~element:entry recorded
    (List.map
       (fun (entry_key, entry_value) ->
         make_synthetic_expression form ~origin:(make_rewrite_origin value.id) entry
           (build_record [ (Entry_key, entry_key); (Entry_value, entry_value) ]))
       entries)

and build_try form env (value : Syntax.expression) (inner : Syntax.expression) ~(output : Types.ty)
    : Core.kind =
  let origin : Core.origin = Desugared { construct = value.id; desugaring = Try } in
  let scrutinee = build_expression form env inner in
  let read_variants (type_ : Types.ty) =
    match type_ with
    | Types.Named { path; arguments } -> (
        match Members.find_variants form.lookups path arguments with
        | Some [ success; failure ] -> (success, failure)
        | _ -> raise_bug "`?` on `%s`" (Types.show type_))
    | _ -> raise_bug "`?` on `%s`" (Types.show type_)
  in
  let success, failure = read_variants scrutinee.type_ in
  let _, returned_failure = read_variants output in
  let make = make_synthetic_expression form ~origin in
  let bind_fields (variant : Types.variant) : Core.pattern * (string * Core.expression) list =
    let fields =
      List.map
        (fun (field : Types.field) -> (field, allocate_synthetic_local form))
        (Option.value ~default:[] variant.fields)
    in
    ( make_pattern form ~origin scrutinee.type_
        (Variant
           {
             variant = variant.variant_name;
             fields =
               List.map
                 (fun ((field : Types.field), local) ->
                   ( field.field_name,
                     make_binding form ~origin ~is_var:false ~mode:Own field.field_type local ))
                 fields;
           }),
      List.map
        (fun ((field : Types.field), local) ->
          (field.field_name, make_local_use form ~origin field.field_type local))
        fields )
  in
  let success_pattern, success_fields = bind_fields success in
  let failure_pattern, failure_fields = bind_fields failure in
  let make_arm patterns body : Core.arm = { patterns; guard = None; body; origin } in
  Match
    {
      scrutinees = [ Operands.build Own scrutinee ];
      arms =
        [
          make_arm [ success_pattern ]
            {
              statements = [];
              value = (match success_fields with [ (_, field) ] -> Some field | _ -> None);
            };
          make_arm [ failure_pattern ]
            {
              statements = [];
              value =
                Some
                  (make Types.Never
                     (Return
                        (Some
                           (make output
                              (Construct
                                 {
                                   variant = Some returned_failure.variant_name;
                                   fields =
                                     List.map2
                                       (fun (field : Types.field) (_, field_value) ->
                                         (field.field_name, Some (Operands.build Own field_value)))
                                       (Option.value ~default:[] returned_failure.fields)
                                       failure_fields;
                                 })))));
            };
        ];
    }

and build_collection_place form env (iterable : Syntax.expression) (mode : Language.Mode.t)
    ~(desugaring : Core.desugaring) : Core.place * (Core.block -> Core.kind) option =
  let collection = build_expression form env iterable in
  match collection.kind with
  | Use place when is_fixed_place place -> (place, None)
  | _ ->
      let local = allocate_synthetic_local form in
      let origin : Core.origin = Desugared { construct = iterable.id; desugaring } in
      let scrutinee = Operands.build mode collection in
      let pattern =
        make_binding form ~origin ~is_var:false
          ~mode:(match scrutinee with Place _ -> mode | Value _ -> Own)
          collection.type_ local
      in
      ( Local { local; type_ = collection.type_; origin },
        Some (make_binding_match ~origin scrutinee pattern) )

and build_elements form ~origin (collection : Core.place) ~(count : Tables.call)
    ~(element : Tables.call) ~(lends : Language.Mode.t) : Core.elements =
  let uint64 = Types.make_builtin UInt64 in
  let local = allocate_synthetic_local form in
  let make_receiver mode : Core.argument = Passed { mode; value = Place collection } in
  let position = make_local_use form ~origin uint64 local in
  {
    count =
      make_synthetic_expression form ~origin uint64
        (Call
           (make_call form
              ~callee:(convert_callee form count.callee)
              ~arguments:[ make_receiver Read ]
              ~lends:None));
    position = make_binding form ~origin ~is_var:false ~mode:Own uint64 local;
    element =
      (match Types.find_sequence_element (Core_walk.compute_place_type collection) with
      | Some element_type ->
          Element
            {
              id = allocate_node_id form;
              base = collection;
              index = position;
              type_ = element_type;
              origin;
            }
      | None ->
          Lent
            (make_synthetic_expression form ~origin element.callee_result
               (Call
                  (make_call form
                     ~callee:(convert_callee form element.callee)
                     ~arguments:
                       [
                         make_receiver lends;
                         Passed { mode = Read; value = Operands.build Read position };
                       ]
                     ~lends:(Some lends)))));
    lends;
  }

and quantify_over_elements form env (quantified : Syntax.expression)
    (collection : Syntax.expression) ~count ~element ~lends make_quantified : Core.kind =
  let place, bind_collection =
    build_collection_place form env collection lends ~desugaring:Quantifier
  in
  let kind =
    make_quantified
      (build_elements form
         ~origin:(Desugared { construct = collection.id; desugaring = Quantifier })
         place ~count ~element ~lends)
  in
  match bind_collection with
  | None -> kind
  | Some bind_collection ->
      bind_collection
        {
          statements = [];
          value =
            Some (make_synthetic_expression form ~origin:(Written quantified.id) Types.bool kind);
        }

and build_for_loop form env (written : Syntax.statement) (iterable : Syntax.expression) ~pattern
    ~clauses ~body ~mode : Core.statement_kind =
  let make_loop iteration : Core.statement_kind = For { pattern; iteration; clauses; body; mode } in
  let loop_origin : Core.origin = Desugared { construct = written.id; desugaring = For_loop } in
  let iterable_origin : Core.origin =
    Desugared { construct = iterable.id; desugaring = For_loop }
  in
  match (form.tables.elaborations.(written.id), iterable.kind) with
  | Some (Loop (Integer_range { inclusive; _ })), Range { start = Some start; stop = Some stop; _ }
    ->
      let start = build_expression form env start in
      make_loop (Integer_range { start; stop = build_expression form env stop; inclusive })
  | Some (Loop (Elements { count; element; lends })), _ -> (
      let place, bind_collection =
        build_collection_place form env iterable lends ~desugaring:For_loop
      in
      let elements_loop =
        make_loop
          (Elements (build_elements form ~origin:iterable_origin place ~count ~element ~lends))
      in
      match bind_collection with
      | None -> elements_loop
      | Some bind_collection ->
          let statement = make_statement form ~origin:(Written written.id) elements_loop in
          Evaluate
            (make_synthetic_expression form ~origin:loop_origin Types.unit
               (bind_collection { statements = [ statement ]; value = None })))
  | Some (Loop (Pulled { cursor; cursor_call; remaining })), _ -> (
      let collection = build_expression form env iterable in
      let pulled =
        match cursor_call with
        | None -> collection
        | Some cursor_call ->
            make_synthetic_expression form ~origin:iterable_origin cursor
              (Call
                 (make_call form
                    ~callee:(convert_callee form cursor_call.callee)
                    ~arguments:[ Passed { mode = Own; value = Operands.build Own collection } ]
                    ~lends:None))
      in
      let next = build_cursor_next form cursor in
      let make_cursor_loop ?remaining (place : Core.place) : Core.statement_kind =
        let measure =
          Option.map
            (fun (holds_when, (remaining : Tables.call)) : Core.loop_clause Core.conditional ->
              let form = with_condition form holds_when in
              {
                holds_when;
                clause =
                  Core.Decreases
                    [
                      make_synthetic_expression form ~origin:iterable_origin
                        (Types.make_builtin UInt64)
                        (Call
                           (make_call form
                              ~callee:(convert_callee form remaining.callee)
                              ~arguments:[ Passed { mode = Read; value = Place place } ]
                              ~lends:None));
                    ];
              })
            remaining
        in
        For
          {
            pattern;
            iteration = Cursor { cursor = place; next; next_origin = iterable_origin };
            clauses = clauses @ Option.to_list measure;
            body;
            mode;
          }
      in
      match
        ( pulled.kind,
          if Option.is_some (Core_walk.find_measure_condition clauses) then None else remaining )
      with
      | Use place, remaining when is_fixed_place place -> make_cursor_loop ?remaining place
      | _, None -> make_cursor_loop (make_place pulled)
      | _, Some remaining ->
          let local = allocate_synthetic_local form and origin = iterable_origin in
          let binding = make_binding form ~origin ~is_var:true ~mode:Own pulled.type_ local in
          let statement =
            make_statement form ~origin:(Written written.id)
              (make_cursor_loop ~remaining (Local { local; type_ = pulled.type_; origin }))
          in
          Evaluate
            (make_synthetic_expression form ~origin:loop_origin Types.unit
               (make_binding_match ~origin (Operands.build Own pulled) binding
                  { statements = [ statement ]; value = None })))
  | _ -> raise_bug "the checker recorded no iteration for a `for` loop"

and build_cost form env ~origin ({ amortized; resource = written; bound } : Syntax.cost) : Core.cost
    =
  {
    origin;
    amortized;
    resource = convert_resource form written;
    bound =
      (match bound with
      | Big_o value -> Order_of (build_expression form env value)
      | At_most value -> At_most (build_expression form env value)
      | Exactly value -> Exactly (build_expression form env value));
  }

and build_loop_clauses form env (clauses : Syntax.loop_clause list) =
  List.filter_map
    (fun (clause : Syntax.loop_clause) ->
      build_under_condition form ~id:clause.id clause.condition (fun form : Core.loop_clause ->
          match clause.kind with
          | Invariant value -> Invariant (build_expression form env value)
          | Loop_decreases measures -> Decreases (List.map (build_expression form env) measures)
          | Loop_cost written -> Cost (build_cost form env ~origin:(Written clause.id) written)))
    clauses

and build_compound_assign form env (written : Syntax.statement) (target : Syntax.expression)
    (value : Syntax.expression) operation : Core.statement_kind =
  let place = make_place (build_expression form env target) in
  let target_type = read_type form target in
  let origin = make_rewrite_origin written.id in
  let current = make_synthetic_expression form ~origin target_type Core.Current_target in
  let right = build_expression form env value in
  let bound = allocate_synthetic_local form in
  let bound_value = make_local_use form ~origin:(make_rewrite_origin value.id) right.type_ bound in
  let make_built_in operation : Core.kind * Core.operand =
    (Operator { operation; arguments = [ current; bound_value ] }, Operands.build Own right)
  in
  let kind, right_operand =
    match Tables.find_call form.tables written.id with
    | Some ({ callee = Trait_method { trait; name; receiver; self_type; _ }; _ } as recorded) -> (
        match find_built_in_operation trait name receiver self_type with
        | Some operation -> make_built_in operation
        | None ->
            let read_argument_mode index =
              match
                List.find_opt
                  (fun (argument : Tables.argument) -> argument.core_argument_index = index)
                  recorded.arguments
              with
              | Some argument -> argument.mode
              | None -> Language.Mode.Read
            in
            ( Call
                (make_call form
                   ~callee:(convert_callee form recorded.callee)
                   ~arguments:
                     [
                       Operands.build_argument (read_argument_mode 0) current;
                       Operands.build_argument (read_argument_mode 1) bound_value;
                     ]
                   ~lends:None),
              Operands.build (decide_binding_mode form (read_argument_mode 1) right.type_) right ))
    | Some _ -> raise_bug "a compound assignment's call is not a trait method call"
    | None -> make_built_in (convert_to_operation operation)
  in
  Compound_assign
    {
      target = place;
      operand = right_operand;
      bound;
      value = make_synthetic_expression form ~origin target_type kind;
    }

and build_statement form env (written : Syntax.statement) : Core.statement =
  let rec strip_mode_keyword (value : Syntax.expression) =
    match value.kind with
    | Mode (_, inner) | Parenthesized inner -> strip_mode_keyword inner
    | _ -> value
  in
  let find_hole (value : Syntax.expression) =
    let value = strip_mode_keyword value in
    if was_hole form (fun tables -> tables.types) value.id then Some value else None
  in
  match
    match written.kind with
    | For { iterable; _ } -> find_hole iterable
    | Assignment { target; _ } -> find_hole target
    | _ -> None
  with
  | Some value ->
      make_statement form ~origin:(make_rewrite_origin written.id)
        (Evaluate (build_expression form env value))
  | None ->
      let kind = build_statement_kind form env written in
      make_statement form ~origin:(Written written.id) kind

and build_statement_kind form env (written : Syntax.statement) : Core.statement_kind =
  match written.kind with
  | Expression value -> Evaluate (build_expression form env value)
  | Let { is_var; pattern = written_pattern; value; else_; _ } ->
      let mode =
        if is_var then Language.Mode.Own
        else if Places.is_borrowed form.resolved form.tables value then Language.Mode.Read
        else Language.Mode.Own
      in
      let value = Operands.build mode (build_expression form env value) in
      let pattern = build_scrutinee_pattern form written_pattern in
      Let { pattern; value; else_ = Option.map (build_block form env) else_ }
  | Assignment { target = written_target; operator = Assign; value } -> (
      match Tables.find_call form.tables written.id with
      | Some recorded ->
          let id = allocate_node_id form in
          let call = build_call form env ~lends:None recorded in
          Evaluate
            { id; origin = make_rewrite_origin written.id; type_ = Types.unit; kind = Call call }
      | None ->
          let target = make_place (build_expression form env written_target) in
          Assign { target; value = build_expression form env value })
  | Assignment { target = written_target; operator = Compound operation; value } ->
      build_compound_assign form env written written_target value operation
  | For { mode = running; pattern = written_pattern; iterable; clauses; body; _ } ->
      let inner =
        match iterable.kind with
        | Mode (_, inner)
          when Option.is_none (Places.find_keyword_operation form.resolved form.tables inner) ->
            inner
        | _ -> iterable
      in
      let pattern = build_pattern form written_pattern in
      let clauses = build_loop_clauses form env clauses in
      build_for_loop form env written inner ~pattern ~clauses ~body:(build_block form env body)
        ~mode:running
  | While { condition = test; clauses; body } ->
      let condition = build_expression form env test in
      let clauses = build_loop_clauses form env clauses in
      While { condition; clauses; body = build_block form env body }
  | Parallel body ->
      let branches = List.map (build_statement form env) body.statements in
      Parallel branches
  | Concurrent body ->
      let branches = List.map (build_statement form env) body.statements in
      Concurrent branches
  | Proof body -> Proof (build_block form env body)
  | Assert { value; by_bit_vector } ->
      let value = build_expression form env value in
      Assert { condition = { value; executable = is_executable form value }; by_bit_vector }
  | Statement_error -> raise_bug "an erroneous statement is built"

and build_block form env (written : Syntax.block) : Core.block =
  let rec build_statements (statements : Syntax.statement list) =
    match statements with
    | [] -> ([], None)
    | [ ({ kind = Expression value; _ } as last) ]
      when form.tables.elaborations.(last.id) <> Some Discarded ->
        ([], Some (build_expression form env value))
    | first :: rest ->
        let first = build_statement form env first in
        let rest, value = build_statements rest in
        (first :: rest, value)
  in
  let statements, value = build_statements written.statements in
  { statements; value }

and build_pattern form (written : Syntax.pattern) : Core.pattern =
  if was_hole form (fun tables -> tables.scrutinee_types) written.id then
    make_pattern form ~origin:(make_rewrite_origin written.id) Types.Never Wildcard
  else
    let id = allocate_node_id form in
    match form.tables.scrutinee_types.(written.id) with
    | Some type_ ->
        {
          Core.id;
          origin = Written written.id;
          type_;
          kind = build_pattern_kind form type_ written;
        }
    | None -> raise_bug "`%s` has a node and no type" (quote form written.id)

and build_pattern_kind form type_ (written : Syntax.pattern) : Core.pattern_kind =
  match (written.kind, form.tables.patterns.(written.id)) with
  | (Wildcard | Pattern_error), _ -> Wildcard
  | Binding bound, Some (Binding_pattern { local; is_var; mode }) ->
      Bind
        {
          local = Declared { origin = local; name = bound.text };
          is_var;
          mode;
          may_alias = binding_may_alias form mode type_;
        }
  | Qualified_constant _, Some (Constant_pattern constant) ->
      build_constant_pattern form written.id (Named_constant constant)
  | Literal literal, _ ->
      build_constant_pattern form written.id (build_literal_constant form written.id literal)
  | Pattern_range { start; stop; inclusive }, _ ->
      Range { start = build_range_bound form start; stop = build_range_bound form stop; inclusive }
  | Variant _, Some (Variant_pattern { variant; fields; _ }) ->
      Variant { variant; fields = build_pattern_fields form fields }
  | Record _, Some (Record_pattern { fields; _ }) -> Record (build_pattern_fields form fields)
  | Alternatives alternatives, _ -> Alternatives (List.map (build_pattern form) alternatives)
  | (Binding _ | Qualified_constant _ | Variant _ | Record _), _ ->
      raise_bug "`%s` is a pattern the checker did not record" (quote form written.id)

and build_pattern_fields form (fields : (string * Syntax.pattern) list) =
  List.map (fun (field, written) -> (field, build_pattern form written)) fields

and build_scrutinee_pattern form written = copy_plain_bindings form (build_pattern form written)

let build_contract form env (clauses : Syntax.clause list) : Core.contract =
  let collect_each choose =
    List.concat_map
      (fun (clause : Syntax.clause) ->
        match choose clause with
        | Some build ->
            List.concat
              (Option.to_list
                 (Option.map
                    (fun (built : _ Core.conditional) ->
                      List.map (fun each -> { built with clause = each }) built.clause)
                    (build_under_condition form ~id:clause.id clause.condition build)))
        | None -> [])
      clauses
  in
  let requires =
    collect_each (fun clause ->
        match clause.kind with
        | Requires value ->
            Some
              (fun form ->
                let value = build_expression form env value in
                [ { Core.value; executable = is_executable form value } ])
        | _ -> None)
  in
  let ensures =
    collect_each (fun clause ->
        match clause.kind with
        | Ensures value -> Some (fun form -> [ build_expression form env value ])
        | _ -> None)
  in
  let decreases =
    collect_each (fun clause ->
        match clause.kind with
        | Decreases measures -> Some (fun form -> List.map (build_expression form env) measures)
        | _ -> None)
  in
  let costs =
    collect_each (fun clause ->
        match clause.kind with
        | Cost cost -> Some (fun form -> [ build_cost form env ~origin:(Written clause.id) cost ])
        | _ -> None)
  in
  let panics_unless =
    List.concat_map
      (fun (clause : Syntax.clause) ->
        match clause.kind with
        | Uses uses ->
            List.concat_map
              (fun (use : Syntax.capability_use) ->
                List.map (build_expression form env) use.unless_values)
              uses
        | Requires _ | Ensures _ | Decreases _ | Cost _ | Clause_error -> [])
      clauses
  in
  { panics_unless; requires; ensures; decreases; costs }

let build_parameters form env (written : Syntax.parameter list) (signature : Types.signature) :
    Core.parameter list =
  List.filter_map
    (fun (parameter : Syntax.parameter) : Core.parameter option ->
      match parameter.kind with
      | Self_parameter _ ->
          Option.map
            (fun (mode, type_) : Core.parameter ->
              { local = Self; mode; type_; default = None; callback_contract = None })
            signature.receiver
      | Named_parameter { name; default; type_; _ } ->
          Option.map
            (fun (info : Types.parameter_info) : Core.parameter ->
              let default = Option.map (build_expression form env) default in
              {
                local = Declared { origin = name.id; name = name.text };
                mode = info.mode;
                type_ = info.type_;
                default;
                callback_contract =
                  (match type_.kind with
                  | Function_type { inputs; clauses; _ }
                    when List.exists
                           (fun (clause : Syntax.clause) ->
                             match clause.kind with Requires _ | Ensures _ -> true | _ -> false)
                           clauses
                         && List.for_all
                              (fun (input : Syntax.function_input) -> Option.is_some input.name)
                              inputs ->
                      let list_clauses select =
                        List.filter_map
                          (fun (clause : Syntax.clause) ->
                            Option.map (build_expression form env) (select clause.kind))
                          clauses
                      in
                      Some
                        {
                          inputs =
                            List.filter_map
                              (fun (input : Syntax.function_input) ->
                                Option.map
                                  (fun (input_name : Syntax.name) : Core.local ->
                                    Declared { origin = input_name.id; name = input_name.text })
                                  input.name)
                              inputs;
                          requires =
                            list_clauses (function
                              | Syntax.Requires value -> Some value
                              | _ -> None);
                          ensures =
                            list_clauses (function Syntax.Ensures value -> Some value | _ -> None);
                        }
                  | _ -> None);
              })
            (List.find_opt
               (fun (info : Types.parameter_info) -> info.name = name.text)
               signature.parameters)
      | Parameter_error -> None)
    written

let build_function form ~holds_body (written : Syntax.signature) (body_block : Syntax.block option)
    (signature : Types.signature) : Core.definition =
  let env = { output = Some signature.output; self = Option.map snd signature.receiver } in
  let parameters = build_parameters form env written.parameters signature in
  let contract = build_contract form env written.clauses in
  let body = if holds_body then Option.map (build_block form env) body_block else None in
  let body =
    match signature.output with
    | Lends (mode, _) -> Option.map (lend_block form mode) body
    | Returns _ -> body
  in
  Function { parameters; contract; body }

let build_type form ~self (type_body : Syntax.type_body) (clauses : Syntax.type_clause list) :
    Core.definition =
  let env = { output = None; self = Some self } in
  let list_defaulted variant (fields : Syntax.field list) =
    List.filter_map
      (fun (field : Syntax.field) ->
        match field.kind with
        | Field_declaration { name; default = Some value; _ } -> Some (variant, name.text, value)
        | _ -> None)
      fields
  in
  let defaults =
    List.map
      (fun (variant, name, value) ->
        (variant, name, build_expression form { output = None; self = None } value))
      (match type_body with
      | Fields fields -> list_defaulted None fields
      | Variants variants ->
          List.concat_map
            (fun (variant : Syntax.variant) ->
              list_defaulted (Some variant.name.text) (Option.value ~default:[] variant.fields))
            variants
      | Type_todo -> [])
  in
  let collect_clause choose =
    List.filter_map (fun (clause : Syntax.type_clause) -> choose clause.kind) clauses
  in
  Type
    {
      defaults;
      invariants =
        collect_clause (function
          | Type_invariant value ->
              let value = build_expression form env value in
              Some { Core.value; executable = is_executable form value }
          | _ -> None);
      potential =
        (match
           collect_clause (function
             | Potential value -> Some (build_expression form env value)
             | _ -> None)
         with
        | first :: _ -> Some first
        | [] -> None);
    }

let build_trait form ~self ~is_broken (members : Syntax.trait_member Syntax.node list) :
    Core.definition =
  let env = { output = None; self = Some self } in
  Trait
    (List.concat
       (List.mapi
          (fun index (line : Syntax.trait_member Syntax.node) ->
            match line.kind with
            | Law law when not (is_broken (Resolve.Parts.Member_body index)) ->
                let parameters =
                  List.filter_map
                    (fun (parameter : Syntax.parameter) : Core.parameter option ->
                      match parameter.kind with
                      | Named_parameter { name; _ } ->
                          Some
                            {
                              local = Declared { origin = name.id; name = name.text };
                              mode = Read;
                              type_ = read_local_type form name.id;
                              default = None;
                              callback_contract = None;
                            }
                      | _ -> None)
                    law.parameters
                in
                let requires = List.map (build_expression form env) law.requires in
                [
                  {
                    Core.name = law.name.text;
                    parameters;
                    requires;
                    body = build_block form { env with output = Some (Returns Types.bool) } law.body;
                    origin = Written line.id;
                  };
                ]
            | _ -> [])
          members))

let build_law_proof form ~holds_body (written : Syntax.block) : Core.definition =
  let parameters =
    List.mapi
      (fun index (name, type_) : Core.parameter ->
        {
          local = Trait_parameter { index; name };
          mode = Read;
          type_;
          default = None;
          callback_contract = None;
        })
      form.law_parameters
  in
  Law_proof
    {
      parameters;
      body =
        (if holds_body then
           Some (build_block form { output = Some (Returns Types.unit); self = None } written)
         else None);
    }

let build_definition form ~(key : Resolve.Names.key) ~(definition : Syntax.definition)
    ~(elaborated : Interface.Environment.elaborated_interface) ~checks_body : Core.definition =
  let is_broken (part : Resolve.Parts.part) =
    Resolve.Names.is_broken form.lookups.interface.names key part || (part = Body && not checks_body)
  in
  let holds_body = checks_body in
  let read_effective_signature () =
    match Interface.Impls.read_signature form.lookups.interface key.path with
    | Some signature -> signature
    | None -> raise_bug "a function with an interface has no signature"
  in
  if is_broken Header then Empty
  else
    match (definition.kind, elaborated.interface) with
    | Function { signature; body = written }, Function_interface _ ->
        build_function form ~holds_body signature (Some written) (read_effective_signature ())
    | Method_declaration signature, Function_interface _ ->
        build_function form ~holds_body signature None (read_effective_signature ())
    | Type_definition { body = type_body; clauses; _ }, Type_interface interface ->
        build_type form
          ~self:
            (Types.Named
               { path = key.path; arguments = Types.list_generic_arguments interface.type_generics })
          type_body clauses
    | Trait { members; _ }, Trait_interface _ ->
        build_trait form
          ~self:(Types.Parameter (Types.make_self_parameter key.path))
          ~is_broken members
    | Constant { value; _ }, Constant_interface _ ->
        Constant
          (if holds_body then Some (build_expression form { output = None; self = None } value)
           else None)
    | Test { body = written; _ }, _ ->
        Test
          (if holds_body then
             Some (build_block form { output = Some (Returns Types.unit); self = None } written)
           else None)
    | Theorem { parameters; clauses; body = written; _ }, Theorem_interface signature ->
        let env = { output = Some (Returns Types.unit); self = None } in
        let parameters = build_parameters form env parameters signature in
        let contract = build_contract form env clauses in
        Function
          {
            parameters;
            contract;
            body = (if holds_body then Some (build_block form env written) else None);
          }
    | Law_proof { body = written; _ }, _ -> build_law_proof form ~holds_body written
    | _ -> Empty

let rec replace_holes type_ =
  Types.map ~map_capabilities:replace_capability_holes
    (function Types.Hole -> Some Types.Never | _ -> None)
    type_

and replace_capability_holes capabilities =
  Types.map_capability_types replace_holes (Types.map_trait replace_holes) capabilities

let build lookups ~resolved ~tables ~context ~package ~text ~key ~definition ~elaborated
    ~law_parameters ~checks_body : Core.t =
  let tables_with_holes =
    if Tables.exists_type (function Types.Hole -> true | _ -> false) tables then Some tables
    else None
  in
  let form =
    {
      lookups;
      resolved;
      tables =
        (match tables_with_holes with
        | Some _ ->
            Tables.map ~map_type:replace_holes
              ~map_argument:(Types.map_argument replace_holes)
              ~map_capabilities:replace_capability_holes tables
        | None -> tables);
      tables_with_holes;
      context;
      law_parameters;
      package;
      text;
      counters = { next_node_id = 0; next_synthetic_local = 0 };
    }
  in
  {
    definition = build_definition form ~key ~definition ~elaborated ~checks_body;
    origin = Written definition.id;
  }

module For_testing = struct
  let is_written_expression = is_written_expression
end
