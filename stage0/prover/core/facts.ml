type unsupported = {
  location : Obligation.location;
  construct : Catalog.Prover.construct;
  foreign_definition : Path.t option;
}

exception Unsupported of unsupported

let is_home (context : State.context) (source : State.source) =
  source.key = context.home && Path.equal source.definition context.home.path

let is_in_home_package (context : State.context) (source : State.source) =
  Path.compare_package
    (Path.locate_package source.definition)
    (Path.locate_package context.home.path)
  = 0

let raise_unsupported location construct =
  raise (Unsupported { location; construct; foreign_definition = None })

let run_in_source (context : State.context) (source : State.source) read =
  try read ()
  with
  | Unsupported ({ foreign_definition = None; _ } as unsupported)
  when not (is_home context source)
  ->
    raise (Unsupported { unsupported with foreign_definition = Some source.definition })

let raise_bug format = Compiler_bug.raise_bug ~stage:"Prover" format
let list_method_type_arguments ~self_type arguments = Types.Type self_type :: arguments

let read_parameter_name (parameter : Mir.parameter) =
  match Mir.find_local_name parameter.local with
  | Some name -> name
  | None -> raise_bug "a parameter that no definition names"

let list_clauses (requires : Mir.requirement list) =
  List.map (fun (requirement : Mir.requirement) -> requirement.clause) requires

let make_variable ?numbers label = Query.make_variable ?numbers label
let declare (context : State.context) declaration = Query.declare context.query declaration

let find_argument_sorts (context : State.context) symbol =
  Query.find_argument_sorts context.query symbol

let add_fact (context : State.context) fact = Query.add_fact context.query fact
let make_fresh_name (context : State.context) label = Query.make_fresh_name context.query label

let mentions_fresh_after (context : State.context) mark term =
  Query.mentions_fresh_after context.query mark term

let run_once (context : State.context) stated make = Query.run_once context.query stated make

let declare_value_symbol context (frame : State.frame) name sort =
  match List.rev frame.binders with
  | [] ->
      declare context (Logic.Constant (name, sort));
      Logic.Symbol name
  | outermost_first ->
      declare context
        (Logic.Function (name, List.map (fun (_, sort, _) -> sort) outermost_first, sort));
      Logic.Apply (name, List.map (fun (bound, _, _) -> Logic.Symbol bound) outermost_first)

let declare_fresh (context : State.context) frame label sort =
  declare_value_symbol context frame (Query.make_ordered_fresh_name context.query label) sort

let close_over_binders (frame : State.frame) term =
  let names = List.map (fun (name, _, _) -> name) frame.binders in
  if Logic.mentions (List.filter (fun name -> not (List.mem name names)) frame.bound) term then None
  else if not (Logic.mentions names term) then Some term
  else
    let outermost_first = List.rev frame.binders in
    Some
      (Logic.forall
         ( List.map (fun (name, sort, _) -> (name, sort)) outermost_first,
           Logic.( ==> )
             (Logic.conjunction (List.map (fun (_, _, premise) -> premise) outermost_first))
             term ))

let add_frame_fact context (frame : State.frame) term =
  if not (Logic.mentions frame.bound term) then add_fact context term
  else Query.add_scoped_fact context.query ~bound:frame.bound term

let assume context (frame : State.frame) term =
  match term with
  | Logic.Boolean true -> ()
  | _ ->
      let guarded = Logic.( ==> ) frame.condition term in
      if not (Logic.mentions frame.bound term || Logic.mentions frame.bound frame.condition) then
        add_fact context guarded
      else Query.add_scoped_fact context.query ~bound:frame.bound guarded

let locate (context : State.context) (source : State.source) origin =
  if is_home context source then Obligation.Node origin else Whole_definition

let add_hole (context : State.context) hole =
  if not (List.mem hole context.holes) then context.holes <- hole :: context.holes

let find_signature (context : State.context) =
  match context.lookups.interface.names.read_definition context.home with
  | { kind = Function { signature; body; _ }; _ } -> Some (signature, body)
  | _ -> None

let make_panic_fix (context : State.context) : Catalog.Prover.fix list =
  match find_signature context with
  | Some (signature, body) when not context.inherits_precondition ->
      [
        (match
           ( List.find_opt
               (fun (clause : Syntax.clause) ->
                 match clause.kind with Uses _ -> true | _ -> false)
               signature.clauses,
             signature.clauses )
         with
        | Some uses, _ -> Add_panic_to_uses (Written uses.id)
        | None, first :: _ -> Add_panic (Before_clause (Written first.id))
        | None, [] -> Add_panic (Before_body (Written body.id)));
      ]
  | Some _ | None -> []

let find_parameter_name (context : State.context) symbol =
  if List.mem symbol context.entry then
    match List.assoc_opt symbol context.parameter_names with
    | Some name -> Some name
    | None -> Some "self"
  else None

let collect_codes codes = if List.mem None codes then None else Some (List.filter_map Fun.id codes)

let rec find_value_code context : Logic.term -> Catalog.Code.t option = function
  | Logic.Operation (Add, (_ :: _ :: _ as parts)) ->
      Option.map (fun parts -> Catalog.Code.Sum parts) (find_value_codes context parts)
  | Logic.Operation (Multiply, (_ :: _ :: _ as parts)) ->
      Option.map (fun parts -> Catalog.Code.Product parts) (find_value_codes context parts)
  | Logic.Operation (Subtract, [ left; right ]) -> (
      match (find_value_code context left, find_value_code context right) with
      | Some left, Some right -> Some (Difference (left, right))
      | _ -> None)
  | Logic.Operation (Negate, [ Logic.Operation (Negate, [ inner ]) ]) ->
      find_value_code context inner
  | Logic.Operation (Negate, [ inner ]) ->
      Option.map (fun inner -> Catalog.Code.Negated inner) (find_value_code context inner)
  | Logic.Apply (Logic.Symbol.Field { field; variant = None; _ }, [ receiver ]) ->
      Option.map
        (fun receiver -> Catalog.Code.Field { receiver; field })
        (find_value_code context receiver)
  | Logic.Symbol symbol ->
      Option.map (fun name -> Catalog.Code.Name name) (find_parameter_name context symbol)
  | Logic.Integer value -> Some (Integer value)
  | Logic.Boolean value -> Some (Boolean value)
  | _ -> None

and find_value_codes context parts = collect_codes (List.map (find_value_code context) parts)

let find_comparison_operator : Logic.operator -> Language.Comparison.t option = function
  | Less -> Some Less
  | Less_equal -> Some Less_equal
  | Greater -> Some Greater
  | Greater_equal -> Some Greater_equal
  | Equal -> Some Equal
  | _ -> None

let find_goal_code context term =
  let rec find_goal (term : Logic.term) : Catalog.Code.t option =
    match term with
    | Operation (And, parts) -> (
        match List.filter (fun part -> not (Logic.is_valid part)) parts with
        | [] -> None
        | [ part ] -> find_goal part
        | parts ->
            Option.map
              (fun parts -> Catalog.Code.All parts)
              (collect_codes (List.map find_goal parts)))
    | Operation (Or, parts) ->
        Option.map (fun parts -> Catalog.Code.Any parts) (collect_codes (List.map find_goal parts))
    | Operation (Not, [ inner ]) ->
        Option.map (fun inner -> Catalog.Code.Not inner) (find_goal inner)
    | Operation (Implies, [ premise; conclusion ]) -> (
        match (find_goal premise, find_goal conclusion) with
        | Some premise, Some conclusion -> Some (Implies { premise; conclusion })
        | _ -> None)
    | Operation (operator, [ left; right ]) -> (
        match find_comparison_operator operator with
        | Some comparison -> find_comparison left comparison right
        | None -> find_value_code context term)
    | term -> find_value_code context term
  and find_comparison left comparison right =
    match (find_value_code context left, find_value_code context right) with
    | Some left, Some right -> Some (Catalog.Code.Compared { left; comparison; right })
    | _ -> None
  in
  if
    List.exists (fun symbol -> List.mem symbol context.State.entry) (Logic.list_free_constants term)
  then find_goal term
  else None

let read_requires_clause (signature : Syntax.signature) (origin : Core.origin) =
  let expression = match origin with Written id | Desugared { construct = id; _ } -> id in
  match
    List.find_opt
      (fun (clause : Syntax.clause) ->
        match clause.kind with Requires written -> written.id = expression | _ -> false)
      signature.clauses
  with
  | Some clause -> clause
  | None -> raise_bug "a `requires` is read that the signature does not write"

let add_requires (context : State.context) (frame : State.frame) required : Catalog.Prover.fix list
    =
  match find_signature context with
  | Some (signature, body) when not context.inherits_precondition ->
      let place : Catalog.Prover.clause_place =
        match context.requires_clause_being_read with
        | Some origin -> Before_clause (Written (read_requires_clause signature origin).id)
        | None -> Before_body (Written body.id)
      in
      [
        Add_requires
          {
            place;
            required;
            premise =
              (match frame.condition with
              | Logic.Boolean true -> None
              | condition -> find_goal_code context condition);
            condition = context.condition;
          };
      ]
  | Some _ | None -> []

let make_obligation (context : State.context) (frame : State.frame) location obligation goal =
  Query.make_obligation context.query ~condition:frame.condition location obligation goal

let make_closed_obligation (context : State.context) (frame : State.frame) location obligation goal
    =
  if not frame.makes_obligations then None
  else if not (Logic.mentions frame.bound goal || Logic.mentions frame.bound frame.condition) then
    Some (make_obligation context frame location obligation goal)
  else
    let names = List.map (fun (name, _, _) -> name) frame.binders in
    let goal =
      match Query.list_scope_facts context.query names with
      | [] -> goal
      | facts -> Logic.( ==> ) (Logic.conjunction facts) goal
    in
    match close_over_binders frame (Logic.( ==> ) frame.condition goal) with
    | Some closed ->
        Some
          (make_obligation context
             { frame with condition = Logic.Boolean true }
             location obligation closed)
    | None -> None

let remove_panic_condition (uses : Types.capability_set) =
  Types.replace_capabilities
    (function Types.Capability_unless_values _ -> Some Types.no_capabilities | _ -> None)
    uses

let is_panic_obligation : Diagnostic.Code.prover -> bool = function
  | Overflow | Division | Shift | Panic -> true
  | _ -> false

let oblige ?cited ?(fixes = []) ?(can_be_required = true) ?(is_proven_by_evaluation = false)
    ?holds_when (context : State.context) (frame : State.frame) location obligation goal =
  let code = Catalog.Prover_description.find_code obligation in
  let holds_when = Option.value holds_when ~default:context.obligation_condition in
  if
    (is_panic_obligation code && context.panics)
    || (Option.is_some context.panic_condition && not (is_panic_obligation code))
    || not
         (holds_when = context.condition
         || (code = Diagnostic.Code.Termination && context.keeps_termination)
         || (is_panic_obligation code && context.keeps_failures))
  then assume context frame goal
  else
    let is_held =
      match goal with
      | Logic.Boolean _ -> false
      | _ ->
          (not is_proven_by_evaluation) && frame.makes_obligations
          && (not (Logic.mentions frame.bound goal || Logic.mentions frame.bound frame.condition))
          && Query.holds context.query ~under:frame.condition goal
    in
    if is_held then assume context frame goal
    else
      match
        make_closed_obligation context frame location obligation
          (Query.add_quantifier_facts context.query
             ~binders:(List.map (fun (name, _, _) -> name) frame.binders)
             goal)
      with
      | Some obligation ->
          let is_home_body = is_home context frame.source && frame.makes_obligations in
          let fixes =
            match fixes with
            | [] when is_home_body && can_be_required -> (
                match find_goal_code context goal with
                | Some _ when Logic.is_refuted goal -> []
                | Some required -> add_requires context frame [ Clause required ]
                | None -> [])
            | fixes -> fixes
          in
          let fixes =
            if is_panic_obligation code && context.can_declare_panic && is_home_body then
              fixes @ make_panic_fix context
            else fixes
          in
          Query.add_obligation context.query { obligation with cited; fixes };
          assume context frame goal
      | None -> ()

let quote (source : State.source) origin : Catalog.Prover.quoted = { key = source.key; origin }

let describe_local (context : State.context) (frame : State.frame) :
    Locals.local -> Catalog.Prover.value = function
  | Core_local Self -> Self_value
  | local -> (
      match
        ( Tables.Local_table.find_opt context.local_names local,
          Tables.Local_table.find_opt context.local_origins local )
      with
      | Some name, _ -> Named name
      | None, Some origin -> Quoted (quote frame.source origin)
      | None, None -> Temporary)

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
  let value = declare_fresh context frame prefix (declare_sort context ty) in
  assume context frame (make_in_range ty value);
  value

let bind (frame : State.frame) local ty term =
  {
    frame with
    State.locals = Locals.add local term frame.locals;
    types = Locals.add local ty frame.types;
  }

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

let restrict (frame : State.frame) condition =
  { frame with State.condition = Logic.( &&& ) frame.condition condition }

let merge_known_on_paths (paths : (Logic.term * State.frame) list) =
  let merge_known pick ~is_same ~on_differing =
    let keys =
      List.fold_left
        (fun keys ((_, frame) : Logic.term * State.frame) ->
          Locals.fold (fun key _ keys -> Locals.add key () keys) (pick frame) keys)
        Locals.empty paths
    in
    Locals.mapi
      (fun key () ->
        let each =
          List.map (fun (condition, frame) -> (condition, Locals.find_opt key (pick frame))) paths
        in
        match each with
        | (_, Some one) :: rest
          when List.for_all
                 (fun (_, other) ->
                   match other with Some other -> is_same one other | None -> false)
                 rest ->
            one
        | _ -> on_differing each)
      keys
  in
  let guard condition = List.map (fun (on, known) -> (Logic.( &&& ) condition on, known)) in
  let guard_each each =
    List.concat_map
      (fun (condition, known) -> guard condition (Option.value ~default:[] known))
      each
  in
  let aliases = merge_known (fun frame -> frame.aliases) ~is_same:( = ) ~on_differing:guard_each in
  let lends = merge_known (fun frame -> frame.lends) ~is_same:( == ) ~on_differing:guard_each in
  (aliases, lends)

let name_path_condition context (frame : State.frame) condition =
  match condition with
  | Logic.Boolean _ | Logic.Symbol _ -> condition
  | _ when (not frame.makes_obligations) || Logic.mentions frame.bound condition -> condition
  | _ ->
      let path = declare_fresh context frame "path" Logic.Bool in
      add_frame_fact context frame (Logic.equal path condition);
      path

let merge context ?value_type ~condition
    (paths : (Logic.term * State.frame * Logic.term option) list) =
  let first = match paths with (_, first, _) :: _ -> first | [] -> raise_bug "no paths meet" in
  let is_expression = not first.makes_obligations in
  let aliases, lends = merge_known_on_paths (List.map (fun (on, frame, _) -> (on, frame)) paths) in
  let merged = { first with condition; aliases; lends } in
  let choose values =
    match List.rev values with
    | (_, _, last) :: earlier ->
        List.fold_left (fun otherwise (on, _, term) -> Logic.ite on term otherwise) last earlier
    | [] -> raise_bug "a value that no path gives"
  in
  let define prefix sort (values : (Logic.term * State.frame * Logic.term) list) =
    match values with
    | (_, _, term) :: rest
      when List.for_all (fun (_, _, other) -> other == term || other = term) rest ->
        term
    | _
      when List.for_all
             (fun (_, _, term) -> match term with Logic.Boolean _ -> true | _ -> false)
             values ->
        Logic.disjunction
          (List.filter_map
             (fun (on, _, term) -> if term = Logic.Boolean true then Some on else None)
             values)
    | _
      when is_expression
           || List.exists
                (fun (on, (frame : State.frame), term) ->
                  Logic.mentions first.bound on
                  || Logic.mentions first.bound frame.condition
                  || Logic.mentions first.bound term)
                values ->
        choose values
    | _ ->
        let symbol = declare_fresh context first prefix sort in
        List.iter
          (fun (_, (frame : State.frame), term) ->
            add_frame_fact context first (Logic.( ==> ) frame.condition (Logic.equal symbol term)))
          values;
        symbol
  in
  let find_held pick =
    let values =
      List.filter_map
        (fun (on, frame, _) -> Option.map (fun term -> (on, frame, term)) (pick frame))
        paths
    in
    if List.length values = List.length paths then Some values else None
  in
  let keys =
    List.fold_left
      (fun keys (_, (frame : State.frame), _) ->
        Locals.fold (fun key _ keys -> Locals.add key () keys) frame.locals keys)
      Locals.empty paths
  in
  let locals =
    Locals.mapi
      (fun id () ->
        match find_held (fun frame -> Locals.find_opt id frame.locals) with
        | Some values ->
            let sort =
              match find_local_type context first id with
              | Some ty -> declare_sort context ty
              | None -> (
                  match values with (_, _, Logic.Boolean _) :: _ -> Logic.Bool | _ -> Logic.Int)
            in
            define "joined" sort values
        | None -> (
            match
              List.find_map
                (fun (_, (frame : State.frame), _) -> Locals.find_opt id frame.locals)
                paths
            with
            | Some term -> term
            | None -> raise_bug "a local that no path binds"))
      keys
  in
  let types =
    List.fold_left
      (fun types (_, (frame : State.frame), _) ->
        Locals.union (fun _ ty _ -> Some ty) types frame.types)
      Locals.empty paths
  in
  let self =
    match (first.self_type, find_held (fun frame -> frame.self)) with
    | Some ty, Some values -> Some (define "self" (declare_sort context ty) values)
    | _ -> first.self
  in
  let list_renamings (frame : State.frame) =
    let renamings =
      Locals.fold
        (fun id joined renamings ->
          match Locals.find_opt id frame.locals with
          | Some incoming when incoming != joined && incoming <> joined ->
              (incoming, joined) :: renamings
          | _ -> renamings)
        locals []
    in
    match (frame.self, self) with
    | Some incoming, Some joined when incoming <> joined -> (incoming, joined) :: renamings
    | _ -> renamings
  in
  let spent =
    Costs.join_spent first.spent
      ~paths:
        (List.map
           (fun (on, (frame : State.frame), _) -> (on, list_renamings frame, frame.spent))
           paths)
      ~name:(fun amount ->
        if Logic.mentions first.bound amount then amount
        else
          let symbol = declare_fresh context first "spent" Logic.Int in
          add_frame_fact context first (Logic.equal symbol amount);
          symbol)
  in
  let value =
    let values =
      List.filter_map
        (fun (on, frame, value) -> Option.map (fun term -> (on, frame, term)) value)
        paths
    in
    if values = [] || List.length values <> List.length paths then None
    else
      match value_type with
      | Some ty -> Some (define "value" (declare_sort context ty) values)
      | None -> Some (choose values)
  in
  let yielded_so_far =
    match (context.lending, find_held (fun frame -> frame.yielded_so_far)) with
    | Some { part_type; _ }, Some values ->
        Some
          (define "parts"
             (declare_sort context
                (Types.Named
                   { path = Well_known.make_path Sequence; arguments = [ Types.Type part_type ] }))
             values)
    | _ -> first.yielded_so_far
  in
  ({ merged with locals; types; spent; self; yielded_so_far }, value)

let join context ?value_type frames =
  match frames with
  | [] -> None
  | [ (frame, value) ] -> Some (frame, value)
  | (first, _) :: _ ->
      let condition =
        name_path_condition context first
          (Logic.disjunction (List.map (fun ((frame : State.frame), _) -> frame.condition) frames))
      in
      Some
        (merge context ?value_type ~condition
           (List.map (fun ((frame : State.frame), value) -> (frame.condition, frame, value)) frames))

let join_frames context frames =
  Option.map fst (join context (List.map (fun frame -> (frame, None)) frames))
