let run_ghost_code (context : State.context) (frame : State.frame) (code : Mir.t) =
  let unfinished = context.unfinished in
  context.unfinished <- [];
  Fun.protect
    ~finally:(fun () -> context.unfinished <- unfinished)
    (fun () ->
      ignore
        (Lambdas.run_lambda_body context { frame with is_ghost = true } ~lambdas:code.lambdas
           code.body ~type_:Types.unit);
      Logic.disjunction context.unfinished)

let assume_extensional context frame (ty : Types.ty) left right =
  match ty with
  | Types.Named { path; arguments = [ Types.Type element ] }
    when Path.equal path Models.sequence_path -> (
      let index = Facts.make_fresh_name context "index" in
      match
        ( Models.index_sequence context element left (Logic.Symbol index),
          Models.index_sequence context element right (Logic.Symbol index) )
      with
      | Some at_a, Some at_b ->
          let length = Models.make_sequence_length context element in
          Facts.add_frame_fact context frame
            Logic.(
              equal (length left) (length right)
              &&& forall
                    ( [ (index, Int) ],
                      less_equal (int 0) (Symbol index)
                      &&& less (Symbol index) (length left)
                      ==> equal at_a at_b )
              ==> equal left right)
      | _ -> ())
  | Types.Named { path; arguments }
    when Well_known.is Finite_set path || Well_known.is Finite_map path -> (
      let finite_map = Well_known.is Finite_map path in
      match arguments with
      | Types.Type key :: rest ->
          let each = Facts.make_fresh_name context "key" in
          let apply_function method_ output inputs =
            Models.make_finite_function context method_ ~arguments output inputs
          in
          let key_sort = Facts.declare_sort context key in
          let has =
            apply_function
              (if finite_map then Well_known.Finite_map_contains_key else Finite_set_contains)
              Logic.Bool
              [ (Logic.Symbol each, key_sort) ]
          in
          let same =
            if finite_map then
              match rest with
              | [ Types.Type value_type ] ->
                  let get =
                    apply_function Finite_map_get
                      (Facts.declare_sort context value_type)
                      [ (Logic.Symbol each, key_sort) ]
                  in
                  Logic.(
                    equal (has left) (has right) &&& (has left ==> equal (get left) (get right)))
              | _ -> Logic.equal (has left) (has right)
            else Logic.equal (has left) (has right)
          in
          Facts.add_frame_fact context frame
            Logic.(
              forall ([ (each, key_sort) ], Facts.make_in_range key (Symbol each) ==> same)
              ==> equal left right)
      | _ -> ())
  | _ -> ()

let make_sequence context frame (ty : Types.ty) ~element values =
  let literal = Facts.arrive context frame "literal" ty in
  let sequence =
    match ty with
    | Types.Named { path; _ } when Path.equal path Models.sequence_path -> Some literal
    | Types.Named { path; _ } when Well_known.find_builtin_type path = Some Array ->
        Models.find_model context ty literal ~element
    | _ -> None
  in
  Option.map
    (fun sequence ->
      Validity.assume_valid context frame ty literal;
      Facts.assume context frame
        (Logic.equal
           (Models.make_sequence_length context element sequence)
           (Logic.int (List.length values)));
      List.iteri
        (fun index item ->
          match Models.index_sequence context element sequence (Logic.int index) with
          | Some at -> Facts.assume context frame (Logic.equal at item)
          | None -> ())
        values;
      literal)
    sequence

let assume_only_members context frame label sort contains members =
  let each = Facts.make_fresh_name context label in
  Facts.assume context frame
    (Logic.forall
       ( [ (each, sort) ],
         Logic.( ==> ) (contains (Logic.Symbol each))
           (Logic.disjunction (List.map (Logic.equal (Logic.Symbol each)) members)) ))

let make_set context frame (ty : Types.ty) ~element values =
  let arguments = [ Types.Type element ] in
  let literal = Facts.arrive context frame "literal" ty in
  let model =
    match ty with
    | Types.Named { path; _ } when Well_known.is Finite_set path -> Some literal
    | _ -> None
  in
  Option.map
    (fun model ->
      Validity.assume_valid context frame ty literal;
      let element_sort = Facts.declare_sort context element in
      let contains value =
        Models.make_finite_function context Finite_set_contains ~arguments Logic.Bool
          [ (value, element_sort) ]
          model
      in
      List.iter (fun value -> Facts.assume context frame (contains value)) values;
      assume_only_members context frame "value" element_sort contains values;
      let size =
        Models.make_finite_function context Finite_set_size ~arguments Logic.Int [] model
      in
      Facts.assume context frame (Logic.less_equal size (Logic.int (List.length values)));
      literal)
    model

let apply_list_literal context frame (site : Invocation.site) values =
  let ty = Facts.substitute_type context frame site.type_ in
  let location = Facts.locate context frame.source site.origin in
  let element =
    match ty with
    | Types.Named { arguments = Types.Type element :: _; _ } -> element
    | _ -> Facts.raise_unsupported location "a literal of `%s`" (Types.show ty)
  in
  let literal =
    match make_sequence context frame ty ~element values with
    | Some literal -> literal
    | None -> (
        match make_set context frame ty ~element values with
        | Some literal -> literal
        | None -> Facts.raise_unsupported location "a literal of `%s`" (Types.show ty))
  in
  (frame, literal)

let reads_only_literals (parameter : Core.local) (clause : Mir.formula) =
  let is_parameter local =
    match clause.locals.(local).kind with
    | Source { local = core; _ } -> core = parameter
    | Temporary | Lent _ -> false
  in
  let is_literal_only = ref true in
  Mir.iter_places_read
    (fun (place : Mir.place) ->
      match place with
      | { root = Local local; projections = Field field :: _ }
        when is_parameter local && field = Well_known.show_field Template_literals ->
          ()
      | { root = Local local; _ } when is_parameter local -> is_literal_only := false
      | _ -> ())
    clause.value;
  !is_literal_only

let apply_template context (frame : State.frame) (site : Invocation.site) ~trait ~name ~receiver
    ~evidence ~literals value_ =
  let location = Facts.locate context frame.source site.origin in
  let tag_type = Facts.substitute_type context frame site.type_ in
  match evidence with
  | Core.Impl { impl; _ } -> (
      let path = Path.Method { owner = impl; name; receiver } in
      match Contracts.find_method_contract context.lookups trait name receiver evidence with
      | Some contract ->
          let callee_clauses = contract.callee_clauses in
          let entry =
            Validity.bind_arguments frame callee_clauses
              ~arguments:[ (0, value_) ]
              ~substitution:Types.no_substitution
          in
          let is_evaluable (requirement : Mir.requirement) =
            match (evidence, callee_clauses.parameters) with
            | Impl { substitution; _ }, [ parameter ] when Types.is_empty_substitution substitution
              ->
                requirement.is_executable && reads_only_literals parameter.local requirement.clause
            | _ -> false
          in
          let template_check =
            {
              Obligation.from_template = path;
              literals;
              clauses =
                List.filter_map Fun.id
                  (List.mapi
                     (fun index requirement ->
                       if is_evaluable requirement then Some index else None)
                     callee_clauses.requires);
            }
          in
          List.iteri
            (fun index (requirement : Mir.requirement) ->
              let template_clause =
                if List.mem index template_check.clauses then
                  Some { Obligation.check = template_check; clause = index }
                else None
              in
              Facts.oblige ?template_clause context frame Requires location
                [
                  Text "This template may not meet `";
                  Facts.quote callee_clauses.callee requirement.clause.origin;
                  Text "`, which its tag requires.";
                ]
                (snd (Validity.read_specification context entry requirement.clause)))
            callee_clauses.requires;
          let result = Facts.arrive context frame "tagged" tag_type in
          Validity.assume_valid context frame tag_type result;
          List.iter
            (fun (clause : Mir.formula) ->
              Facts.assume context frame
                (snd
                   (Validity.read_specification context { entry with result = Some result } clause)))
            callee_clauses.ensures;
          let frame =
            Operations.spend context frame
              (Amounts.compute_callee_amount context frame ~is_recursive:false
                 ~clauses:(Contracts.list_declared_clauses contract)
                 ~bind_frame:(fun clauses ->
                   {
                     (Validity.bind_arguments frame clauses
                        ~arguments:[ (0, value_) ]
                        ~substitution:Types.no_substitution)
                     with
                     result = Some result;
                   })
                 ~uses:Types.no_capabilities ~values:[] ~change:None)
          in
          (frame, result)
      | None ->
          Facts.raise_unsupported location "a tagged template whose tag the prover cannot read")
  | Bound | Dynamic ->
      Facts.raise_unsupported location "a tagged template whose tag the prover cannot read"

let apply_map_literal context frame ~(ty : Types.ty) ~location terms =
  let key_type, value_type =
    match ty with
    | Types.Named { arguments = [ Types.Type key; Types.Type value_type ]; _ } -> (key, value_type)
    | _ -> Facts.raise_unsupported location "a literal of `%s`" (Types.show ty)
  in
  List.iteri
    (fun index (_, key_term, _) ->
      List.iteri
        (fun other (other_key, other_term, _) ->
          if other > index then
            Facts.oblige context frame Disjoint
              (match other_key with
              | Some origin -> Facts.locate context frame.source origin
              | None -> location)
              [
                Text "The key `";
                (match other_key with
                | Some origin -> Facts.quote frame.source origin
                | None -> Text "this key");
                Text "` may equal an earlier key of this map.";
              ]
              (Logic.not_ (Operations.make_equality context frame key_type key_term other_term)))
        terms)
    terms;
  let arguments = [ Types.Type key_type; Types.Type value_type ] in
  let literal = Facts.arrive context frame "literal" ty in
  let model =
    match ty with
    | Types.Named { path; _ } when Well_known.is Finite_map path -> literal
    | _ -> Facts.raise_unsupported location "a literal of `%s`" (Types.show ty)
  in
  Validity.assume_valid context frame ty literal;
  let key_sort = Facts.declare_sort context key_type in
  let has key =
    Models.make_finite_function context Finite_map_contains_key ~arguments Logic.Bool
      [ (key, key_sort) ]
      model
  in
  let get key =
    Models.make_finite_function context Finite_map_get ~arguments
      (Facts.declare_sort context value_type)
      [ (key, key_sort) ]
      model
  in
  List.iter
    (fun (_, key, entry) -> Facts.assume context frame Logic.(has key &&& equal (get key) entry))
    terms;
  assume_only_members context frame "key" key_sort has (List.map (fun (_, key, _) -> key) terms);
  Facts.assume context frame
    (Logic.equal
       (Models.make_finite_function context Finite_map_size ~arguments Logic.Int [] model)
       (Logic.int (List.length terms)));
  (frame, literal)

let literal_bytes_limit = 256

let make_text_value context frame (ty : Types.ty) text =
  let symbol = Logic.Symbol.Text_literal { type_ = ty; text } in
  let literal = Logic.Symbol symbol in
  Facts.run_once context (Value_of symbol) (fun () ->
      Facts.declare context (Logic.Constant (symbol, Facts.declare_sort context ty));
      Validity.assume_valid context
        { frame with condition = Logic.Boolean true; bound = []; binders = [] }
        ty literal;
      let byte = Types.make_builtin UInt8 in
      let assume_holds model =
        Facts.add_fact context
          (Logic.equal
             (Models.make_sequence_length context byte model)
             (Logic.int (String.length text)));
        if String.length text <= literal_bytes_limit then
          String.iteri
            (fun index character ->
              match Models.index_sequence context byte model (Logic.int index) with
              | Some at -> Facts.add_fact context (Logic.equal at (Logic.int (Char.code character)))
              | None -> ())
            text
      in
      Option.iter assume_holds (Models.find_model context ty literal ~element:byte);
      match Facts.find_constructors context ty with
      | Some [ (None, [ (field, Types.Named { path; arguments = [ Types.Type element ] }) ]) ]
        when Well_known.find_builtin_type path = Some Storage && Types.equal element byte ->
          assume_holds
            (Intrinsics.make_buffer_model context Storage byte
               (Logic.Apply (Facts.make_selector_symbol ty None field, [ literal ])))
      | _ -> ());
  literal

let make_owner_of_view context frame ~(view : Types.ty) ~(owner : Types.ty) viewed =
  let symbol = Logic.Symbol.Owner_of_view owner in
  Facts.declare context
    (Logic.Function (symbol, [ Facts.declare_sort context view ], Facts.declare_sort context owner));
  let converted = Logic.Apply (symbol, [ viewed ]) in
  Validity.assume_valid context frame owner converted;
  let element =
    match owner with
    | Types.Named { arguments = [ Types.Type element ]; _ } -> element
    | _ -> Types.make_builtin UInt8
  in
  (match
     ( Models.find_model context owner converted ~element,
       Models.find_model context view viewed ~element )
   with
  | Some owned, Some elements -> Facts.assume context frame (Logic.equal owned elements)
  | _ ->
      Facts.raise_bug "`%s` and its view `%s` have no model of one type" (Types.show owner)
        (Types.show view));
  converted

let project_field context frame ty variant field field_type term =
  let part = Validity.select_field context ty variant field term in
  Amounts.assume_typed context frame (Facts.make_in_range field_type part);
  if context.ranking then begin
    Facts.assume context frame
      (Logic.less (Models.rank context field_type part) (Models.rank context ty term))
  end;
  part

let assume_contract_for_every_argument context (frame : State.frame) (contract : State.contract)
    parameters value =
  let inputs = List.map (fun (name, _) -> Logic.Symbol name) parameters in
  let over =
    {
      frame with
      State.bound = List.map fst parameters @ frame.bound;
      binders =
        List.rev_map (fun (name, sort) -> (name, sort, Logic.Boolean true)) parameters
        @ frame.binders;
      makes_obligations = false;
    }
  in
  let read (clauses : State.clauses) =
    {
      (Validity.bind_arguments over clauses
         ~arguments:(List.mapi (fun index input -> (index, input)) inputs)
         ~substitution:Types.no_substitution)
      with
      result = Some value;
    }
  in
  try
    let precondition_clauses = Contracts.select_precondition_clauses contract in
    let conjoin_requires (clauses : State.clauses) =
      Logic.conjunction
        (List.map
           (fun requirement -> snd (Validity.read_specification context (read clauses) requirement))
           (Facts.list_clauses clauses.requires))
    in
    let required = conjoin_requires precondition_clauses in
    List.iter
      (fun (clauses : State.clauses) ->
        let required =
          if clauses == precondition_clauses then required else conjoin_requires clauses
        in
        List.iter
          (fun clause ->
            match snd (Validity.read_specification context (read clauses) clause) with
            | ensured -> (
                match Facts.close_over_binders over (Logic.( ==> ) required ensured) with
                | Some closed -> Facts.add_fact context closed
                | None -> ())
            | exception Facts.Unsupported _ -> ())
          clauses.ensures)
      (Contracts.list_declared_clauses contract)
  with Facts.Unsupported _ -> ()

let translate_named_function (context : State.context) (frame : State.frame)
    (site : Invocation.site) path type_arguments (contract : State.contract) ~is_argument =
  let ty = Facts.substitute_type context frame site.type_ in
  let callee_clauses = contract.callee_clauses in
  (match ty with
  | Types.Function function_type
    when callee_clauses.requires <> [] && frame.makes_obligations && not is_argument ->
      let inputs = Validity.declare_callback_arguments context frame function_type.inputs in
      if List.length callee_clauses.parameters = List.length inputs then begin
        let inside =
          Validity.bind_arguments frame callee_clauses
            ~arguments:(List.mapi (fun index input -> (index, input)) inputs)
            ~substitution:Types.no_substitution
        in
        List.iter
          (fun (requirement : Mir.formula) ->
            Facts.oblige context frame Requires
              (Facts.locate context frame.source site.origin)
              [
                Text
                  (Printf.sprintf
                     "`%s` is used as a value of `%s`, which promises nothing of its arguments, so \
                      its `"
                     (Path.show path) (Types.show ty));
                Facts.quote callee_clauses.callee requirement.origin;
                Text "` may not hold.";
              ]
              (snd (Validity.read_specification context inside requirement)))
          (Facts.list_clauses callee_clauses.requires)
      end
  | _ -> ());
  let type_arguments = List.map (Types.substitute_argument frame.substitution) type_arguments in
  let symbol = Logic.Symbol.Function_value { callee = path; type_arguments } in
  Facts.declare context (Logic.Constant (symbol, Facts.declare_sort context ty));
  let term = Logic.Symbol symbol in
  (match ty with
  | Types.Function function_type
    when Lambdas.is_in_the_logic function_type && contract.is_logic_function ->
      let parameters = Lambdas.make_parameter_symbols context frame function_type in
      let inputs = List.map (fun (name, _) -> Logic.Symbol name) parameters in
      let function_symbol = Logic.Symbol.Function { callee = path; type_arguments } in
      Facts.declare context
        (Logic.Function
           ( function_symbol,
             List.map snd parameters,
             Facts.declare_sort context function_type.output ));
      let value = Logic.Apply (function_symbol, inputs) in
      if type_arguments = [] then
        assume_contract_for_every_argument context frame contract parameters value;
      Facts.add_frame_fact context frame
        (Logic.forall
           (parameters, Logic.equal (Lambdas.apply_function context function_type term inputs) value))
  | _ -> ());
  term

let translate_global_value (context : State.context) frame (site : Invocation.site) path
    type_arguments ~is_argument =
  match Contracts.find_function_contract context.lookups path with
  | Some contract ->
      translate_named_function context frame site path type_arguments contract ~is_argument
  | None ->
      Facts.raise_unsupported
        (Facts.locate context frame.source site.origin)
        "a function the prover cannot read, used as a value"

let evaluate_constant (context : State.context) frame path =
  match
    (Contracts.find_source context.lookups path, Mir.read_initializer context.lookups.mir path)
  with
  | Some (constant_source, _, _), Some { form = code; _ } ->
      let symbol = Logic.Symbol.Constant path in
      let empty =
        {
          frame with
          State.source = constant_source;
          locals = Locals.empty;
          types = Locals.empty;
          makes_obligations = false;
          self = None;
          condition = Logic.Boolean true;
          bound = [];
          binders = [];
        }
      in
      Facts.run_once context (Value_of symbol) (fun () ->
          let ty = Interface.Definition.read_constant_type context.lookups.interface path in
          Facts.declare context (Logic.Constant (symbol, Facts.declare_sort context ty));
          let _, defined_value =
            Validity.run_without_costs context (fun () ->
                Amounts.run_code context empty code ~type_:ty)
          in
          Facts.add_fact context (Logic.equal (Logic.Symbol symbol) defined_value));
      Logic.Symbol symbol
  | _ -> Facts.raise_bug "the constant %s has no initializer" (Path.show path)

let evaluate_field_default context frame ty variant field =
  match (ty, Validity.find_type_source context ty) with
  | Types.Named { path; _ }, Some source -> (
      match Mir.read_defaults context.lookups.mir path with
      | Some { form = Field_defaults defaults; _ } -> (
          match
            List.find_opt
              (fun (default : Mir.t Mir.field_default) ->
                default.variant = variant && default.field = field)
              defaults
          with
          | Some default ->
              let inside = Validity.make_type_frame context frame source ty ~self:None in
              snd
                (Amounts.run_code context inside default.value
                   ~type_:(Facts.substitute_type context inside default.type_))
          | None -> Facts.raise_bug "the field %s of %s has no default" field (Types.show ty))
      | Some { form = Parameter_defaults _; _ } | None ->
          Facts.raise_bug "a type with no MIR of its defaults")
  | _ -> Facts.raise_bug "a default of %s, which has no source" (Types.show ty)

let check_built context frame (site : Invocation.site) ty term =
  Lambdas.check_valid context frame
    (Facts.locate context frame.source site.origin)
    ty term ~deep:false ~when_:"for the value built here"

let is_indirect (context : State.context) (ty : Types.ty) variant =
  match (ty, variant) with
  | Types.Named { path; _ }, Some variant -> (
      match Interface.Definition.find_interface context.lookups.interface path with
      | Some (Interface.Environment.Type_interface { shape = Sum variants; _ }) ->
          List.exists
            (fun (written : Types.variant) -> written.variant_name = variant && written.indirect)
            variants
      | _ -> false)
  | _ -> false

let construct_amount context frame (ty : Types.ty) variant (counter : Costs.counter) =
  match counter.resource with
  | Metric (Allocations | Allocated_bytes) when not (is_indirect context ty variant) -> Costs.zero
  | Metric Allocations -> Logic.int 1
  | Metric Allocated_bytes when counter.counting = Units -> Logic.int 1
  | Metric Allocated_bytes ->
      let symbol = Logic.Symbol.Block_bytes { type_ = ty; variant } in
      Facts.declare context (Logic.Constant (symbol, Logic.Int));
      Facts.add_frame_fact context frame (Logic.less_equal (Logic.int 1) (Logic.Symbol symbol));
      Logic.Symbol symbol
  | Metric Time | Calls _ -> Costs.zero

let apply_construct context frame (site : Invocation.site) variant
    (fields : (string * Logic.term option) list) =
  let ty = Facts.substitute_type context frame site.type_ in
  if Types.equal ty Types.unit then begin
    ignore (Facts.declare_sort context Types.unit);
    (frame, Logic.Apply (Logic.Symbol.Unit, []))
  end
  else
    let frame, field_terms =
      List.fold_left
        (fun (frame, field_terms) (field, written) ->
          match written with
          | Some term -> (frame, field_terms @ [ (field, term) ])
          | None ->
              ( frame,
                field_terms @ [ (field, evaluate_field_default context frame ty variant field) ] ))
        (frame, []) fields
    in
    let frame = Operations.spend context frame (construct_amount context frame ty variant) in
    match Facts.find_constructors context ty with
    | Some shape ->
        ignore (Facts.declare_sort context ty);
        let shaped = match List.assoc_opt variant shape with Some fields -> fields | None -> [] in
        let read_field_value (name, _) =
          match List.assoc_opt name field_terms with
          | Some term -> term
          | None -> Facts.raise_bug "a construction of %s without its field %s" (Types.show ty) name
        in
        let built =
          Logic.Apply (Facts.make_constructor_symbol ty variant, List.map read_field_value shaped)
        in
        check_built context frame site ty built;
        (frame, built)
    | None -> (frame, Facts.arrive context frame "built" ty)

let make_text_match context location ty term text =
  let byte = Types.make_builtin UInt8 in
  match Models.find_model context ty term ~element:byte with
  | Some model ->
      Logic.conjunction
        (Logic.equal
           (Models.make_sequence_length context byte model)
           (Logic.int (String.length text))
        :: List.init (String.length text) (fun index ->
            match Models.index_sequence context byte model (Logic.int index) with
            | Some at -> Logic.equal at (Logic.int (Char.code text.[index]))
            | None -> Logic.Boolean false))
  | None -> Facts.raise_unsupported location "a string pattern on `%s`" (Types.show ty)

let make_log_facts number ~halving =
  let log number = Logic.Apply (Logic.Symbol.Cost_log, [ number ]) in
  let basic =
    Logic.(
      less_equal (int 0) (log number)
      &&& (less_equal number (int 0) ==> equal (log number) (int 0))
      &&& (greater_equal number (int 0) ==> less_equal (log number) number))
  in
  if halving then
    let half = Logic.Operation (Div, [ number; Logic.int 2 ]) in
    ( [ basic; Logic.(greater_equal number (int 1) ==> equal (log number) (add (log half) (int 1))) ],
      Some half )
  else ([ basic ], None)

let make_log_order left right =
  let log number = Logic.Apply (Logic.Symbol.Cost_log, [ number ]) in
  Logic.(
    less_equal left right
    ==> less_equal (log left) (log right)
    &&& (less_equal right left ==> less_equal (log right) (log left)))

let declare_log context frame log_argument =
  Facts.declare context (Logic.Function (Logic.Symbol.Cost_log, [ Logic.Int ], Logic.Int));
  let rec add log_argument ~halving =
    match List.assoc_opt log_argument context.logs with
    | Some true -> ()
    | Some false when not halving -> ()
    | seen ->
        if seen = None then
          List.iter
            (fun (other, _) ->
              Facts.add_frame_fact context frame (make_log_order log_argument other))
            context.logs;
        context.logs <- (log_argument, halving) :: List.remove_assoc log_argument context.logs;
        let facts, half = make_log_facts log_argument ~halving in
        List.iter (Facts.add_frame_fact context frame) facts;
        Option.iter (fun half -> add half ~halving:false) half
  in
  if not (Logic.mentions frame.bound log_argument) then add log_argument ~halving:true;
  (match log_argument with
  | Logic.Integer limit ->
      Facts.add_frame_fact context frame
        (Logic.equal
           (Logic.Apply (Logic.Symbol.Cost_log, [ log_argument ]))
           (Logic.int (if Z.sign limit <= 0 then 0 else Z.numbits limit)))
  | _ -> ());
  Logic.Apply (Logic.Symbol.Cost_log, [ log_argument ])

let apply_specification_function context frame ~location (measure : Core.specification_function)
    values ~unconverted ~types =
  match (measure, values, unconverted, types) with
  | Log, [ log_argument ], [ unconverted ], _ ->
      let log = declare_log context frame log_argument in
      (match Facts.find_bounds unconverted with
      | Some (_, high) when not (Logic.mentions frame.bound log_argument) ->
          Facts.add_frame_fact context frame
            Logic.(less_equal log_argument (Integer high) ==> less_equal log (int (Z.numbits high)))
      | _ -> ());
      (frame, log)
  | Power, [ base; exponent ], _, _ -> (frame, Operations.declare_power context frame base exponent)
  | Callback_cost metric, [ function_term ], _, [ function_type ] ->
      (frame, Calls.make_callback_cost context frame metric function_type function_term)
  | _ -> Facts.raise_unsupported location "this specification function"

let copy_value ?literal (context : State.context) frame ty term =
  if
    context.counters = []
    || Interface.Impls.is_plain context.lookups.interface
         ~list_bounds:(Operations.compute_current_bounds context)
         ty
       && not (try Amounts.has_potential context ty with Facts.Unsupported _ -> true)
  then frame
  else
    let declare_copy_cost metric =
      Amounts.declare_method_cost context frame metric
        (Well_known.make_method_path Copyable_copy)
        ~trait_arguments:[] ty
    in
    Operations.spend context frame (fun (counter : Costs.counter) ->
        match (literal, counter.resource, counter.counting) with
        | _, Metric Time, Units ->
            let time = match literal with Some _ -> Costs.zero | None -> declare_copy_cost Time in
            let copy_potential =
              try Amounts.compute_potential context frame ty term
              with Facts.Unsupported _ -> Costs.zero
            in
            Costs.minus (Costs.plus time (Logic.int 1)) copy_potential
        | Some text, Metric (Allocations | Allocated_bytes), Units
        | Some text, Metric Allocations, _ ->
            Logic.int (if text = "" then 0 else 1)
        | Some text, Metric Allocated_bytes, (At_most | Exactly) -> Logic.int (String.length text)
        | Some _, Calls _, _ -> Costs.zero
        | None, Metric ((Allocations | Allocated_bytes) as metric), _ ->
            Amounts.compute_amount_within context frame counter (declare_copy_cost metric)
        | _, Metric Time, (At_most | Exactly) | None, Calls _, _ ->
            Operations.declare_unknown_amount context frame counter)
