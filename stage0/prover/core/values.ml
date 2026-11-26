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
    | _ -> Facts.raise_unsupported location (Literal_of ty)
  in
  let literal =
    match make_sequence context frame ty ~element values with
    | Some literal -> literal
    | None -> (
        match make_set context frame ty ~element values with
        | Some literal -> literal
        | None -> Facts.raise_unsupported location (Literal_of ty))
  in
  (frame, literal)

let apply_map_literal context frame ~(ty : Types.ty) ~location terms =
  let key_type, value_type =
    match ty with
    | Types.Named { arguments = [ Types.Type key; Types.Type value_type ]; _ } -> (key, value_type)
    | _ -> Facts.raise_unsupported location (Literal_of ty)
  in
  List.iteri
    (fun index (_, key_term, _) ->
      List.iteri
        (fun other (other_key, other_term, _) ->
          if other > index then
            Facts.oblige context frame
              (match other_key with
              | Some origin -> Facts.locate context frame.source origin
              | None -> location)
              (Duplicate_key { key = Option.map (Facts.quote frame.source) other_key })
              (Logic.not_ (Operations.make_equality context frame key_type key_term other_term)))
        terms)
    terms;
  let arguments = [ Types.Type key_type; Types.Type value_type ] in
  let literal = Facts.arrive context frame "literal" ty in
  let model =
    match ty with
    | Types.Named { path; _ } when Well_known.is Finite_map path -> literal
    | _ -> Facts.raise_unsupported location (Literal_of ty)
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

let rec make_literal_value context frame (ty : Types.ty) (value : Language.Literal.t) =
  let symbol = Logic.Symbol.Literal { type_ = ty; value } in
  let literal = Logic.Symbol symbol in
  Facts.run_once context (Value_of symbol) (fun () ->
      Facts.declare context (Logic.Constant (symbol, Facts.declare_sort context ty));
      Validity.assume_valid context
        { frame with condition = Logic.Boolean true; bound = []; binders = [] }
        ty literal;
      let element, count, elements =
        match (value, ty) with
        | Text text, _ ->
            ( Types.make_builtin UInt8,
              String.length text,
              if String.length text <= literal_bytes_limit then
                List.init (String.length text) (fun index -> Logic.int (Char.code text.[index]))
              else [] )
        | Elements elements, Types.Named { arguments = [ Types.Type element ]; _ } ->
            ( element,
              List.length elements,
              List.map (make_literal_value context frame element) elements )
        | Elements _, _ -> Facts.raise_bug "a literal of elements has the type `%s`" (Types.show ty)
      in
      let assume_holds model =
        Facts.add_fact context
          (Logic.equal (Models.make_sequence_length context element model) (Logic.int count));
        List.iteri
          (fun index at_index ->
            match Models.index_sequence context element model (Logic.int index) with
            | Some at -> Facts.add_fact context (Logic.equal at at_index)
            | None -> ())
          elements
      in
      Option.iter assume_holds (Models.find_model context ty literal ~element);
      match Facts.find_constructors context ty with
      | Some [ (None, [ (field, field_type) ]) ] -> (
          let part = Logic.Apply (Facts.make_selector_symbol ty None field, [ literal ]) in
          match field_type with
          | Types.Named { path; arguments = [ Types.Type stored ] }
            when Option.is_some (Well_known.find_builtin_type path) ->
              if Well_known.find_builtin_type path = Some Storage && Types.equal stored element then
                assume_holds (Intrinsics.make_buffer_model context Storage element part)
          | _ ->
              Facts.add_fact context
                (Logic.equal part (make_literal_value context frame field_type value)))
      | _ -> ());
  literal

let rec find_abstracted_selection context term =
  match term with
  | Logic.Apply ((Logic.Symbol.Field _ as selector), [ whole ]) ->
      Option.map
        (fun (parameters, abstracted) -> (parameters, Logic.Apply (selector, [ abstracted ])))
        (find_abstracted_selection context whole)
  | Logic.Apply ((Logic.Symbol.Function _ as callee), _) ->
      Option.map
        (fun sorts ->
          let parameters =
            List.mapi
              (fun index sort ->
                (Logic.Symbol.Variable { label = "ranged"; numbers = [ index ] }, sort))
              sorts
          in
          ( parameters,
            Logic.Apply (callee, List.map (fun (name, _) -> Logic.Symbol name) parameters) ))
        (Facts.find_argument_sorts context callee)
  | _ -> None

let assume_field_range_of_every_result context ty variant field field_type term =
  match find_abstracted_selection context term with
  | Some (parameters, abstracted) -> (
      let selection = Validity.select_field context ty variant field abstracted in
      match Facts.make_in_range field_type selection with
      | Logic.Boolean true -> ()
      | range ->
          Facts.run_once context (Field_in_range selection) (fun () ->
              let range =
                match variant with
                | Some name ->
                    Logic.(Is (Facts.make_constructor_symbol ty (Some name), abstracted) ==> range)
                | None -> range
              in
              Facts.add_fact context (Logic.forall ~trigger:[ selection ] (parameters, range))))
  | None -> ()

let project_field context (frame : State.frame) ty variant field field_type term =
  let part = Validity.select_field context ty variant field term in
  Contract_axioms.assume_typed context frame (Facts.make_in_range field_type part);
  if Logic.mentions (List.map (fun (name, _, _) -> name) frame.binders) term then
    assume_field_range_of_every_result context ty variant field field_type term;
  if context.ranking then begin
    Facts.assume context frame
      (Logic.less (Models.rank context field_type part) (Models.rank context ty term))
  end;
  part

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
            Facts.oblige context frame
              (Facts.locate context frame.source site.origin)
              (Value_contract
                 { path; type_ = ty; clause = Facts.quote callee_clauses.callee requirement.origin })
              (snd (Validity.read_specification context inside requirement)))
          (Facts.list_clauses callee_clauses.requires)
      end
  | _ -> ());
  let type_arguments =
    List.map (Types.substitute_argument_erased frame.substitution) type_arguments
  in
  let symbol = Logic.Symbol.Function_value { callee = path; type_arguments } in
  Facts.declare context (Logic.Constant (symbol, Facts.declare_sort context ty));
  let term = Logic.Symbol symbol in
  (match ty with
  | Types.Function function_type
    when Lambdas.is_in_the_logic function_type && contract.is_logic_function ->
      let parameters = Lambdas.make_parameter_symbols context frame function_type in
      let inputs = List.map (fun (name, _) -> Logic.Symbol name) parameters in
      let sorts = List.map snd parameters in
      let function_symbol =
        Contract_axioms.declare_function context ~path ~type_arguments ~sorts
          ~result_type:function_type.output
      in
      let value = Logic.Apply (function_symbol, inputs) in
      if type_arguments = [] then
        Contract_axioms.state context frame
          { symbol = function_symbol; sorts; term = value; is_limited = false }
          contract
          ~substitution_of:(fun _ -> Types.no_substitution)
          ~result_type:function_type.output
          ~group_member:
            (Cycles.find_group_member context frame
               (Core.Function
                  { path; instantiation = { type_arguments; capability_arguments = [] } }))
          ~is_on_bound_values:true;
      Facts.add_frame_fact context frame
        (Logic.forall
           (parameters, Logic.equal (Lambdas.apply_function context function_type term inputs) value))
  | _ -> ());
  term

let translate_global_value (context : State.context) frame (site : Invocation.site) path
    type_arguments ~is_argument =
  match Contracts.find_function_contract context path with
  | Some contract ->
      translate_named_function context frame site path type_arguments contract ~is_argument
  | None ->
      Facts.raise_unsupported
        (Facts.locate context frame.source site.origin)
        Unreadable_function_value

let evaluate_constant (context : State.context) frame path =
  match
    (Contracts.find_source context.lookups path, Mir.read_initializer context.lookups.mir path)
  with
  | Some (constant_source, _, _), Some { form = code; _ } ->
      let symbol : Logic.symbol =
        if Cycles.is_evaluated_constant context path code then Evaluated (Constant_value path)
        else Constant path
      in
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
            Counters.run_without_counters context (fun () ->
                Lambdas.run_code context empty code ~type_:ty)
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
              let evaluated, value =
                Lambdas.run_code context inside default.value
                  ~type_:(Facts.substitute_type context inside default.type_)
              in
              ({ frame with spent = evaluated.spent }, value)
          | None -> Facts.raise_bug "the field %s of %s has no default" field (Types.show ty))
      | Some { form = Parameter_defaults _; _ } | None ->
          Facts.raise_bug "a type with no MIR of its defaults")
  | _ -> Facts.raise_bug "a default of %s, which has no source" (Types.show ty)

let check_built context frame (site : Invocation.site) ty term =
  Lambdas.check_valid context frame
    (Facts.locate context frame.source site.origin)
    ty term ~deep:false ~moment:Built_here

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
              let frame, value = evaluate_field_default context frame ty variant field in
              (frame, field_terms @ [ (field, value) ]))
        (frame, []) fields
    in
    let frame =
      Counters.spend context frame (Amounts.compute_construction_amount context frame ty variant)
    in
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
        let frame = Potentials.spend_declared_potential context frame ty built in
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
  | None -> Facts.raise_unsupported location (String_pattern_on ty)

let make_log_facts number ~halving =
  let log number = Logic.Apply (Logic.Symbol.Integer_log, [ number ]) in
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
  let log number = Logic.Apply (Logic.Symbol.Integer_log, [ number ]) in
  Logic.(
    less_equal left right
    ==> less_equal (log left) (log right)
    &&& (less_equal right left ==> less_equal (log right) (log left)))

let declare_log context frame log_argument =
  Facts.declare context (Logic.Function (Logic.Symbol.Integer_log, [ Logic.Int ], Logic.Int));
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
           (Logic.Apply (Logic.Symbol.Integer_log, [ log_argument ]))
           (Logic.int (if Z.sign limit <= 0 then 0 else Z.numbits limit)))
  | _ -> ());
  Logic.Apply (Logic.Symbol.Integer_log, [ log_argument ])

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
      (frame, Amounts.make_callback_cost context frame metric function_type function_term)
  | Callback_ensures, _, _, Types.Function function_type :: _ ->
      (frame, Lambdas.apply_callback_ensures context function_type values)
  | _ -> Facts.raise_unsupported location Specification_function
