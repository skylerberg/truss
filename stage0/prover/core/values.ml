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

let assume_extensional (frame : State.frame) (ty : Types.ty) left right =
  match ty with
  | Types.Named { path; arguments = [ Types.Type element ] }
    when Path.equal path Encoding.sequence_path -> (
      let index = Query.make_fresh_name frame.query "index" in
      match
        ( Models.index_sequence frame.environment frame.query element left (Logic.Symbol index),
          Models.index_sequence frame.environment frame.query element right (Logic.Symbol index) )
      with
      | Some at_a, Some at_b ->
          let length = Models.make_sequence_length frame.query element in
          Facts.add_frame_fact frame
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
          let each = Query.make_fresh_name frame.query "key" in
          let apply_function method_ output inputs =
            Models.make_finite_function frame.query method_ ~arguments output inputs
          in
          let key_sort = Encoding.sort_of key in
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
                    apply_function Finite_map_get (Encoding.sort_of value_type)
                      [ (Logic.Symbol each, key_sort) ]
                  in
                  Logic.(
                    equal (has left) (has right) &&& (has left ==> equal (get left) (get right)))
              | _ -> Logic.equal (has left) (has right)
            else Logic.equal (has left) (has right)
          in
          Facts.add_frame_fact frame
            Logic.(
              forall ([ (each, key_sort) ], Encoding.make_in_range key (Symbol each) ==> same)
              ==> equal left right)
      | _ -> ())
  | _ -> ()

let make_sequence (context : State.context) (frame : State.frame) (ty : Types.ty) ~element values =
  let literal = Encoding.arrive frame "literal" ty in
  let sequence =
    match ty with
    | Types.Named { path; _ } when Path.equal path Encoding.sequence_path -> Some literal
    | Types.Named { path; _ } when Well_known.find_builtin_type path = Some Array ->
        Models.find_model context ty literal ~element
    | _ -> None
  in
  Option.map
    (fun sequence ->
      Validity.assume_valid context frame ty literal;
      Facts.assume frame
        (Logic.equal
           (Models.make_sequence_length context.query element sequence)
           (Logic.int (List.length values)));
      List.iteri
        (fun index item ->
          match
            Models.index_sequence context.environment context.query element sequence
              (Logic.int index)
          with
          | Some at -> Facts.assume frame (Logic.equal at item)
          | None -> ())
        values;
      literal)
    sequence

let assume_only_members (frame : State.frame) label sort contains members =
  let each = Query.make_fresh_name frame.query label in
  Facts.assume frame
    (Logic.forall
       ( [ (each, sort) ],
         Logic.( ==> ) (contains (Logic.Symbol each))
           (Logic.disjunction (List.map (Logic.equal (Logic.Symbol each)) members)) ))

let make_set (context : State.context) (frame : State.frame) (ty : Types.ty) ~element values =
  let arguments = [ Types.Type element ] in
  let literal = Encoding.arrive frame "literal" ty in
  let model =
    match ty with
    | Types.Named { path; _ } when Well_known.is Finite_set path -> Some literal
    | _ -> None
  in
  Option.map
    (fun model ->
      Validity.assume_valid context frame ty literal;
      let element_sort = Encoding.sort_of element in
      let contains value =
        Models.make_finite_function context.query Finite_set_contains ~arguments Logic.Bool
          [ (value, element_sort) ]
          model
      in
      List.iter (fun value -> Facts.assume frame (contains value)) values;
      assume_only_members frame "value" element_sort contains values;
      let size =
        Models.make_finite_function context.query Finite_set_size ~arguments Logic.Int [] model
      in
      Facts.assume frame (Logic.less_equal size (Logic.int (List.length values)));
      literal)
    model

let apply_list_literal (context : State.context) (frame : State.frame) (site : Invocation.site)
    values =
  let ty = Encoding.substitute_type frame site.type_ in
  let location = Facts.locate frame site.origin in
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

let apply_map_literal (context : State.context) (frame : State.frame) ~(ty : Types.ty) ~location
    terms =
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
            Obligations.oblige frame
              (match other_key with Some origin -> Facts.locate frame origin | None -> location)
              (Duplicate_key { key = Option.map (Facts.quote frame.source) other_key })
              (Logic.not_ (Operations.make_equality context frame key_type key_term other_term)))
        terms)
    terms;
  let arguments = [ Types.Type key_type; Types.Type value_type ] in
  let literal = Encoding.arrive frame "literal" ty in
  let model =
    match ty with
    | Types.Named { path; _ } when Well_known.is Finite_map path -> literal
    | _ -> Facts.raise_unsupported location (Literal_of ty)
  in
  Validity.assume_valid context frame ty literal;
  let key_sort = Encoding.sort_of key_type in
  let has key =
    Models.make_finite_function context.query Finite_map_contains_key ~arguments Logic.Bool
      [ (key, key_sort) ]
      model
  in
  let get key =
    Models.make_finite_function context.query Finite_map_get ~arguments
      (Encoding.sort_of value_type)
      [ (key, key_sort) ]
      model
  in
  List.iter
    (fun (_, key, entry) -> Facts.assume frame Logic.(has key &&& equal (get key) entry))
    terms;
  assume_only_members frame "key" key_sort has (List.map (fun (_, key, _) -> key) terms);
  Facts.assume frame
    (Logic.equal
       (Models.make_finite_function context.query Finite_map_size ~arguments Logic.Int [] model)
       (Logic.int (List.length terms)));
  (frame, literal)

let literal_bytes_limit = 256

let rec make_literal_value (context : State.context) (frame : State.frame) (ty : Types.ty)
    (value : Language.Literal.t) =
  let symbol = Logic.Symbol.Literal { type_ = ty; value } in
  let literal = Logic.Symbol symbol in
  Query.run_once context.query (Value_of symbol) (fun () ->
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
        Query.add_fact context.query
          (Logic.equal (Models.make_sequence_length context.query element model) (Logic.int count));
        List.iteri
          (fun index at_index ->
            match
              Models.index_sequence context.environment context.query element model
                (Logic.int index)
            with
            | Some at -> Query.add_fact context.query (Logic.equal at at_index)
            | None -> ())
          elements
      in
      Option.iter assume_holds (Models.find_model context ty literal ~element);
      match Encoding.find_constructors context.environment ty with
      | Some [ (None, [ (field, field_type) ]) ] -> (
          let part = Logic.Apply (Encoding.make_selector_symbol ty None field, [ literal ]) in
          match field_type with
          | Types.Named { path; arguments = [ Types.Type stored ] }
            when Option.is_some (Well_known.find_builtin_type path) ->
              if Well_known.find_builtin_type path = Some Storage && Types.equal stored element then
                assume_holds (Intrinsics.make_buffer_model Storage element part)
          | _ ->
              Query.add_fact context.query
                (Logic.equal part (make_literal_value context frame field_type value)))
      | _ -> ());
  literal

let rec find_abstracted_selection query term =
  match term with
  | Logic.Apply ((Logic.Symbol.Field _ as selector), [ whole ]) ->
      Option.map
        (fun (parameters, abstracted) -> (parameters, Logic.Apply (selector, [ abstracted ])))
        (find_abstracted_selection query whole)
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
        (Query.find_argument_sorts query callee)
  | _ -> None

let assume_field_range_of_every_result (environment : State.environment) query ty variant field
    field_type term =
  match find_abstracted_selection query term with
  | Some (parameters, abstracted) -> (
      let selection = Encoding.select_field environment ty variant field abstracted in
      match Encoding.make_in_range field_type selection with
      | Logic.Boolean true -> ()
      | range ->
          Query.run_once query (Field_in_range selection) (fun () ->
              let range =
                match variant with
                | Some name ->
                    Logic.(
                      Is (Encoding.make_constructor_symbol ty (Some name), abstracted) ==> range)
                | None -> range
              in
              Query.add_fact query (Logic.forall ~trigger:[ selection ] (parameters, range))))
  | None -> ()

let project_field (context : State.context) (frame : State.frame) ty variant field field_type term =
  let part = Encoding.select_field context.environment ty variant field term in
  Contract_axioms.assume_typed context frame (Encoding.make_in_range field_type part);
  if Logic.mentions (List.map (fun (name, _, _) -> name) frame.binders) term then
    assume_field_range_of_every_result context.environment context.query ty variant field field_type
      term;
  if context.environment.ranking then begin
    Facts.assume frame
      (Logic.less
         (Models.rank context.environment context.query field_type part)
         (Models.rank context.environment context.query ty term))
  end;
  part

let evaluate_constant (context : State.context) (frame : State.frame) path =
  match
    ( Contracts.find_source context.environment.lookups path,
      Mir.read_initializer context.environment.lookups.mir path )
  with
  | Some (constant_source, _, _), Some { form = code; _ } ->
      let symbol : Logic.symbol =
        if Cycles.is_evaluated_constant context.environment path code then
          Evaluated (Constant_value path)
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
      Query.run_once context.query (Value_of symbol) (fun () ->
          let ty =
            Interface.Definition.read_constant_type context.environment.lookups.interface path
          in
          Query.declare context.query (Logic.Constant (symbol, Encoding.sort_of ty));
          let _, defined_value =
            Counters.run_without_counters context (fun () ->
                Lambdas.run_code context empty code ~type_:ty)
          in
          Query.add_fact context.query (Logic.equal (Logic.Symbol symbol) defined_value));
      Logic.Symbol symbol
  | _ -> Facts.raise_bug "the constant %s has no initializer" (Path.show path)

let evaluate_field_default (context : State.context) (frame : State.frame) ty variant field =
  match (ty, Validity.find_type_source context ty) with
  | Types.Named { path; _ }, Some source -> (
      match Mir.read_defaults context.environment.lookups.mir path with
      | Some { form = Field_defaults defaults; _ } -> (
          match
            List.find_opt
              (fun (default : Mir.t Mir.field_default) ->
                default.variant = variant && default.field = field)
              defaults
          with
          | Some default ->
              let inside = Validity.make_type_frame frame source ty ~self:None in
              let evaluated, value =
                Lambdas.run_code context inside default.value
                  ~type_:(Encoding.substitute_type inside default.type_)
              in
              ({ frame with spent = evaluated.spent }, value)
          | None -> Facts.raise_bug "the field %s of %s has no default" field (Types.show ty))
      | Some { form = Parameter_defaults _; _ } | None ->
          Facts.raise_bug "a type with no MIR of its defaults")
  | _ -> Facts.raise_bug "a default of %s, which has no source" (Types.show ty)

let check_built (context : State.context) (frame : State.frame) (site : Invocation.site) ty term =
  Validity.check_valid context frame (Facts.locate frame site.origin) ty term ~deep:false
    ~moment:Built_here

let apply_construct (context : State.context) (frame : State.frame) (site : Invocation.site) variant
    (fields : (string * Logic.term option) list) =
  let ty = Encoding.substitute_type frame site.type_ in
  if Types.equal ty Types.unit then (frame, Logic.Apply (Logic.Symbol.Unit, []))
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
      Counters.spend context frame (Amounts.compute_construction_amount frame ty variant)
    in
    match Encoding.find_constructors context.environment ty with
    | Some shape ->
        let shaped = match List.assoc_opt variant shape with Some fields -> fields | None -> [] in
        let read_field_value (name, _) =
          match List.assoc_opt name field_terms with
          | Some term -> term
          | None -> Facts.raise_bug "a construction of %s without its field %s" (Types.show ty) name
        in
        let built =
          Logic.Apply (Encoding.make_constructor_symbol ty variant, List.map read_field_value shaped)
        in
        check_built context frame site ty built;
        let frame = Potentials.spend_declared_potential context frame ty built in
        (frame, built)
    | None -> (frame, Encoding.arrive frame "built" ty)

let make_text_match (context : State.context) location ty term text =
  let byte = Types.make_builtin UInt8 in
  match Models.find_model context ty term ~element:byte with
  | Some model ->
      Logic.conjunction
        (Logic.equal
           (Models.make_sequence_length context.query byte model)
           (Logic.int (String.length text))
        :: List.init (String.length text) (fun index ->
            match
              Models.index_sequence context.environment context.query byte model (Logic.int index)
            with
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

let declare_log (context : State.context) (frame : State.frame) log_argument =
  let rec add log_argument ~halving =
    match List.assoc_opt log_argument context.logs with
    | Some true -> ()
    | Some false when not halving -> ()
    | seen ->
        if seen = None then
          List.iter
            (fun (other, _) -> Facts.add_frame_fact frame (make_log_order log_argument other))
            context.logs;
        context.logs <- (log_argument, halving) :: List.remove_assoc log_argument context.logs;
        let facts, half = make_log_facts log_argument ~halving in
        List.iter (Facts.add_frame_fact frame) facts;
        Option.iter (fun half -> add half ~halving:false) half
  in
  if not (Logic.mentions frame.bound log_argument) then add log_argument ~halving:true;
  (match log_argument with
  | Logic.Integer limit ->
      Facts.add_frame_fact frame
        (Logic.equal
           (Logic.Apply (Logic.Symbol.Integer_log, [ log_argument ]))
           (Logic.int (if Z.sign limit <= 0 then 0 else Z.numbits limit)))
  | _ -> ());
  Logic.Apply (Logic.Symbol.Integer_log, [ log_argument ])

let apply_specification_function (context : State.context) (frame : State.frame) ~location
    (measure : Core.specification_function) values ~unconverted ~types =
  match (measure, values, unconverted, types) with
  | Log, [ log_argument ], [ unconverted ], _ ->
      let log = declare_log context frame log_argument in
      (match Encoding.find_bounds unconverted with
      | Some (_, high) when not (Logic.mentions frame.bound log_argument) ->
          Facts.add_frame_fact frame
            Logic.(less_equal log_argument (Integer high) ==> less_equal log (int (Z.numbits high)))
      | _ -> ());
      (frame, log)
  | Power, [ base; exponent ], _, _ -> (frame, Operations.declare_power context frame base exponent)
  | Callback_cost metric, [ function_term ], _, [ function_type ] ->
      (frame, Amounts.make_callback_cost context frame metric function_type function_term)
  | Callback_ensures, _, _, Types.Function function_type :: _ ->
      (frame, Callbacks.apply_callback_ensures function_type values)
  | _ -> Facts.raise_unsupported location Specification_function
