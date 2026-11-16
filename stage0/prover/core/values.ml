open Core
open State
open Facts
open Contracts
open Validity
open Operations
open Models
open Lambdas
open Intrinsics
open Amounts
open Calls

let ghost_code context frame (code : Mir.t) =
  let proving = context.proving and unfinished = context.unfinished in
  context.proving <- true;
  context.unfinished <- [];
  Fun.protect
    ~finally:(fun () ->
      context.proving <- proving;
      context.unfinished <- unfinished)
    (fun () ->
      ignore (body_run context frame ~lambdas:code.lambdas code.body ~type_:Types.unit);
      Logic.disjunction context.unfinished)

let finite_map_path : Path.t = Well_known.path Finite_map

let extensional context frame (ty : Types.ty) left right =
  match ty with
  | Types.Named { path; arguments = [ Types.Type element ] } when Path.equal path sequence_path -> (
      let index = fresh_name context "index" in
      match
        ( sequence_at context element left (Logic.Symbol index),
          sequence_at context element right (Logic.Symbol index) )
      with
      | Some at_a, Some at_b ->
          let length = sequence_length context element in
          fact context frame
            Logic.(
              equal (length left) (length right)
              &&& forall
                    ( [ (index, Int) ],
                      Operation ("<=", [ int 0; Symbol index ])
                      &&& Operation ("<", [ Symbol index; length left ])
                      ==> equal at_a at_b )
              ==> equal left right)
      | _ -> ())
  | Types.Named { path; arguments }
    when Path.equal path finite_set_path || Path.equal path finite_map_path -> (
      let finite_map = Path.equal path finite_map_path in
      match arguments with
      | Types.Type key :: rest ->
          let each = fresh_name context "key" in
          let function_ name output inputs = finite_function context ty name output inputs in
          let key_sort = sort_of context key in
          let has =
            function_
              (if finite_map then "contains_key" else "contains")
              Logic.Bool
              [ (Logic.Symbol each, key_sort) ]
          in
          let same =
            if finite_map then
              match rest with
              | [ Types.Type value_type ] ->
                  let get =
                    function_ "get" (sort_of context value_type) [ (Logic.Symbol each, key_sort) ]
                  in
                  Logic.(
                    equal (has left) (has right) &&& (has left ==> equal (get left) (get right)))
              | _ -> Logic.equal (has left) (has right)
            else Logic.equal (has left) (has right)
          in
          fact context frame
            Logic.(
              forall ([ (each, key_sort) ], in_range key (Symbol each) ==> same)
              ==> equal left right)
      | _ -> ())
  | _ -> ()

let sequence_of context frame (ty : Types.ty) ~element values =
  let literal = arrive context frame "literal" ty in
  let sequence =
    match ty with
    | Types.Named { path; _ } when Path.equal path sequence_path -> Some literal
    | Types.Named { path; _ } when Intrinsic.builtin_of_path path = Some Array ->
        model_of context ty literal ~element
    | _ -> None
  in
  Option.map
    (fun sequence ->
      assume_valid context frame ty literal;
      assume context frame
        (Logic.equal (sequence_length context element sequence) (Logic.int (List.length values)));
      List.iteri
        (fun index item ->
          match sequence_at context element sequence (Logic.int index) with
          | Some at -> assume context frame (Logic.equal at item)
          | None -> ())
        values;
      literal)
    sequence

let only_members context frame label sort contains members =
  let each = fresh_name context label in
  assume context frame
    (Logic.forall
       ( [ (each, sort) ],
         Logic.( ==> ) (contains (Logic.Symbol each))
           (Logic.disjunction (List.map (Logic.equal (Logic.Symbol each)) members)) ))

let set_of context frame (ty : Types.ty) ~element values =
  let finite = Types.Named { path = finite_set_path; arguments = [ Types.Type element ] } in
  let literal = arrive context frame "literal" ty in
  let model =
    match ty with
    | Types.Named { path; _ } when Path.equal path finite_set_path -> Some literal
    | _ -> None
  in
  Option.map
    (fun model ->
      assume_valid context frame ty literal;
      let element_sort = sort_of context element in
      let contains value =
        finite_function context finite "contains" Logic.Bool [ (value, element_sort) ] model
      in
      List.iter (fun value -> assume context frame (contains value)) values;
      only_members context frame "value" element_sort contains values;
      let size = finite_function context finite "size" Logic.Int [] model in
      assume context frame (Costs.at_most size (Logic.int (List.length values)));
      literal)
    model

let apply_list_literal context frame (site : Invocation.site) values =
  let ty = substituted context frame site.type_ in
  let location = locate context frame.source site.origin in
  let element =
    match ty with
    | Types.Named { arguments = Types.Type element :: _; _ } -> element
    | _ -> unsupported location "a literal of `%s`" (Types.show ty)
  in
  let literal =
    match sequence_of context frame ty ~element values with
    | Some literal -> literal
    | None -> (
        match set_of context frame ty ~element values with
        | Some literal -> literal
        | None -> unsupported location "a literal of `%s`" (Types.show ty))
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
      | { root = Local local; projections = Field "literals" :: _ } when is_parameter local -> ()
      | { root = Local local; _ } when is_parameter local -> is_literal_only := false
      | _ -> ())
    clause.value;
  !is_literal_only

let apply_template context frame (site : Invocation.site) ~trait ~name ~receiver ~evidence ~literals
    value_ =
  let location = locate context frame.source site.origin in
  let tag_type = substituted context frame site.type_ in
  match evidence with
  | Impl { impl; _ } -> (
      let path = Path.Method { owner = impl; name; receiver } in
      match method_contract context.lookups trait name receiver evidence with
      | Some contract ->
          let own = List.hd contract.parts in
          let entry = part_frame frame own ~arguments:[ (0, value_) ] ~substitution:[] in
          let is_evaluable (requirement : Mir.requirement) =
            match (evidence, own.parameters) with
            | Impl { arguments = []; _ }, [ parameter ] ->
                requirement.is_executable && reads_only_literals parameter.local requirement.clause
            | _ -> false
          in
          let template_check =
            {
              from_template = path;
              literals;
              clauses =
                List.filter_map Fun.id
                  (List.mapi
                     (fun index requirement ->
                       if is_evaluable requirement then Some index else None)
                     own.requires);
            }
          in
          List.iteri
            (fun index (requirement : Mir.requirement) ->
              let template_clause =
                if List.mem index template_check.clauses then
                  Some { check = template_check; clause = index }
                else None
              in
              oblige ?template_clause context frame Requires location
                [
                  Text "This template may not meet `";
                  quote own.callee requirement.clause.origin;
                  Text "`, which its tag requires.";
                ]
                (snd (specification_value context entry requirement.clause)))
            own.requires;
          let result = arrive context frame "tagged" tag_type in
          assume_valid context frame tag_type result;
          List.iter
            (fun (clause : Mir.formula) ->
              assume context frame
                (snd (specification_value context { entry with result = Some result } clause)))
            own.ensures;
          let frame =
            spend context frame
              (callee_amount context frame ~path ~parts:contract.parts
                 ~bound_frame:(fun part ->
                   {
                     (part_frame frame part ~arguments:[ (0, value_) ] ~substitution:[]) with
                     result = Some result;
                   })
                 ~uses:[] ~values:[] ~change:None)
          in
          (frame, result)
      | None -> unsupported location "a tagged template whose tag the prover cannot read")
  | Bound | Dynamic -> unsupported location "a tagged template whose tag the prover cannot read"

let apply_map_literal context frame ~(ty : Types.ty) ~location terms =
  let key_type, value_type =
    match ty with
    | Types.Named { arguments = [ Types.Type key; Types.Type value_type ]; _ } -> (key, value_type)
    | _ -> unsupported location "a literal of `%s`" (Types.show ty)
  in
  List.iteri
    (fun index (_, key_term, _) ->
      List.iteri
        (fun other (other_key, other_term, _) ->
          if other > index then
            oblige context frame Disjoint
              (match other_key with
              | Some origin -> locate context frame.source origin
              | None -> location)
              [
                Text "The key `";
                (match other_key with
                | Some origin -> quote frame.source origin
                | None -> Text "this key");
                Text "` may equal an earlier key of this map.";
              ]
              (Logic.not_ (equal_of context frame key_type key_term other_term)))
        terms)
    terms;
  let finite =
    Types.Named
      { path = finite_map_path; arguments = [ Types.Type key_type; Types.Type value_type ] }
  in
  let literal = arrive context frame "literal" ty in
  let model =
    match ty with
    | Types.Named { path; _ } when Path.equal path finite_map_path -> literal
    | _ -> unsupported location "a literal of `%s`" (Types.show ty)
  in
  assume_valid context frame ty literal;
  let key_sort = sort_of context key_type in
  let has key =
    finite_function context finite "contains_key" Logic.Bool [ (key, key_sort) ] model
  in
  let get key =
    finite_function context finite "get" (sort_of context value_type) [ (key, key_sort) ] model
  in
  List.iter
    (fun (_, key, entry) -> assume context frame Logic.(has key &&& equal (get key) entry))
    terms;
  only_members context frame "key" key_sort has (List.map (fun (_, key, _) -> key) terms);
  assume context frame
    (Logic.equal
       (finite_function context finite "size" Logic.Int [] model)
       (Logic.int (List.length terms)));
  (frame, literal)

let literal_bytes_limit = 256

let text_value context frame (ty : Types.ty) text =
  let symbol = Symbol.Text_literal { type_ = ty; text } in
  let literal = Logic.Symbol symbol in
  once context (Value_of symbol) (fun () ->
      declare context (Logic.Constant (symbol, sort_of context ty));
      assume_valid context
        { frame with condition = Logic.Boolean true; bound = []; binders = [] }
        ty literal;
      let byte = Types.make_builtin UInt8 in
      let holds model =
        add_fact context
          (Logic.equal (sequence_length context byte model) (Logic.int (String.length text)));
        if String.length text <= literal_bytes_limit then
          String.iteri
            (fun index character ->
              match sequence_at context byte model (Logic.int index) with
              | Some at -> add_fact context (Logic.equal at (Logic.int (Char.code character)))
              | None -> ())
            text
      in
      Option.iter holds (model_of context ty literal ~element:byte);
      match constructors context ty with
      | Some [ (None, [ (field, Types.Named { path; arguments = [ Types.Type element ] }) ]) ]
        when Intrinsic.builtin_of_path path = Some Storage && Types.equal element byte ->
          holds
            (buffer_model context Storage byte
               (Logic.Apply (selector_name ty None field, [ literal ])))
      | _ -> ());
  literal

let field_of context frame ty variant field field_type term =
  let part = selected context ty variant field term in
  assume_typed context frame (in_range field_type part);
  if context.ranking then begin
    let below = rank context field_type part in
    assume context frame
      Logic.(
        Operation ("<=", [ int 0; below ]) &&& Operation ("<", [ below; rank context ty term ]))
  end;
  part

let contract_for_every_argument context frame (contract : contract) parameters value =
  let inputs = List.map (fun (name, _) -> Logic.Symbol name) parameters in
  let over =
    {
      frame with
      bound = List.map fst parameters @ frame.bound;
      binders =
        List.rev_map (fun (name, sort) -> (name, sort, Logic.Boolean true)) parameters
        @ frame.binders;
      makes_obligations = false;
    }
  in
  let read (part : part) =
    {
      (part_frame over part
         ~arguments:(List.mapi (fun index input -> (index, input)) inputs)
         ~substitution:[])
      with
      result = Some value;
    }
  in
  try
    let requiring =
      match contract.parts with
      | own :: others -> if own.requires <> [] || others = [] then [ own ] else others
      | [] -> []
    in
    let requires_of parts =
      Logic.conjunction
        (List.concat_map
           (fun (part : part) ->
             List.map
               (fun requirement -> snd (specification_value context (read part) requirement))
               (clauses part.requires))
           parts)
    in
    let required = requires_of requiring in
    List.iter
      (fun (part : part) ->
        let required = if List.memq part requiring then required else requires_of [ part ] in
        List.iter
          (fun clause ->
            match snd (specification_value context (read part) clause) with
            | ensured -> (
                match closed_over_binders over (Logic.( ==> ) required ensured) with
                | Some closed -> add_fact context closed
                | None -> ())
            | exception Foreign_unsupported _ -> ())
          part.ensures)
      contract.parts
  with Unsupported _ | Foreign_unsupported _ -> ()

let named_function context frame (site : Invocation.site) path type_arguments contract ~is_argument
    =
  if context.terminates && frame.makes_obligations && is_in_recursion_group context path then
    oblige context frame Termination
      (locate context frame.source site.origin)
      [
        Text
          (Printf.sprintf
             "Naming `%s` as a value reaches back here, and such a use passes no arguments the \
              prover can compare, so the recursion cannot be shown to end: write it as a direct \
              call on a part."
             (Path.show path));
      ]
      (Logic.Boolean false);
  let ty = substituted context frame site.type_ in
  (match (ty, contract.parts) with
  | Types.Function function_type, own :: _
    when own.requires <> [] && frame.makes_obligations && not is_argument ->
      let inputs = callback_arguments context frame function_type.inputs in
      if List.length own.parameters = List.length inputs then begin
        let inside =
          part_frame frame own
            ~arguments:(List.mapi (fun index input -> (index, input)) inputs)
            ~substitution:[]
        in
        List.iter
          (fun (requirement : Mir.formula) ->
            oblige context frame Requires
              (locate context frame.source site.origin)
              [
                Text
                  (Printf.sprintf
                     "`%s` is used as a value of `%s`, which promises nothing of its arguments, so \
                      its `"
                     (Path.show path) (Types.show ty));
                quote own.callee requirement.origin;
                Text "` may not hold.";
              ]
              (snd (specification_value context inside requirement)))
          (clauses own.requires)
      end
  | _ -> ());
  let instance = List.map (Types.substitute_argument frame.substitution) type_arguments in
  let symbol = Symbol.Function_value { callee = path; instance } in
  declare context (Logic.Constant (symbol, sort_of context ty));
  let term = Logic.Symbol symbol in
  (match ty with
  | Types.Function function_type when in_the_logic function_type && contract.is_logic_function ->
      let parameters = parameters_of context frame function_type in
      let inputs = List.map (fun (name, _) -> Logic.Symbol name) parameters in
      let function_symbol = Symbol.Function { callee = path; instance } in
      declare context
        (Logic.Function
           (function_symbol, List.map snd parameters, sort_of context function_type.output));
      let value = Logic.Apply (function_symbol, inputs) in
      if instance = [] then contract_for_every_argument context frame contract parameters value;
      fact context frame
        (Logic.forall (parameters, Logic.equal (applied context function_type term inputs) value))
  | _ -> ());
  let constant_time =
    List.exists
      (fun (part : part) ->
        List.exists
          (fun (cost : Mir.cost) ->
            match cost with
            | { resource = Time; bound = Order_of amount; amortized = false; _ } ->
                literal amount <> None
            | _ -> false)
          part.costs)
      contract.parts
  in
  (if constant_time then
     let time = time_of context frame ty term in
     fact context frame (Logic.equal time (Logic.int 1)));
  term

let global_value context frame (site : Invocation.site) path type_arguments ~is_argument =
  match function_contract context.lookups path with
  | Some contract -> named_function context frame site path type_arguments contract ~is_argument
  | None ->
      unsupported
        (locate context frame.source site.origin)
        "a function the prover cannot read, used as a value"

let constant_type context path =
  match Interface.Definition.read_constant_type context.lookups.interface path with
  | Some ty -> ty
  | None -> raise (Foreign_unsupported "a constant with errors")

let constant_value context frame path =
  match (source_at context.lookups path, Mir.initializer_of_path context.lookups.mir path) with
  | Some (constant_source, _, _), Some { form = code; _ } ->
      let symbol = Symbol.Constant path in
      let empty =
        {
          frame with
          source = constant_source;
          locals = Locals.empty;
          types = Locals.empty;
          makes_obligations = false;
          self = None;
          condition = Logic.Boolean true;
          bound = [];
          binders = [];
        }
      in
      once context (Value_of symbol) (fun () ->
          let ty = constant_type context path in
          declare context (Logic.Constant (symbol, sort_of context ty));
          let _, defined_value =
            without_costs context (fun () -> code_value context empty code ~type_:ty)
          in
          add_fact context (Logic.equal (Logic.Symbol symbol) defined_value));
      Logic.Symbol symbol
  | _ -> raise (Foreign_unsupported "a constant with errors")

let field_default context frame (site : Invocation.site) ty variant field =
  match (ty, type_source context ty) with
  | Types.Named { path; _ }, Some source -> (
      match Mir.defaults_of_path context.lookups.mir path with
      | Some { form = Field_defaults defaults; _ } -> (
          match
            List.find_opt
              (fun (default : Mir.t Mir.field_default) ->
                default.variant = variant && default.field = field)
              defaults
          with
          | Some default ->
              let inside = type_frame context frame source ty ~self:None in
              snd
                (code_value context inside default.value
                   ~type_:(substituted context inside default.type_))
          | None ->
              unsupported
                (locate context frame.source site.origin)
                "a field left out without a default")
      | Some { form = Parameter_defaults _; _ } | None -> bug "a type with no MIR of its defaults")
  | _ -> unsupported (locate context frame.source site.origin) "a default of a type with errors"

let check_built context frame (site : Invocation.site) ty term =
  check_valid context frame
    (locate context frame.source site.origin)
    ty term ~deep:false ~when_:"for the value built here"

let indirect context (ty : Types.ty) variant =
  match (ty, variant) with
  | Types.Named { path; _ }, Some variant -> (
      match Interface.Definition.read_interface context.lookups.interface path with
      | Some (Interface.Environment.Type_interface { shape = Sum variants; _ }) ->
          List.exists
            (fun (written : Types.variant) -> written.variant_name = variant && written.indirect)
            variants
      | _ -> false)
  | _ -> false

let construct_amount context frame (ty : Types.ty) variant (counter : Costs.counter) =
  match counter.resource with
  | (Allocations | Allocated_bytes) when not (indirect context ty variant) -> Costs.zero
  | Allocations -> Logic.int 1
  | Allocated_bytes when counter.counting = Units -> Logic.int 1
  | Allocated_bytes ->
      let symbol = Symbol.Block_bytes { type_ = ty; variant } in
      declare context (Logic.Constant (symbol, Logic.Int));
      fact context frame (Logic.Operation ("<=", [ Logic.int 1; Logic.Symbol symbol ]));
      Logic.Symbol symbol
  | Time | Calls _ -> Costs.zero

let apply_construct context frame (site : Invocation.site) variant
    (fields : (string * Logic.term option) list) =
  let ty = substituted context frame site.type_ in
  if Types.equal ty Types.unit then begin
    ignore (sort_of context Types.unit);
    (frame, Logic.Apply (Symbol.Unit, []))
  end
  else
    let frame, field_terms =
      List.fold_left
        (fun (frame, field_terms) (field, written) ->
          match written with
          | Some term -> (frame, field_terms @ [ (field, term) ])
          | None ->
              (frame, field_terms @ [ (field, field_default context frame site ty variant field) ]))
        (frame, []) fields
    in
    let frame = spend context frame (construct_amount context frame ty variant) in
    match constructors context ty with
    | Some shape ->
        ignore (sort_of context ty);
        let shaped = match List.assoc_opt variant shape with Some fields -> fields | None -> [] in
        let field_value (name, _) =
          match List.assoc_opt name field_terms with
          | Some term -> term
          | None -> unsupported (locate context frame.source site.origin) "a field left out"
        in
        let built = Logic.Apply (constructor_name ty variant, List.map field_value shaped) in
        check_built context frame site ty built;
        (frame, built)
    | None -> (frame, arrive context frame "built" ty)

let text_matches context location ty term text =
  let byte = Types.make_builtin UInt8 in
  match model_of context ty term ~element:byte with
  | Some model ->
      Logic.conjunction
        (Logic.equal (sequence_length context byte model) (Logic.int (String.length text))
        :: List.init (String.length text) (fun index ->
            match sequence_at context byte model (Logic.int index) with
            | Some at -> Logic.equal at (Logic.int (Char.code text.[index]))
            | None -> Logic.Boolean false))
  | None -> unsupported location "a string pattern on `%s`" (Types.show ty)

let log_facts number ~halving =
  let log number = Logic.Apply (Symbol.Cost_log, [ number ]) in
  let basic =
    Logic.(
      Operation ("<=", [ int 0; log number ])
      &&& (Operation ("<=", [ number; int 0 ]) ==> equal (log number) (int 0))
      &&& (Operation (">=", [ number; int 0 ]) ==> Operation ("<=", [ log number; number ])))
  in
  if halving then
    let half = Logic.Operation ("div", [ number; Logic.int 2 ]) in
    ( [
        basic;
        Logic.(
          Operation (">=", [ number; int 1 ])
          ==> equal (log number) (Operation ("+", [ log half; int 1 ])));
      ],
      Some half )
  else ([ basic ], None)

let log_order left right =
  let log number = Logic.Apply (Symbol.Cost_log, [ number ]) in
  Logic.(
    Operation ("<=", [ left; right ])
    ==> Operation ("<=", [ log left; log right ])
    &&& (Operation ("<=", [ right; left ]) ==> Operation ("<=", [ log right; log left ])))

let log_of context frame log_argument =
  declare context (Logic.Function (Symbol.Cost_log, [ Logic.Int ], Logic.Int));
  let rec add log_argument ~halving =
    match List.assoc_opt log_argument context.logs with
    | Some true -> ()
    | Some false when not halving -> ()
    | seen ->
        if seen = None then
          List.iter
            (fun (other, _) -> fact context frame (log_order log_argument other))
            context.logs;
        context.logs <- (log_argument, halving) :: List.remove_assoc log_argument context.logs;
        let facts, half = log_facts log_argument ~halving in
        List.iter (fact context frame) facts;
        Option.iter (fun half -> add half ~halving:false) half
  in
  if not (Logic.mentions frame.bound log_argument) then add log_argument ~halving:true;
  (match log_argument with
  | Logic.Integer limit ->
      fact context frame
        (Logic.equal
           (Logic.Apply (Symbol.Cost_log, [ log_argument ]))
           (Logic.int (if Z.sign limit <= 0 then 0 else Z.numbits limit)))
  | _ -> ());
  Logic.Apply (Symbol.Cost_log, [ log_argument ])

let apply_specification_function context frame ~location (measure : specification_function) values
    ~unconverted ~types =
  match (measure, values, unconverted, types) with
  | Log, [ log_argument ], [ unconverted ], _ ->
      let log = log_of context frame log_argument in
      (match bounds unconverted with
      | Some (_, high) when not (Logic.mentions frame.bound log_argument) ->
          fact context frame
            Logic.(
              Operation ("<=", [ log_argument; Integer high ])
              ==> Operation ("<=", [ log; int (Z.numbits high) ]))
      | _ -> ());
      (frame, log)
  | Power, [ base; exponent ], _, _ -> (frame, power_of context frame base exponent)
  | Time, [ function_term ], _, [ function_type ] ->
      (frame, time_of context frame function_type function_term)
  | _ -> unsupported location "this specification function"

let copied ?literal context frame ty term =
  if
    context.counters = []
    || Interface.Impls.is_plain context.lookups.interface ~bounds:(current_bounds context) ty
       && not (try has_potential context ty with Foreign_unsupported _ -> true)
  then frame
  else
    spend context frame (fun (counter : Costs.counter) ->
        match (literal, counter.resource, counter.counting) with
        | _, Time, Units ->
            let time =
              match literal with
              | Some _ -> Costs.zero
              | None ->
                  trait_method_time context frame
                    (Path.Method
                       { owner = Well_known.path Copyable; name = "copy"; receiver = Read })
                    ty
            in
            let copy_potential =
              try potential context frame ty term
              with Unsupported _ | Foreign_unsupported _ -> Costs.zero
            in
            Costs.minus (Costs.plus time (Logic.int 1)) copy_potential
        | Some text, (Allocations | Allocated_bytes), Units | Some text, Allocations, _ ->
            Logic.int (if text = "" then 0 else 1)
        | Some text, Allocated_bytes, (At_most | Exactly) -> Logic.int (String.length text)
        | Some _, Calls _, _ -> Costs.zero
        | _ -> unknown_amount context frame counter)
