(* Lambdas: a lambda's body, proven where it is written, and a functional
   lambda as a function of the logic. *)

open Core
open State
open Facts
open Contracts
open Validity

(* A function value applied to its arguments, through the [apply] of its
   type's sorts. *)
let applied context (function_type : Types.function_type) callee arguments =
  let inputs = List.map (fun (_, input) -> sort_of context input) function_type.inputs in
  let output =
    sort_of context (match function_type.output with Returns output -> output | _ -> Types.unit)
  in
  let value_sort = sort_of context (Types.Function function_type) in
  let symbol = Symbol.Apply ((value_sort :: inputs) @ [ output ]) in
  declare context (Logic.Function (symbol, value_sort :: inputs, output));
  Logic.Apply (symbol, callee :: arguments)

let add_lambda_facts context frame ~capture_free function_type term ~called ~arguments ~start_fresh
    ~end_fresh ~start_declarations ~premises ~shown ~ended =
  let declared_here =
    List.filteri
      (fun index _ -> index < List.length context.declarations - start_declarations)
      context.declarations
  in
  let captures_fresh = function
    | Symbol.Lambda _ as name when not (Hashtbl.mem context.fresh_order name) -> (
        match Hashtbl.find_opt context.lambda_definitions name with
        | Some defined -> mentions_fresh_after context start_fresh defined
        | None -> false)
    | _ -> false
  in
  begin
    let parameters =
      List.mapi
        (fun index (_, input) ->
          (variable "lambda.argument" ~numbers:[ index ], sort_of context input))
        function_type.Types.inputs
    in
    let variables = List.map (fun (name, _) -> Logic.Symbol name) parameters in
    let renamed = Hashtbl.create 16 in
    (match called with
    | Logic.Symbol name -> Hashtbl.replace renamed name (Logic.Boolean true)
    | _ -> ());
    List.iter2
      (fun argument variable ->
        match argument with Logic.Symbol name -> Hashtbl.replace renamed name variable | _ -> ())
      arguments variables;
    let functions = Hashtbl.create 8 in
    List.iter
      (function
        | Logic.Constant (name, sort) when not (Hashtbl.mem renamed name) ->
            let is_fresh_in_body =
              match Hashtbl.find_opt context.fresh_order name with
              | Some order -> order > start_fresh && order <= end_fresh
              | None -> captures_fresh name
            in
            if is_fresh_in_body then begin
              let over = Symbol.Over name in
              declare context (Logic.Function (over, List.map snd parameters, sort));
              Hashtbl.replace renamed name (Logic.Apply (over, variables))
            end
        | Logic.Function (name, inputs, sort) when frame.binders <> [] -> (
            match Hashtbl.find_opt context.fresh_order name with
            | Some order when order > start_fresh && order <= end_fresh ->
                let over = Symbol.Over name in
                declare context (Logic.Function (over, inputs @ List.map snd parameters, sort));
                Hashtbl.replace functions name over
            | _ -> ())
        | _ -> ())
      declared_here;
    let rec over = function
      | Logic.Symbol name as symbol -> Option.value (Hashtbl.find_opt renamed name) ~default:symbol
      | (Logic.Integer _ | Logic.Boolean _ | Logic.Bits _) as term -> term
      | Logic.Apply (name, _)
        when match called with Logic.Apply (called_name, _) -> called_name = name | _ -> false ->
          Logic.Boolean true
      | Logic.Apply (name, arguments) when Hashtbl.mem functions name ->
          Logic.Apply (Hashtbl.find functions name, List.map over arguments @ variables)
      | (Logic.Apply _ | Logic.Operation _ | Logic.Is _) as term -> Logic.map_arguments over term
      | Logic.Forall (bound, trigger, body) -> Logic.Forall (bound, List.map over trigger, over body)
      | Logic.Exists (bound, body) -> Logic.Exists (bound, over body)
    in
    let premise = over (Logic.conjunction premises) in
    let applied_here = applied context function_type term variables in
    let statements =
      List.map over shown
      @ List.filter_map
          (fun ((exit_ : frame), value) ->
            Option.map
              (fun value ->
                Logic.( ==> ) (over exit_.condition) (Logic.equal applied_here (over value)))
              value)
          ended
    in
    (* A lambda that captures a quantifier's bound values states its behavior
       for each of them, closed over the quantifier. *)
    List.iter
      (fun statement ->
        let stated = Logic.forall (parameters, Logic.( ==> ) premise statement) in
        if frame.bound = [] || capture_free then add_fact context stated
        else
          match closed_over_binders frame stated with
          | Some closed -> add_fact context closed
          | None -> ())
      statements
  end

(* Whether a call through a value of a function type is a function in the
   logic: it ends, uses no capabilities, mutates none of its arguments, and
   returns its result. *)
let in_the_logic (function_type : Types.function_type) =
  Types.terminates function_type
  && function_type.uses = Types.no_capabilities
  && List.for_all (fun (mode, _) -> mode <> Types.Mut) function_type.inputs
  && match function_type.output with Returns _ -> true | _ -> false

(* Bound names for each input of a function type, at this depth of
   quantifiers. *)
let parameters_of context frame (function_type : Types.function_type) =
  let depth = List.length frame.bound in
  List.mapi
    (fun index (_, input) ->
      ( Symbol.Variable { label = "parameter"; numbers = [ depth; index ] },
        sort_of context (substituted context frame input) ))
    function_type.inputs

(* A lambda whose body is functional, as a function in the logic: applied,
   it is its body. Lambdas with the same body over the same captured values
   are the same function, so a bound and a loop's bound that both write
   [(row) => row.length()] mean the same sum. A body whose value needs a
   fresh symbol, or that the prover cannot read, gives no definition. *)
let lambda_definition context frame (function_type : Types.function_type) (written : lambda_code) =
  match written.definition with
  | Some definition when in_the_logic function_type -> (
      let bound = parameters_of context frame function_type in
      (* The body's value over the bound names, which it binds its parameters'
       patterns to. Nothing is counted or obliged, and a body that the
       prover cannot read, or whose value needs a fresh symbol, gives none. *)
      let defined =
        let mark = context.fresh in
        let saved_counters = context.counters in
        context.counters <- [];
        Fun.protect
          ~finally:(fun () -> context.counters <- saved_counters)
          (fun () ->
            try
              let _, defined =
                context.formula_term
                  {
                    frame with
                    bound = List.map fst bound @ frame.bound;
                    checking = false;
                    result = None;
                  }
                  definition
                  ~arguments:(List.map (fun (name, _) -> Logic.Symbol name) bound)
              in
              if mentions_fresh_after context mark defined then None else Some defined
            with Unsupported _ | Foreign_unsupported _ -> None)
      in
      let quantified = List.map (fun (name, _, _) -> name) frame.binders in
      let enclosing_parameters =
        List.filter (fun name -> not (List.mem name quantified)) frame.bound
      in
      match defined with
      | Some defined when Logic.mentions enclosing_parameters defined -> None
      | Some defined ->
          let defined = canonical_binders defined in
          (* The same body is the same function wherever it is written, so its
           parameters are named by position alone in its symbol. *)
          let named_by_position =
            List.fold_left
              (fun term (index, (name, _)) ->
                Logic.replace ~from:(Logic.Symbol name)
                  ~into:(Logic.Symbol (variable "parameter" ~numbers:[ index ]))
                  term)
              defined
              (List.mapi (fun index parameter -> (index, parameter)) bound)
          in
          let symbol =
            Symbol.Lambda { sorts = List.map snd bound; definition = named_by_position }
          in
          let sort = sort_of context (Types.Function function_type) in
          (* A lambda that captures a quantifier's bound symbol is a function
           of it. *)
          let term =
            if Logic.mentions frame.bound defined then value_symbol context frame symbol sort
            else value_symbol context { frame with binders = [] } symbol sort
          in
          let application =
            applied context function_type term (List.map (fun (name, _) -> Logic.Symbol name) bound)
          in
          Hashtbl.replace context.lambda_definitions symbol defined;
          fact context frame (Logic.forall (bound, Logic.equal application defined));
          (* Its body's value is in the range of the body's type, which may be
           narrower than the function type's [Integer]. *)
          (match written.value_type with
          | Some value_type -> (
              match in_range (substituted context frame value_type) application with
              | Logic.Boolean true -> ()
              | range ->
                  (* For arguments of the parameters' types, which the body
                   was read with. *)
                  let arguments_in_range =
                    Logic.conjunction
                      (List.map2
                         (fun (name, _) (_, input) ->
                           in_range (substituted context frame input) (Logic.Symbol name))
                         bound function_type.inputs)
                  in
                  fact context frame (Logic.forall (bound, Logic.( ==> ) arguments_in_range range)))
          | None -> ());
          Some term
      | _ -> None)
  | _ -> None

let check_valid context frame span ty term ~deep ~when_ =
  match validity context frame ~assuming:false ~deep ty term with
  | Logic.Boolean true -> ()
  | valid ->
      oblige context frame Invariant span
        (Printf.sprintf "The invariant of `%s` may not hold %s." (Types.show ty) when_)
        valid

let counting_of (cost : Mir.cost) : Costs.counting =
  match cost.bound with Order_of _ | Finite -> Units | At_most _ -> At_most | Exactly _ -> Exactly

(* Costs: each step's cost. *)

(* The counters a body's loops' [cost] clauses count, outside lambdas,
   which count on their own. *)
let mir_loop_counters locals (body : Mir.body) =
  let counters = ref [] in
  let note (loop : Mir.loop) =
    List.iter
      (function
        | Mir.Cost cost -> (
            match resource_of cost ~locals with
            | Some resource ->
                counters :=
                  { Costs.resource; counting = counting_of cost; amortized = false } :: !counters
            | None -> raise (Foreign_unsupported "this `calls` target"))
        | Invariant _ | Decreases _ -> ())
      loop.clauses
  in
  Array.iter
    (fun (block : Mir.basic_block) ->
      (match block.terminator with For { loop; _ } -> note loop | _ -> ());
      Option.iter (fun (natural : Mir.natural_loop) -> note natural.loop) block.header)
    body.blocks;
  List.rev !counters

(* The facts since a mark in the list, which is kept reversed. *)
let facts_since context count =
  let rec take count list =
    if count <= 0 then []
    else match list with [] -> [] | item :: rest -> item :: take (count - 1) rest
  in
  take (List.length context.facts - count) context.facts

let read_lambda ?(capture_free = false) context frame ~(site : Invocation.site)
    (written : lambda_code) ~facts =
  let span = span_of frame.source site.origin in
  let ty = substituted context frame site.type_ in
  let function_type =
    match ty with Types.Function function_type -> function_type | _ -> unsupported span "a lambda"
  in
  if List.length written.code.parameters <> List.length function_type.inputs then
    unsupported span "a lambda with a different number of parameters";
  (* A lambda's body may run any number of times, including none, so it is
     proven under a fresh path condition: its assumptions about its
     arguments and callees hold on no other path. *)
  let called = fresh context frame "called" Logic.Bool in
  let inside = { (restrict frame called) with result = None } in
  let start_fresh = context.fresh
  and start_facts = List.length context.facts
  and start_declarations = List.length context.declarations in
  let arguments =
    List.map
      (fun (_, input) ->
        let input = substituted context frame input in
        let argument = arrive context inside "argument" input in
        assume_valid context inside input argument;
        argument)
      function_type.inputs
  in
  List.iter (assume context inside) (facts arguments);
  (* A lambda's costs are counted apart from the enclosing function: the
     cost clauses of its type, and, where the enclosing function counts
     time, its time, to bound [time(f)] for it. *)
  let promised =
    List.filter_map
      (fun (cost : Types.cost) ->
        let counting : Costs.counting option =
          match cost.bound with
          | Order_of -> Some Units
          | No_more_than (Some _) -> Some At_most
          | Exactly_cost (Some _) -> Some Exactly
          | Finite_cost | No_more_than None | Exactly_cost None -> None
        in
        let resource : Costs.resource option =
          match cost.resource with
          | Time -> Some Time
          | Allocations -> Some Allocations
          | Allocated_bytes -> Some Allocated_bytes
          | Calls _ -> None
        in
        match (resource, counting) with
        | Some resource, Some counting ->
            let counter = { Costs.resource; counting; amortized = cost.amortized } in
            Some (counter, cost.bound)
        | _ -> None)
      function_type.costs
  in
  let time_units = { Costs.resource = Time; counting = Units; amortized = false } in
  let counts_time =
    List.exists
      (fun (counter : Costs.counter) -> counter.resource = Time && counter.counting = Units)
      context.counters
  in
  let times_by_type = List.exists (fun (counter, _) -> counter = time_units) promised in
  (* A call back into the definition around it still assumes its bound. *)
  let saved_counters = context.counters in
  context.counters <-
    distinct_counters
      ((if counts_time then [ time_units ] else [])
      @ List.map fst promised
      @ mir_loop_counters inside.locals written.code);
  let inside =
    { inside with spent = List.map (fun counter -> (counter, Costs.zero)) context.counters }
  in
  let mark = context.fresh and facts_mark = List.length context.facts in
  let premises =
    List.filteri
      (fun index _ -> index >= List.length context.facts - facts_mark)
      (facts_since context start_facts)
  in
  let ended = ref [] in
  let saved_returns = context.returns and saved_terminates = context.terminates in
  context.returns <- [];
  context.terminates <- Types.terminates function_type;
  let pending =
    Fun.protect
      ~finally:(fun () ->
        context.returns <- saved_returns;
        context.terminates <- saved_terminates;
        context.counters <- saved_counters)
      (fun () ->
        (* The body binds its parameters' patterns to the arguments it is
           given. The temporaries of the code around are not the lambda's:
           its own are numbered from zero too. *)
        let finished =
          let inside =
            {
              inside with
              locals =
                Locals.filter
                  (fun key _ -> match key with Core.Synthetic number -> number >= 0 | _ -> true)
                  inside.locals;
            }
          in
          let inside =
            List.fold_left2
              (fun inside parameter argument ->
                let info = written.code.locals.(parameter) in
                bind inside
                  (match info.kind with
                  | Source { local; _ } -> local
                  | Temporary | Lent _ -> Core.Synthetic (-1 - parameter))
                  (substituted context inside info.type_)
                  argument)
              inside written.code.parameters arguments
          in
          context.run_body inside ~lambdas:written.lambdas written.code;
          None
        in
        let exits =
          (match finished with Some (frame, _) -> [ frame ] | None -> [])
          @ List.map fst context.returns
        in
        ended :=
          (match finished with Some (frame, value) -> [ (frame, Some value) ] | None -> [])
          @ context.returns;
        (* Like a function, it meets its type's invariants where it ends:
           a call through it assumes so. *)
        List.iter
          (fun ((exit_ : frame), returned) ->
            (match (returned, function_type.output) with
            | Some term, Returns output ->
                check_valid context exit_ span
                  (substituted context frame output)
                  term ~deep:true ~when_:"for the value this lambda returns"
            | _ -> ());
            List.iter2
              (fun parameter (mode, input) ->
                match (mode, written.code.locals.(parameter).kind) with
                | Types.Mut, Source { local; _ } -> (
                    match Locals.find_opt local exit_.locals with
                    | Some term ->
                        check_valid context exit_ span (substituted context frame input) term
                          ~deep:true ~when_:"for a `mut` parameter when this lambda ends"
                    | None -> ())
                | _ -> ())
              written.code.parameters function_type.inputs)
          !ended;
        let spent_of (exit_ : frame) counter =
          match List.assoc_opt counter exit_.spent with Some term -> term | None -> Costs.zero
        in
        List.iter
          (fun (exit_ : frame) ->
            List.iter
              (fun (counter, (bound : Types.cost_bound)) ->
                let spent = spent_of exit_ counter in
                let goal =
                  match bound with
                  | Order_of -> Costs.at_most spent (Costs.bound (Logic.int 1))
                  | No_more_than (Some limit) -> Costs.at_most spent (Logic.Integer limit)
                  | Exactly_cost (Some limit) -> Logic.equal spent (Logic.Integer limit)
                  | _ -> Logic.Boolean true
                in
                oblige context exit_ Cost span
                  (Printf.sprintf "This lambda may spend more than its type, `%s`, allows."
                     (Types.show ty))
                  goal)
              promised)
          exits;
        (* A bound on the time of one call in terms of the values the lambda
           does not change, proven only once a cost uses it. *)
        if counts_time && not times_by_type then
          let spent = List.map (fun exit_ -> spent_of exit_ time_units) exits in
          let most =
            match spent with
            | [] -> Costs.zero
            | first :: rest -> List.fold_left Costs.larger first rest
          in
          match
            Costs.bound_on
              ~varies:(mentions_fresh_after context mark)
              ~facts:
                (facts_since context facts_mark
                @ List.map (fun (exit_ : frame) -> exit_.condition) exits)
              most
          with
          | Some bound ->
              Some
                ( bound,
                  List.filter_map
                    (fun ((exit_ : frame), spent) ->
                      obligation_at context exit_ Cost span
                        "The prover cannot show that a call of this lambda takes no more time than \
                         the bound it found for every call, which a cost here relies on."
                        (Costs.at_most spent bound))
                    (List.combine exits spent) )
          | None -> None
        else None)
  in
  let end_fresh = context.fresh in
  let term =
    match lambda_definition context frame function_type written with
    | Some term -> term
    | None ->
        let term = arrive context frame "lambda" ty in
        if in_the_logic function_type then
          add_lambda_facts context frame ~capture_free function_type term ~called ~arguments
            ~start_fresh ~end_fresh ~start_declarations ~premises
            ~shown:(facts_since context facts_mark) ~ended:!ended;
        term
  in
  context.lambda_captures <-
    (term, List.map (fun (capture : Mir.capture) -> capture.local) written.captures)
    :: context.lambda_captures;
  (match pending with
  | Some pending_time -> context.lambda_times <- (term, pending_time) :: context.lambda_times
  | None -> ());
  (frame, term)

(* Lambdas and callbacks *)

(* A lambda is proven where it is written, with fresh arguments that
   satisfy its function type's [requires]; it is proven to terminate
   exactly when its function type has a [time] clause; and it is a value
   about which nothing more is known. *)
let lambda context frame ~(site : Invocation.site) (written : lambda_code) ~facts =
  (* Inside a quantifier, a lambda that captures none of its bound values is
     one function for every one of them, so it is read outside it. *)
  let captured (capture : Mir.capture) =
    match capture.local with Self -> frame.self | local -> Locals.find_opt local frame.locals
  in
  if
    frame.bound <> []
    && List.for_all
         (fun capture ->
           match captured capture with
           | Some term -> not (Logic.mentions frame.bound term)
           | None -> false)
         written.captures
  then
    let _, term =
      read_lambda ~capture_free:true context
        { frame with binders = []; condition = Logic.Boolean true }
        ~site written ~facts
    in
    (frame, term)
  else read_lambda context frame ~site written ~facts

(* Calls *)

(* The arguments as the callee is given them, from either front end: each
   lambda written as an argument is read with the facts its parameter's
   type gives its arguments, which may name the other arguments. *)
let passed_values context frame (invocation : Invocation.t) (given : given list) =
  let known =
    List.filter_map
      (function
        | Given_value (passed : passed) -> Some (passed.position, passed.term)
        | Given_lambda _ -> None)
      given
  in
  List.map
    (function
      | Given_value passed -> passed
      | Given_lambda { position; mode; site; lambda = written } ->
          let _, term =
            lambda context frame ~site written
              ~facts:(callback_facts context frame invocation position known)
          in
          {
            position;
            mode;
            shape = Other;
            origin = Some site.origin;
            passed_place = None;
            type_ = substituted context frame site.type_;
            term;
          })
    given
