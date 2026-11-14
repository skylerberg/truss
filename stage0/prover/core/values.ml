(* Values built and named: literals, constructors, constants, named
   functions, and templates. *)

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

(* A [proof] block's or a law's proof's body, run for the facts it states.
   Gives the condition of the paths that a [todo] ends. *)
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

(* Two sequences with the same length and the same elements are identical:
   the one fact about sequences their contracts cannot state, since a
   contract describes a result. It is stated for each two that are
   compared, which keeps the solver from comparing every two it knows. *)
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
      (* A set by its elements, and a map by its keys and their values. *)
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

(* That [contains] holds of nothing but [members]: a literal set's
   elements, or a literal map's keys. *)
let only_members context frame label sort contains members =
  let each = fresh_name context label in
  assume context frame
    (Logic.forall
       ( [ (each, sort) ],
         Logic.( ==> ) (contains (Logic.Symbol each))
           (Logic.disjunction (List.map (Logic.equal (Logic.Symbol each)) members)) ))

(* A [Set] or a [FiniteSet] of these elements: one that contains each of
   them and nothing else, so no more of them than were written. *)
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

(* A collection literal of [values]: a sequence's or a set's model. *)
let apply_list_literal context frame (site : Invocation.site) values =
  let ty = substituted context frame site.type_ in
  let span = span_of frame.source site.origin in
  let element =
    match ty with
    | Types.Named { arguments = Types.Type element :: _; _ } -> element
    | _ -> unsupported span "a literal of `%s`" (Types.show ty)
  in
  let literal =
    match sequence_of context frame ty ~element values with
    | Some literal -> literal
    | None -> (
        match set_of context frame ty ~element values with
        | Some literal -> literal
        | None -> unsupported span "a literal of `%s`" (Types.show ty))
  in
  (frame, literal)

(* Whether a clause reads its template parameter only as
   [template.literals], so that a template's parts cannot change it. *)
let reads_only_literals (parameter : Core.local) (clause : Mir.formula) =
  let is_parameter local =
    match clause.locals.(local).kind with
    | Source { local = core; _ } -> core = parameter
    | Temporary | Lent _ -> false
  in
  let fine = ref true in
  Mir.iter_places_read
    (fun (place : Mir.place) ->
      match place with
      | { root = Local local; projections = Field "literals" :: _ } when is_parameter local -> ()
      | { root = Local local; _ } when is_parameter local -> fine := false
      | _ -> ())
    clause.value;
  !fine

(* A tagged string: its tag's [from_template], through the [impl]'s
   contract, on the template [value_]. *)
let apply_template context frame (site : Invocation.site) ~trait ~name ~receiver ~evidence ~texts
    value_ =
  let span = span_of frame.source site.origin in
  let tag_type = substituted context frame site.type_ in
  match evidence with
  | Impl { impl; _ } -> (
      let path = Path.Method { owner = impl; name; receiver } in
      match
        method_contract ?reading_package:(reading_package context) context.database trait name
          receiver evidence
      with
      | Some contract ->
          let own = List.hd contract.parts in
          let entry = part_frame frame own ~arguments:[ (0, value_) ] ~substitution:[] in
          (* A clause that reads only the template's literal texts, of a tag
             whose [impl] is not generic, can be decided by running it. *)
          let evaluable (clause : Mir.formula) =
            match (evidence, own.parameters) with
            | Impl { arguments = []; _ }, [ parameter ] ->
                reads_only_literals parameter.local clause
            | _ -> false
          in
          List.iteri
            (fun index (requirement : Mir.formula) ->
              let evaluation =
                if evaluable requirement then Some { from_template = path; texts; clause = index }
                else None
              in
              oblige ?evaluation context frame Requires span
                (Printf.sprintf "This template may not meet `%s`, which its tag requires."
                   (quote own.callee requirement.origin))
                (snd (specification_value context entry requirement)))
            (clauses own.requires);
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
      | None -> unsupported span "a tagged template whose tag the prover cannot read")
  | Bound | Dynamic -> unsupported span "a tagged template whose tag the prover cannot read"

(* A map literal of entries: each key's origin, where it is written at one,
   its value, and the value it maps to. *)
let apply_map_literal context frame ~(ty : Types.ty) ~span terms =
  let key_type, value_type =
    match ty with
    | Types.Named { arguments = [ Types.Type key; Types.Type value_type ]; _ } -> (key, value_type)
    | _ -> unsupported span "a literal of `%s`" (Types.show ty)
  in
  List.iteri
    (fun index (_, key_term, _) ->
      List.iteri
        (fun other (other_key, other_term, _) ->
          if other > index then
            oblige context frame Disjoint
              (match other_key with Some origin -> span_of frame.source origin | None -> span)
              (Printf.sprintf "The key `%s` may equal an earlier key of this map."
                 (match other_key with
                 | Some origin -> quote frame.source origin
                 | None -> "this key"))
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
    | _ -> unsupported span "a literal of `%s`" (Types.show ty)
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

(* Text as a value whose model is its UTF-8 bytes. A literal is one value
   for its text and type, so two literals with the same text are the same
   value, as a key written twice is the same key. *)
let text_value context frame (ty : Types.ty) text =
  let symbol = Symbol.Literal { type_key = type_key ty; text } in
  let literal = Logic.Symbol symbol in
  once context (Value_of symbol) (fun () ->
      declare context (Logic.Constant (symbol, sort_of context ty));
      assume_valid context
        { frame with condition = Logic.Boolean true; bound = []; binders = [] }
        ty literal;
      let byte = Types.builtin UInt8 in
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

let cursor_trait : Path.t = Well_known.path Cursor
let option_path : Path.t = Well_known.path Option

(* A sequence of parts about which only its length is known. *)
let some_parts context frame element =
  let parts = fresh context frame "parts" (sort_of context (sequence_type element)) in
  assume context frame Logic.(Operation (">=", [ sequence_length context element parts; int 0 ]));
  parts

(* Data *)

(* A field of a value, which is in its type's range like every value. *)
let field_of context frame ty variant field field_type term =
  let part = selected context ty variant field term in
  assume_typed context frame (in_range field_type part);
  (* A part of a value is below it, whatever its type, which is how
     structural recursion is shown to end. *)
  if context.ranking then begin
    let below = rank context field_type part in
    assume context frame
      Logic.(
        Operation ("<=", [ int 0; below ]) &&& Operation ("<", [ below; rank context ty term ]))
  end;
  part

(* A pure function's contract about its value for every argument:
   where its [requires] holds, its [ensures] does. Its clauses are read over
   the parameters as a quantifier's body is. *)
let contract_for_every_argument context frame (contract : contract) parameters value =
  let inputs = List.map (fun (name, _) -> Logic.Symbol name) parameters in
  let over =
    {
      frame with
      bound = List.map fst parameters @ frame.bound;
      binders =
        List.rev_map (fun (name, sort) -> (name, sort, Logic.Boolean true)) parameters
        @ frame.binders;
      checking = false;
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

(* A function named as a value is a value of its type known by its
   promise about its calls: one unit of time per call when its [time] is a
   constant. Naming it is an edge of the call graph that passes no
   arguments, so in a function that must end, it must not reach back. *)
let named_function context frame (site : Invocation.site) path type_arguments contract ~is_argument
    =
  if
    context.terminates && frame.checking
    && Call_graph.reaches context.database ~package:(Path.package context.current) ~from:path
         ~target:context.current
  then
    oblige context frame Termination
      (span_of frame.source site.origin)
      (Printf.sprintf
         "Naming `%s` as a value reaches back here, and such a use passes no arguments the prover \
          can compare, so the recursion cannot be shown to end: write it as a direct call on a \
          part."
         (Path.show path))
      (Logic.Boolean false);
  let ty = substituted context frame site.type_ in
  (* A function with a [requires], used as a value anywhere but passed
     straight to a parameter, which checks it, has a type that keeps no
     [requires], so it must accept every argument of that type. *)
  (match (ty, contract.parts) with
  | Types.Function function_type, own :: _
    when own.requires <> [] && frame.checking && not is_argument ->
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
              (span_of frame.source site.origin)
              (Printf.sprintf
                 "`%s` is used as a value of `%s`, which promises nothing of its arguments, so its \
                  `%s` may not hold."
                 (Path.show path) (Types.show ty)
                 (quote own.callee requirement.origin))
              (snd (specification_value context inside requirement)))
          (clauses own.requires)
      end
  | _ -> ());
  let instance =
    List.map argument_key (List.map (Types.substitute_argument frame.substitution) type_arguments)
  in
  let symbol = Symbol.Function_value { callee = path; instance } in
  declare context (Logic.Constant (symbol, sort_of context ty));
  let term = Logic.Symbol symbol in
  (* Applied, a pure function named as a value is the function: its body,
     where it has a definition that holds for every argument, and
     otherwise the function in the logic. *)
  (match ty with
  | Types.Function function_type when in_the_logic function_type && contract.pure ->
      let parameters = parameters_of context frame function_type in
      let inputs = List.map (fun (name, _) -> Logic.Symbol name) parameters in
      let defined =
        match contract.definition with
        | Some (part, body)
          when part.requires = [] && instance = []
               && not (List.exists (Path.equal path) context.instantiating) ->
            context.instantiating <- path :: context.instantiating;
            Fun.protect
              ~finally:(fun () -> context.instantiating <- List.tl context.instantiating)
              (fun () ->
                body_over context frame parameters body (fun inside ->
                    part_frame inside part
                      ~arguments:(List.mapi (fun index input -> (index, input)) inputs)
                      ~substitution:[]))
        | _ -> None
      in
      let value =
        match defined with
        | Some defined -> defined
        | None ->
            let output =
              match function_type.output with Returns output -> output | _ -> Types.unit
            in
            let function_symbol = Symbol.Function { callee = path; instance } in
            declare context
              (Logic.Function (function_symbol, List.map snd parameters, sort_of context output));
            let value = Logic.Apply (function_symbol, inputs) in
            if instance = [] then
              contract_for_every_argument context frame contract parameters value;
            value
      in
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

(* A function used as a value. *)
let global_value context frame (site : Invocation.site) path type_arguments ~is_argument =
  match function_contract ?reading_package:(reading_package context) context.database path with
  | Some contract -> named_function context frame site path type_arguments contract ~is_argument
  | None ->
      unsupported
        (span_of frame.source site.origin)
        "a function the prover cannot read, used as a value"

(* A constant is its value, computed from its definition, which is made
   of literals, arithmetic, other constants, and values built from them. *)
(* The type a constant declares. *)
let constant_type context path =
  match Query.demand context.database Interface.Environment.constant_type path with
  | Some ty -> ty
  | None -> raise (Foreign_unsupported "a constant with errors")

let constant_value context frame path =
  match (source_at context.database path, Query.demand context.database Mir.of_constant path) with
  | Some (constant_source, _, _), Some code ->
      (* A constant is one value, a symbol whose value is stated once, as
         a fact of mathematics, wherever it is used. *)
      let symbol = Symbol.Constant path in
      let empty =
        {
          frame with
          source = constant_source;
          locals = Locals.empty;
          types = Locals.empty;
          checking = false;
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
      match Query.demand context.database Mir.defaults_of_path path with
      | Some (Field_defaults defaults) -> (
          match
            List.find_opt
              (fun (default : Mir.field_default) ->
                default.variant = variant && default.field = field)
              defaults
          with
          | Some default ->
              let inside = type_frame context frame source ty ~self:None in
              snd
                (code_value context inside default.value
                   ~type_:(substituted context inside default.type_))
          | None ->
              unsupported (span_of frame.source site.origin) "a field left out without a default")
      | Some (Parameter_defaults _) | None -> bug "a type with no MIR of its defaults")
  | _ -> unsupported (span_of frame.source site.origin) "a default of a type with errors"

let check_built context frame (site : Invocation.site) ty term =
  check_valid context frame
    (span_of frame.source site.origin)
    ty term ~deep:false ~when_:"for the value built here"

let indirect context (ty : Types.ty) variant =
  match (ty, variant) with
  | Types.Named { path; _ }, Some variant -> (
      match Query.demand context.database Interface.Environment.interface path with
      | Some (Interface.Environment.Type_interface { shape = Sum variants; _ }) ->
          List.exists
            (fun (written : Types.variant) -> written.variant_name = variant && written.indirect)
            variants
      | _ -> false)
  | _ -> false

(* The cost of building a record or a variant: one allocation, of its
   block, for a variant that is held by reference. *)
let construct_amount context frame (ty : Types.ty) variant (counter : Costs.counter) =
  match counter.resource with
  | (Allocations | Allocated_bytes) when not (indirect context ty variant) -> Costs.zero
  | Allocations -> Logic.int 1
  | Allocated_bytes when counter.counting = Units -> Logic.int 1
  | Allocated_bytes ->
      (* The size of the variant's block, which is fixed and not known
         here. *)
      let symbol = Symbol.Block_bytes { type_key = type_key ty; variant } in
      declare context (Logic.Constant (symbol, Logic.Int));
      fact context frame (Logic.Operation ("<=", [ Logic.int 1; Logic.Symbol symbol ]));
      Logic.Symbol symbol
  | Time | Calls _ -> Costs.zero

(* A record or a variant built from its fields' values, a field given none
   taking its type's default. *)
let apply_construct context frame (site : Invocation.site) variant
    (fields : (string * Logic.term option) list) =
  let ty = substituted context frame site.type_ in
  if Types.equal ty Types.unit then begin
    (* The one value of [Unit]. *)
    ignore (sort_of context Types.unit);
    (frame, Logic.Apply (Symbol.Unit, []))
  end
  else
    let frame, field_terms =
      List.fold_left
        (fun (frame, field_terms) (field, given) ->
          match given with
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
          | None -> unsupported (span_of frame.source site.origin) "a field left out"
        in
        let built = Logic.Apply (constructor_name ty variant, List.map field_value shaped) in
        check_built context frame site ty built;
        (frame, built)
    | None ->
        (* A type whose fields are not visible here is known by its range. *)
        (frame, arrive context frame "built" ty)

(* Whether a value matches a pattern, and the names it binds: the
   condition, and the frame with the names bound. A name bound is the part
   of the value it names, which means something only where the condition
   holds, and is used only there. *)
(* Whether text has a string literal's bytes. *)
let text_matches context span ty term text =
  let byte = Types.builtin UInt8 in
  match model_of context ty term ~element:byte with
  | Some model ->
      Logic.conjunction
        (Logic.equal (sequence_length context byte model) (Logic.int (String.length text))
        :: List.init (String.length text) (fun index ->
            match sequence_at context byte model (Logic.int index) with
            | Some at -> Logic.equal at (Logic.int (Char.code text.[index]))
            | None -> Logic.Boolean false))
  | None -> unsupported span "a string pattern on `%s`" (Types.show ty)

let log_of context frame log_argument =
  declare context (Logic.Function (Symbol.Cost_log, [ Logic.Int ], Logic.Int));
  let rec add log_argument ~halving =
    match List.assoc_opt log_argument context.logs with
    | Some true -> ()
    | Some false when not halving -> ()
    | seen ->
        if seen = None then
          List.iter
            (fun (other, _) -> fact context frame (Costs.log_order log_argument other))
            context.logs;
        context.logs <- (log_argument, halving) :: List.remove_assoc log_argument context.logs;
        let facts, half = Costs.log_facts log_argument ~halving in
        List.iter (fact context frame) facts;
        Option.iter (fun half -> add half ~halving:false) half
  in
  if not (Logic.mentions frame.bound log_argument) then add log_argument ~halving:true;
  (* Of a number, it is the number's bit length: the smallest integer at
     least log2(n + 1). *)
  (match log_argument with
  | Logic.Integer limit ->
      fact context frame
        (Logic.equal
           (Logic.Apply (Symbol.Cost_log, [ log_argument ]))
           (Logic.int (if Z.sign limit <= 0 then 0 else Z.numbits limit)))
  | _ -> ());
  Logic.Apply (Symbol.Cost_log, [ log_argument ])

(* A specification function applied to values: of [types], and, before any
   conversion to [Integer], of the types [unconverted]. *)
let apply_specification_function context frame ~span (measure : specification_function) values
    ~unconverted ~types =
  match (measure, values, unconverted, types) with
  | Log, [ log_argument ], [ unconverted ], _ ->
      let log = log_of context frame log_argument in
      (* [log] of a value of a bounded type is at most [log] of the type's
         largest value: its width, for an unsigned type. *)
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
  | _ -> unsupported span "this specification function"

(* A built-in copy: of a [Plain] value that holds no potential, a copy of
   its bits; of any other, a call of [Copyable.copy], which takes
   [time(Types.copy)] and pays for the potential the copy holds, as a trait's
   method that promises only that it ends does. *)
let copied context frame ty term =
  if
    context.counters = []
    || Interface.Impls.plain context.database ~bounds:(current_bounds context) ty
       && not (try has_potential context ty with Foreign_unsupported _ -> true)
  then frame
  else
    spend context frame (fun (counter : Costs.counter) ->
        match (counter.resource, counter.counting) with
        | Time, Units ->
            let time =
              trait_method_time context frame
                (Path.Method
                   { owner = Interface.Impls.copyable_path; name = "copy"; receiver = Read })
                ty
            in
            let copy_potential =
              try potential context frame ty term
              with Unsupported _ | Foreign_unsupported _ -> Costs.zero
            in
            Costs.minus (Costs.plus time (Logic.int 1)) copy_potential
        | _ -> unknown_amount context frame counter)
