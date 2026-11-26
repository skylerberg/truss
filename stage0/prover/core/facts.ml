type unsupported = {
  location : Obligation.location;
  construct : Catalog.Prover.construct;
  foreign_definition : Path.t option;
}

exception Unsupported of unsupported

let is_home_source (environment : State.environment) (source : State.source) =
  source.key = environment.home && Path.equal source.definition environment.home.path

let is_home (frame : State.frame) = is_home_source frame.environment frame.source

let is_in_home_package (frame : State.frame) =
  Path.compare_package
    (Path.locate_package frame.source.definition)
    (Path.locate_package frame.environment.home.path)
  = 0

let raise_unsupported location construct =
  raise (Unsupported { location; construct; foreign_definition = None })

let run_in_source (frame : State.frame) read =
  try read ()
  with Unsupported ({ foreign_definition = None; _ } as unsupported) when not (is_home frame) ->
    raise (Unsupported { unsupported with foreign_definition = Some frame.source.definition })

let raise_bug format = Compiler_bug.raise_bug ~stage:"Prover" format

let list_method_type_arguments (trait : Types.trait_reference) ~self_type arguments =
  trait.trait_arguments @ (Types.Type self_type :: arguments)

let read_parameter_name (parameter : Mir.parameter) =
  match Mir.find_local_name parameter.local with
  | Some name -> name
  | None -> raise_bug "a parameter that no definition names"

let list_clauses (requires : Mir.requirement list) =
  List.map (fun (requirement : Mir.requirement) -> requirement.clause) requires

let declare_value_symbol (frame : State.frame) name sort =
  match List.rev frame.binders with
  | [] ->
      Query.declare frame.query (Logic.Constant (name, sort));
      Logic.Symbol name
  | outermost_first ->
      Query.declare frame.query
        (Logic.Function (name, List.map (fun (_, sort, _) -> sort) outermost_first, sort));
      Logic.Apply (name, List.map (fun (bound, _, _) -> Logic.Symbol bound) outermost_first)

let declare_fresh (frame : State.frame) label sort =
  declare_value_symbol frame (Query.make_ordered_fresh_name frame.query label) sort

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

let add_axiom (frame : State.frame) term =
  if not (Logic.mentions frame.bound term) then Query.add_fact frame.query term
  else Query.add_scoped_fact frame.query ~bound:frame.bound term

let assume (frame : State.frame) term =
  match term with
  | Logic.Boolean true -> ()
  | _ ->
      let guarded = Logic.( ==> ) frame.condition term in
      if not (Logic.mentions frame.bound term || Logic.mentions frame.bound frame.condition) then
        Query.add_fact frame.query guarded
      else Query.add_scoped_fact frame.query ~bound:frame.bound guarded

let locate_source environment source origin =
  if is_home_source environment source then Obligation.Node origin else Whole_definition

let locate (frame : State.frame) origin = locate_source frame.environment frame.source origin

let add_hole (context : State.context) hole =
  if not (List.mem hole context.holes) then context.holes <- hole :: context.holes

let remove_panic (uses : Types.capability_set) =
  Types.replace_capabilities
    (function
      | Types.Capability_unless_values _ | Types.Built_in Panic -> Some Types.no_capabilities
      | _ -> None)
    uses

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

let bind (frame : State.frame) local ty term =
  {
    frame with
    State.locals = Locals.add local term frame.locals;
    types = Locals.add local ty frame.types;
  }

let restrict (frame : State.frame) condition =
  { frame with State.condition = Logic.( &&& ) frame.condition condition }

let restrict_unless_proven (frame : State.frame) precondition =
  if frame.makes_obligations then frame else restrict frame precondition

let suppose (frame : State.frame) label =
  let hypothesis = declare_fresh frame label Logic.Bool in
  (hypothesis, restrict frame hypothesis)
