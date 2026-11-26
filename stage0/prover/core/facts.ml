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

let list_method_type_arguments (trait : Types.trait_reference) ~self_type arguments =
  trait.trait_arguments @ (Types.Type self_type :: arguments)

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

let mentions_fresh_since (context : State.context) mark term =
  Query.mentions_fresh_since context.query mark term

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

let remove_panic_condition (uses : Types.capability_set) =
  Types.replace_capabilities
    (function Types.Capability_unless_values _ -> Some Types.no_capabilities | _ -> None)
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
