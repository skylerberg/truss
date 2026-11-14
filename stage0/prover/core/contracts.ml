(* The contract of a callee: the clauses that its form and its trait's state
   about it, read from the MIR. *)

open Core
open State

let source_of database (key : Names.key) =
  {
    key = Some key;
    name = Names.show_key key;
    spans = lazy (Option.value (Query.demand database Names.spans key) ~default:[||]);
    text = lazy (Option.value (Query.demand database Names.text key) ~default:"");
  }

(* The source of a definition, by its key, where the definition has no
   error. *)
let source_at_key database key =
  if Mir.is_lowered database key then Some (source_of database key) else None

(* The source of a function or a method by its path, with the substitution
   its clauses are read under: the [impl]'s, for the trait's method that the
   [impl] leaves to it. A method that an [impl] derives has no text. *)
let source_at database (path : Path.t) =
  Option.map
    (fun ((origin : Infer.form_origin), substitution) ->
      let source =
        match origin with
        | Written key | Inherited key -> source_of database key
        | Generated -> { key = None; name = Path.show path; spans = lazy [||]; text = lazy "" }
      in
      (source, substitution, origin))
    (Query.demand database Infer.form_origin path)

(* The substitution a trait's clauses and laws are read with for a type: [Self] the
   type, and each of the trait's parameters its argument. *)
let trait_substitution database (trait : Types.trait_reference) (ty : Types.ty) =
  let generics =
    match Query.demand database Interface.Environment.interface trait.trait with
    | Some (Interface.Environment.Trait_interface interface) ->
        List.map (fun (generic : Types.generic) -> generic.generic) interface.trait_generics
    | _ -> []
  in
  let rec pair generics arguments =
    match (generics, arguments) with
    | generic :: generics, argument :: arguments -> (generic, argument) :: pair generics arguments
    | _ -> []
  in
  ({ Types.owner = trait.trait; name = "Self" }, Types.Type ty)
  :: pair generics trait.trait_arguments

(* The clauses that the function or method at a path states. *)
let part_of ?(inherited = false) database path callee =
  Option.map
    (fun (contract : Mir.contract) ->
      {
        callee;
        parameters = contract.parameters;
        requires = contract.requires;
        ensures = contract.ensures;
        decreases = contract.decreases;
        costs =
          List.filter
            (fun (cost : Mir.cost) ->
              match cost with { resource = Time; bound = Finite; _ } -> false | _ -> true)
            contract.costs;
        callbacks = contract.callbacks;
        inherited;
      })
    (Query.demand database Mir.contract_of_path path)

(* Whether the code of a definition holds a [todo] that can be reached. *)
let holds_todo database (key : Names.key) =
  match Query.demand database Mir.mir key with
  | Some code ->
      let holds = ref false in
      Mir.iter_code code ~terminator:(function Todo -> holds := true | _ -> ());
      !holds
  | None -> false

(* The [proof]s written for a trait's laws on a type, in the package: each
   law's name, with the proof's source and the renaming of the proof's
   generic parameters to the type's arguments. *)
let law_proofs database package (trait : Types.trait_reference) (for_type : Types.ty) =
  let same_argument (left : Types.argument) (right : Types.argument) =
    match (left, right) with Type left, Type right -> Types.equal left right | _ -> left = right
  in
  List.concat_map
    (fun module_ ->
      List.filter_map
        (fun (declaration : Names.declaration) ->
          match
            ( declaration.kind,
              Query.demand database Interface.Environment.interface declaration.path )
          with
          | Law_proof, Some (Interface.Environment.Law_proof_interface proven)
            when Path.equal proven.trait.trait trait.trait -> (
              let variables =
                List.map (fun (generic : Types.generic) -> generic.generic) proven.generics
              in
              match Interface.Impls.match_type ~variables [] proven.for_type for_type with
              | Some renaming
                when List.equal same_argument
                       (List.map (Types.substitute_argument renaming) proven.trait.trait_arguments)
                       trait.trait_arguments ->
                  Option.map
                    (fun source -> (proven.law, (source, renaming)))
                    (source_at_key database (Names.key_of declaration))
              | _ -> None)
          | _ -> None)
        (Query.demand database Names.declarations module_))
    (Query.demand database Packages.modules package)

(* Whether an [impl] writes a method whose body holds a [todo]. Its laws
   are about its methods' results, so they wait, as the methods'
   contracts do. *)
let impl_unfinished database (key : Names.key) =
  List.exists (holds_todo database) (Query.demand database Names.contained key)

let law_unshown database (impl : Path.t) (trait : Types.trait_reference) for_type name =
  match Query.demand database Interface.Summary.key impl with
  | Some key ->
      impl_unfinished database key
      || List.exists
           (fun (law, ((proof : source), _)) ->
             law = name && Option.fold ~none:false ~some:(holds_todo database) proof.key)
           (law_proofs database (Path.package impl) trait for_type)
  | None -> false

let make_contract database path ~own ~others ~definition =
  let signature = Interface.Impls.signature database path in
  let pure =
    match signature with
    | Some (signature : Types.signature) -> (
        (* A function of its arguments: it may take them [own], but
           mutates none of the caller's. *)
        signature.uses = Types.no_capabilities
        && signature.terminates
        && List.for_all
             (fun (info : Types.parameter_info) -> info.mode <> Types.Mut)
             signature.parameters
        && match signature.receiver with Some (Mut, _) -> false | _ -> true)
    | None -> false
  in
  let result_kind = match signature with Some { output = Lends _; _ } -> `Lends | _ -> `Returns in
  let definition =
    match definition with
    | Some code when pure && result_kind = `Returns -> Some (own, code)
    | _ -> None
  in
  { parts = own :: others; pure; result_kind; definition }

(* The functional body of the callee at a path as its definition, as a
   caller in [reading_package] reads the body: in another package, the body
   that the callee's package exports. *)
let definition_code ?reading_package database (path : Path.t) =
  match
    Query.demand database
      (match reading_package with
      | Some package when package <> Path.package path -> Mir.exported_definition_of_path
      | _ -> Mir.definition_of_path)
      path
  with
  | Some (Functional definition) -> Some definition
  | Some Not_functional | None -> None

(* The contract of a function, a theorem, or a type's own method. *)
let function_contract ?reading_package database (path : Path.t) =
  Option.bind (source_at database path) (fun (callee, _, _) ->
      Option.map
        (fun own ->
          make_contract database path ~own ~others:[]
            ~definition:(definition_code ?reading_package database path))
        (part_of database path callee))

(* A trait's method's clauses. *)
let trait_part database (trait : Path.t) name receiver =
  let path = Path.Method { owner = trait; name; receiver } in
  Option.bind (source_at database path) (fun (callee, _, _) ->
      part_of ~inherited:true database path callee)

(* A capability's method's contract. Its calls are never a function in the
   logic: two calls may give different results, since the prover never
   models an implementation's state. *)
let capability_contract database (capability : Path.t) name =
  let path = Path.Method { owner = capability; name; receiver = Static } in
  Option.bind (source_at database path) (fun (callee, _, _) ->
      Option.map
        (fun own ->
          { (make_contract database path ~own ~others:[] ~definition:None) with pure = false })
        (part_of database path callee))

let capability_part database (capability : Path.t) name =
  let path = Path.Method { owner = capability; name; receiver = Static } in
  Option.bind (source_at database path) (fun (callee, _, _) -> part_of database path callee)

(* A trait method's body, when it provides one. *)
let provided_body database (trait : Path.t) name receiver =
  Query.demand database Mir.definition_of_path (Path.Method { owner = trait; name; receiver })

(* A trait method's contract: the [impl]'s own clauses with the trait's,
   when the call is known to reach one [impl], and the trait's alone
   through a bound or [any]. *)
let method_contract ?reading_package database (trait : Types.trait_reference) name receiver
    (evidence : evidence) =
  let trait_side = trait_part database trait.trait name receiver in
  match evidence with
  | Impl { impl; _ } -> (
      let path = Path.Method { owner = impl; name; receiver } in
      match source_at database path with
      | Some (callee, _, (Written _ | Generated)) ->
          Option.map
            (fun own ->
              make_contract database path ~own ~others:(Option.to_list trait_side)
                ~definition:(definition_code ?reading_package database path))
            (part_of database path callee)
      | Some (_, _, Inherited _) | None ->
          (* A method the [impl] leaves to its trait: the trait's clauses and
             default body, with the [impl]'s signature for the method. *)
          Option.map
            (fun own ->
              make_contract database path ~own ~others:[]
                ~definition:
                  (definition_code database (Path.Method { owner = trait.trait; name; receiver })))
            trait_side)
  | Bound | Dynamic ->
      Option.map
        (fun own ->
          make_contract database
            (Path.Method { owner = trait.trait; name; receiver })
            ~own ~others:[] ~definition:None)
        trait_side

(* The integer that a formula is, where it is one literal. *)
let literal (formula : Mir.formula) =
  match formula.value with
  | { statements = []; value = Constant { value = Integer number; _ } } -> Some number
  | _ -> None

let distinct_counters counters =
  List.fold_left
    (fun distinct counter -> if List.mem counter distinct then distinct else distinct @ [ counter ])
    [] counters

(* A cost clause's resource, with the locals it is read with, which give
   a [calls] clause's parameter its value. *)
let resource_of (cost : Mir.cost) ~locals : Costs.resource option =
  match cost.resource with
  | Time -> Some Time
  | Allocations -> Some Allocations
  | Allocated_bytes -> Some Allocated_bytes
  | Calls (Function_parameter local) ->
      Option.map (fun term -> Costs.Calls (Through term)) (Locals.find_opt local locals)
  | Calls (Capability path) -> Some (Calls (Capability path))
  | Calls (Capability_method (path, name)) -> Some (Calls (Capability_method (path, name)))

let is_test context = match context.current with Path.Test _ -> true | _ -> false

(* Whether a function is a private method that takes [mut self] and is
   written as [fn Type.method], which is a step of an update: its
   receiver's invariant is neither shown at a call nor assumed after. *)
let is_updating_helper database (path : Path.t) =
  match path with
  | Method { receiver = Mut; _ } -> (
      match Interface.Summary.definition database path with
      | Some
          ( _,
            {
              visibility = Private;
              kind = Function { signature = { name = Member_name _; _ }; _ };
              _;
            } ) ->
          true
      | _ -> false)
  | _ -> false

(* Expressions *)

let comparison (comparison : comparison) =
  match comparison with
  | Equal -> Some "="
  | Less -> Some "<"
  | Less_equal -> Some "<="
  | Greater -> Some ">"
  | Greater_equal -> Some ">="
  | Not_equal -> None

(* The longest literal whose bytes are stated one fact each. Every query
   that reaches a literal carries its facts, so a long literal, such as a
   table embedded as text, stalls the solver. A longer literal is known by
   its length alone. *)
let literal_bytes_limit = 256
