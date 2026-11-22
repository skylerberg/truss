let is_bookkeeping (statement : Mir.Graph.statement) =
  match statement.kind with
  | Basic
      ( Live _ | Dead _ | Loan_start _ | Loan_end _ | Ghost_assert _ | Path_note _ | Proof _
      | Evaluated_assert _ ) ->
      true
  | Basic (Assign _ | Call _ | Lend _ | Assert _ | Echo _) | Provide_start _ | Provide_end -> false

let rec only_returns (body : Mir.Graph.body) block ~seen =
  (not (List.mem block seen))
  &&
  let basic = body.blocks.(block) in
  List.for_all is_bookkeeping basic.statements
  &&
  match basic.terminator with
  | Return _ -> true
  | Goto next -> only_returns body next ~seen:(block :: seen)
  | _ -> false

type lent = Call of Mir.call | Place of Mir.place
type t = { setup : (Mir.local * Types.ty * Mir.call) list; lent : lent }
type lending = Lending_call of Mir.call | Yielded of Mir.operand

type forwarding = {
  held : (Mir.local * Mir.operand) list;
  computed : (Mir.local * Mir.call) list;
  lending : lending;
}

let find_forwarding (body : Mir.Graph.body) : forwarding option =
  let entry = body.blocks.(0) in
  let is_unnamed local =
    match body.locals.(local).kind with Temporary | Lent _ -> true | Source _ -> false
  in
  let rec scan ~held ~computed : Mir.Graph.statement list -> _ = function
    | [] -> Some (held, computed, None)
    | statement :: rest -> (
        let is_new local =
          is_unnamed local
          && (not (List.mem_assoc local held))
          && not (List.mem_assoc local computed)
        in
        match statement.kind with
        | _ when is_bookkeeping statement -> scan ~held ~computed rest
        | Basic
            (Assign
               { target = { root = Local local; projections = [] }; value = Operand operand; _ })
          when is_new local ->
            scan ~held:((local, operand) :: held) ~computed rest
        | Basic
            (Call
               {
                 destination = Some { root = Local local; projections = [] };
                 call = { callee = { target = Intrinsic _; _ }; _ } as call;
               })
          when is_new local ->
            scan ~held ~computed:(computed @ [ (local, call) ]) rest
        | Basic (Lend { part; call }) when List.for_all is_bookkeeping rest ->
            Some (held, computed, Some (part, call))
        | _ -> None)
  in
  match (scan ~held:[] ~computed:[] entry.statements, entry.terminator) with
  | Some (held, computed, lend), Yield { part = Part (Borrow { place; _ } as yielded); resume; _ }
    when only_returns body resume ~seen:[ 0 ] -> (
      match (lend, place) with
      | Some (part, call), { root = Local lent; projections = [] } when lent = part ->
          Some { held; computed; lending = Lending_call call }
      | None, _ -> Some { held; computed; lending = Yielded yielded }
      | Some _, _ -> None)
  | _ -> None

let substitute_trait substitution (trait : Types.trait_reference) : Types.trait_reference =
  {
    trait with
    trait_arguments = List.map (Types.substitute_argument substitution) trait.trait_arguments;
    associated =
      List.map (fun (name, ty) -> (name, Types.substitute substitution ty)) trait.associated;
  }

let substitute_target substitution (target : Mir.operand Core.target) :
    Mir.operand Core.target option =
  let substitute_instantiation = Types.substitute_instantiation substitution in
  match target with
  | Function { path; instantiation } ->
      Some (Function { path; instantiation = substitute_instantiation instantiation })
  | Trait_method method_ ->
      Some
        (Trait_method
           {
             method_ with
             trait = substitute_trait substitution method_.trait;
             self_type = Types.substitute substitution method_.self_type;
             instantiation = substitute_instantiation method_.instantiation;
             evidence =
               (match method_.evidence with
               | Impl { impl; substitution = impl_substitution } ->
                   Impl
                     {
                       impl;
                       substitution = Types.substitute_substitution substitution impl_substitution;
                     }
               | (Bound | Dynamic) as evidence -> evidence);
           })
  | Intrinsic { operation; type_arguments } ->
      Some
        (Intrinsic
           {
             operation;
             type_arguments = List.map (Types.substitute_argument substitution) type_arguments;
           })
  | Capability_method _ | Indirect _ -> None

let forward_call ~(substitution : Types.substitution) ~(make_fresh_local : unit -> Mir.local)
    (mir : Mir.Graph.t) (outer : Mir.call) : t option =
  let body = mir.body in
  let ( let* ) = Option.bind in
  let* { held; computed; lending } = find_forwarding body in
  let outer_arguments =
    List.map
      (function
        | Mir.Passed { mode = Read | Mut; value; _ } -> Some value | Passed _ | Default -> None)
      outer.arguments
  in
  let* outer_values =
    if List.for_all Option.is_some outer_arguments then Some (List.map Option.get outer_arguments)
    else None
  in
  let find_parameter local =
    Option.bind
      (List.find_index (Int.equal local) body.parameters)
      (fun position -> List.nth_opt outer_values position)
  in
  let renamed = List.map (fun (local, _) -> (local, make_fresh_local ())) computed in
  let rec find_forwarded (value : Mir.operand) : Mir.operand option =
    let find_projected (written : Mir.place) type_ ~(of_place : Mir.place -> Mir.operand) =
      let* projections =
        List.fold_right
          (fun projection projections ->
            let* projections = projections in
            let* projection = find_forwarded_projection projection in
            Some (projection :: projections))
          written.projections (Some [])
      in
      match written.root with
      | Constant _ | Literal _ -> Some (of_place { written with projections })
      | Local local -> (
          match List.assoc_opt local renamed with
          | Some caller_local ->
              Some
                (Mir.Borrow
                   {
                     place = { root = Local caller_local; projections };
                     type_ = Types.substitute substitution type_;
                     mode = Read;
                     origin = outer.origin;
                   })
          | None -> (
              let stands_for =
                match List.assoc_opt local held with
                | Some operand -> find_forwarded operand
                | None -> find_parameter local
              in
              match (stands_for, projections) with
              | Some whole, [] -> Some whole
              | Some (Borrow { place; _ } | Use { place; _ }), projections ->
                  Some (of_place { place with projections = place.projections @ projections })
              | Some (Take _ | Immediate _), _ :: _ | None, _ -> None))
    in
    match value with
    | Immediate _ -> Some value
    | Borrow borrow ->
        find_projected borrow.place borrow.type_ ~of_place:(fun place ->
            Borrow
              {
                borrow with
                place;
                type_ = Types.substitute substitution borrow.type_;
                origin = outer.origin;
              })
    | Use use ->
        find_projected use.place use.type_ ~of_place:(fun place ->
            Use { place; type_ = Types.substitute substitution use.type_; origin = outer.origin })
    | Take _ -> None
  and find_forwarded_projection (projection : Mir.projection) : Mir.projection option =
    match projection with
    | Field _ | Variant_field _ -> Some projection
    | Element { node; index; sequence; _ } ->
        let* index = find_forwarded index in
        Some
          (Mir.Element
             {
               node;
               index;
               sequence = Types.substitute substitution sequence;
               origin = outer.origin;
             })
    | Range { node; start; stop; sequence; _ } ->
        let* start = find_forwarded start in
        let* stop =
          match stop with
          | None -> Some None
          | Some stop -> Option.map Option.some (find_forwarded stop)
        in
        Some
          (Mir.Range
             {
               node;
               start;
               stop;
               sequence = Types.substitute substitution sequence;
               origin = outer.origin;
             }
            : Mir.projection)
  in
  let find_forwarded_call (inner : Mir.call) : Mir.call option =
    let* target = substitute_target substitution inner.callee.target in
    let* arguments =
      List.fold_right
        (fun (argument : Mir.argument) arguments ->
          let* arguments = arguments in
          match argument with
          | Passed passed ->
              let* value = find_forwarded passed.value in
              Some (Mir.Passed { passed with value } :: arguments)
          | Default -> None)
        inner.arguments (Some [])
    in
    Some { outer with callee = { inner.callee with target }; arguments }
  in
  let* setup =
    List.fold_right
      (fun (local, inner) setup ->
        let* setup = setup in
        let* call = find_forwarded_call inner in
        Some
          ((List.assoc local renamed, Types.substitute substitution body.locals.(local).type_, call)
          :: setup))
      computed (Some [])
  in
  match lending with
  | Lending_call lending ->
      let* call = find_forwarded_call lending in
      Some { setup; lent = Call call }
  | Yielded yielded -> (
      match find_forwarded yielded with
      | Some (Borrow { place; _ } | Use { place; _ }) -> Some { setup; lent = Place place }
      | Some (Take _ | Immediate _) | None -> None)
