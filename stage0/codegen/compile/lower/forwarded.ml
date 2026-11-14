(* A statement that runs no code. *)
let is_bookkeeping (statement : Mir.statement) =
  match statement.kind with
  | Live _ | Dead _ | Loan_start _ | Loan_end _ | Ghost_assert _ | Matched _ | Proof _ -> true
  | Assign _ | Call _ | Lend _ | Slice _ | Template _ | Assert _ | Echo _ | Provide _ | Provide_end
    ->
      false

(* Whether the blocks from [block] on only end scopes and return. *)
let rec only_returns (body : Mir.body) block ~seen =
  (not (List.mem block seen))
  &&
  let basic = body.blocks.(block) in
  List.for_all is_bookkeeping basic.statements
  &&
  match basic.terminator with
  | Return _ -> true
  | Goto next -> only_returns body next ~seen:(block :: seen)
  | _ -> false

type t = { setup : (Mir.local * Types.ty * Mir.call) list; call : Mir.call }

(* What a body does that only forwards: it evaluates the lending call's
   arguments into locals with no name, lends the call's part whole, and
   returns. [held] is the operand that each such local holds: a value, or
   a place that it is bound to. [computed] is each local that the result
   of an intrinsic call is written to first, with the call, in order. *)
type forwarding = {
  held : (Mir.local * Mir.operand) list;
  computed : (Mir.local * Mir.call) list;
  lending : Mir.call;
}

let forwarding (body : Mir.body) : forwarding option =
  let entry = body.blocks.(0) in
  let is_unnamed local =
    match body.locals.(local).kind with Temporary | Lent _ -> true | Source _ -> false
  in
  let rec scan ~held ~computed : Mir.statement list -> _ = function
    | [] -> None
    | statement :: rest -> (
        let is_new local =
          is_unnamed local
          && (not (List.mem_assoc local held))
          && not (List.mem_assoc local computed)
        in
        match statement.kind with
        | _ when is_bookkeeping statement -> scan ~held ~computed rest
        | Assign { target = { root = Local local; projections = [] }; value = Operand operand; _ }
          when is_new local ->
            scan ~held:((local, operand) :: held) ~computed rest
        | Call
            {
              destination = Some { root = Local local; projections = [] };
              call = { callee = Intrinsic _; _ } as call;
            }
          when is_new local ->
            scan ~held ~computed:(computed @ [ (local, call) ]) rest
        | Lend { part; call } when List.for_all is_bookkeeping rest ->
            Some (part, { held; computed; lending = call })
        | _ -> None)
  in
  match (scan ~held:[] ~computed:[] entry.statements, entry.terminator) with
  | ( Some (part, forwarding),
      Yield
        { part = Part (Borrow { place = { root = Local lent; projections = [] }; _ }); resume; _ } )
    when lent = part && only_returns body resume ~seen:[ 0 ] ->
      Some forwarding
  | _ -> None

let substituted_trait substitution (trait : Types.trait_reference) : Types.trait_reference =
  {
    trait with
    trait_arguments = List.map (Types.substitute_argument substitution) trait.trait_arguments;
    associated =
      List.map (fun (name, ty) -> (name, Types.substitute substitution ty)) trait.associated;
  }

(* A callee of the method's body, as the method's instance calls it. A
   capability's method and a function value are no callee of a method that
   only forwards. *)
let substituted_callee substitution (callee : Mir.callee) : Mir.callee option =
  let arguments = List.map (Types.substitute_argument substitution) in
  match callee with
  | Function { path; type_arguments } ->
      Some (Function { path; type_arguments = arguments type_arguments })
  | Trait_method method_ ->
      Some
        (Trait_method
           {
             method_ with
             trait = substituted_trait substitution method_.trait;
             self_type = Types.substitute substitution method_.self_type;
             type_arguments = arguments method_.type_arguments;
             evidence =
               (match method_.evidence with
               | Impl { impl; arguments = impl_arguments } ->
                   Impl
                     {
                       impl;
                       arguments =
                         List.map
                           (fun (parameter, argument) ->
                             (parameter, Types.substitute_argument substitution argument))
                           impl_arguments;
                     }
               | (Bound | Dynamic) as evidence -> evidence);
           })
  | Intrinsic { operation; type_arguments } ->
      Some (Intrinsic { operation; type_arguments = arguments type_arguments })
  | Capability_method _ | Indirect _ -> None

let call ~(substitution : Types.substitution) ~(fresh : unit -> Mir.local) (mir : Mir.t)
    (outer : Mir.call) : t option =
  let body = mir.body in
  let ( let* ) = Option.bind in
  let* { held; computed; lending } = forwarding body in
  (* The method's parameters stand for the outer call's arguments. An
     argument that the method owns would be dropped by the method, and one
     that it leaves out has a default to evaluate: neither is forwarded. *)
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
  let parameter local =
    Option.bind
      (List.find_index (Int.equal local) body.parameters)
      (fun position -> List.nth_opt outer_values position)
  in
  (* The caller's local for each local that an intrinsic call's result is
     written to. *)
  let renamed = List.map (fun (local, _) -> (local, fresh ())) computed in
  (* An operand of the method's body as an operand of the caller's: a
     parameter is the outer call's argument, and a local with no name is
     the operand that it holds, or the caller's local for a computed
     value. *)
  let rec forwarded (value : Mir.operand) : Mir.operand option =
    let projected (written : Mir.place) type_ ~(of_place : Mir.place -> Mir.operand) =
      match written.root with
      | Constant _ -> Some value
      | Local local -> (
          match List.assoc_opt local renamed with
          | Some caller_local ->
              (* The computed value is read where it is: it is a view or
                 another value with nothing to drop. *)
              Some
                (Mir.Borrow
                   {
                     place = { root = Local caller_local; projections = written.projections };
                     type_ = Types.substitute substitution type_;
                     mode = Read;
                     origin = outer.origin;
                   })
          | None -> (
              let stands_for =
                match List.assoc_opt local held with
                | Some operand -> forwarded operand
                | None -> parameter local
              in
              match (stands_for, written.projections) with
              | Some whole, [] -> Some whole
              | Some (Borrow { place; _ } | Use { place; _ }), projections ->
                  Some (of_place { place with projections = place.projections @ projections })
              | Some (Take _ | Constant _), _ :: _ | None, _ -> None))
    in
    match value with
    | Constant _ -> Some value
    | Borrow borrow ->
        projected borrow.place borrow.type_ ~of_place:(fun place ->
            Borrow
              {
                borrow with
                place;
                type_ = Types.substitute substitution borrow.type_;
                origin = outer.origin;
              })
    | Use use ->
        projected use.place use.type_ ~of_place:(fun place ->
            Use
              {
                use with
                place;
                type_ = Types.substitute substitution use.type_;
                origin = outer.origin;
              })
    | Take _ -> None
  in
  let forwarded_call (inner : Mir.call) : Mir.call option =
    let* callee = substituted_callee substitution inner.callee in
    let* arguments =
      List.fold_right
        (fun (argument : Mir.argument) arguments ->
          let* arguments = arguments in
          match argument with
          | Passed passed ->
              let* value = forwarded passed.value in
              Some (Mir.Passed { passed with value } :: arguments)
          | Default -> None)
        inner.arguments (Some [])
    in
    if inner.uses = Types.no_capabilities then
      Some { outer with callee; arguments; uses = inner.uses }
    else None
  in
  let* setup =
    List.fold_right
      (fun (local, inner) setup ->
        let* setup = setup in
        let* call = forwarded_call inner in
        Some
          ((List.assoc local renamed, Types.substitute substitution body.locals.(local).type_, call)
          :: setup))
      computed (Some [])
  in
  let* call = forwarded_call lending in
  Some { setup; call }
