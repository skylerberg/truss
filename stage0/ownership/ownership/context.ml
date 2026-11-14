(* The state of the ownership check of one definition: its locals, its
   source text, and the diagnostics reported so far. *)
(* How a local is bound: it owns its value, it borrows a place read-only, or
   it borrows a place [mut] for a call, an iteration, or a block. *)
type kind = Owned | Borrowed | Borrowed_mut

type context = {
  database : Query.context;
  bounds : Types.parameter -> Types.trait_reference list;
  spans : Syntax.span array;
  mode_keywords : (Core.origin, Types.mode * Core.mode_keyword) Hashtbl.t;
  names : (Core.local, string) Hashtbl.t;
  kinds : (Core.local, kind) Hashtbl.t;
  types : (Core.local, Types.ty) Hashtbl.t;
  mutable parameters : Core.local list;
  implements_capability : bool;
      (** The definition is a method of an [impl] of a capability. Its callers cannot see the
          implementation, so no view may be stored in [self] or returned from it. *)
  mutable mutable_locals : Core.local list;  (** The locals declared with [var]. *)
  mutable diagnostics : Syntax.diagnostic list;
  mutable must_be_disjoint : (Core.origin * Core.origin) list;
      (** Pairs of index calls or slices of one collection, by origin, that must select disjoint
          elements. Each pair becomes a [Disjoint] obligation for the prover. *)
}

let plain context type_ = Interface.Impls.plain context.database ~bounds:context.bounds type_
let copyable context type_ = Interface.Impls.copyable context.database ~bounds:context.bounds type_
let is_view context type_ = Interface.Impls.is_view context.database ~bounds:context.bounds type_

let holds_function context type_ =
  Interface.Impls.holds_function context.database ~bounds:context.bounds type_

(* Whether the callee declares the parameter at [position] as an [own]
   parameter of a function type, where a method's receiver is position 0.
   The callee may store a function that it receives through such a
   parameter. A generic [own] parameter that is instantiated with a function
   type does not count: the callee treats its value as any other view, so
   the view rules track it. *)
(* The signatures that a callee may have: one for a function or a trait
   method, and each implementation's for a capability method. *)
let callee_signatures context (callee : Mir.callee) : Types.signature list =
  match callee with
  | Function { path; _ } -> Option.to_list (Interface.Impls.signature context.database path)
  | Trait_method { trait; name; receiver; _ } ->
      List.map
        (fun (method_ : Types.trait_method) -> method_.method_signature)
        (Option.to_list (Infer.Members.trait_method context.database trait.trait name receiver))
  | Capability_method { capability; name } ->
      List.map
        (fun (method_ : Types.trait_method) -> method_.method_signature)
        (Infer.Members.trait_methods context.database capability name)
  | Intrinsic _ | Indirect _ -> []

let stores_function context (callee : Mir.callee) position =
  let declared (signature : Types.signature) =
    let index = if Option.is_some signature.receiver then position - 1 else position in
    match List.nth_opt signature.parameters index with
    | Some parameter when index >= 0 -> List.mem parameter.name signature.stores_functions
    | _ -> false
  in
  match callee with
  | Indirect _ -> true
  | _ -> List.exists declared (callee_signatures context callee)

let span context (origin : Core.origin) : Syntax.span =
  if origin >= 0 && origin < Array.length context.spans then context.spans.(origin)
  else Syntax.Span.make 0 0

let report context ?(fixes = []) ?(notes = []) code (at : Syntax.span) message =
  context.diagnostics <-
    Diagnostic.make ~fixes ~notes ~code:(Ownership code) at message :: context.diagnostics

let kind_of_mode : Types.mode -> kind = function
  | Own -> Owned
  | Read -> Borrowed
  | Mut -> Borrowed_mut

let kind context (root : Place.root) =
  match root with
  | Constant _ -> Borrowed
  | Environment -> Owned
  | Local local -> Option.value ~default:Owned (Hashtbl.find_opt context.kinds local)
  | Temporary _ -> Owned

let show_root context (root : Place.root) =
  match root with
  | Local Self -> "self"
  | Local local -> Option.value ~default:"this" (Hashtbl.find_opt context.names local)
  | Temporary _ -> "temporary"
  | Constant (Top { name; _ } | Member_constant { name; _ }) -> name
  | Constant path -> Path.show path
  | Environment -> "the lambda's captured variables"

let show context (place : Place.t) =
  show_root context place.root
  ^ String.concat ""
      (List.map (function Place.Field name -> "." ^ name | Element _ -> "[...]") place.steps)

(* The names, kinds, and types of the definition's locals, which its MIR's
   source locals carry, and the mode keywords of its arguments. A lambda's capture
   is its enclosing body's local, which that body describes. *)
let collect context (mir : Mir.t) =
  let record_mode_keyword (argument : Mir.argument) =
    match argument with
    | Passed
        {
          mode;
          value = Use { origin; _ } | Borrow { origin; _ } | Take { origin; _ };
          mode_keyword = Some mode_keyword;
        } ->
        Hashtbl.replace context.mode_keywords origin (mode, mode_keyword)
    | Passed _ | Default -> ()
  in
  let record_mode_keywords (call : Mir.call) = List.iter record_mode_keyword call.arguments in
  let body (body : Mir.body) =
    Array.iteri
      (fun local (info : Mir.local_info) ->
        match info.kind with
        | Source { local = core; mode; name = Some name; is_var }
          when not (List.mem local body.captures) ->
            Hashtbl.replace context.names core name;
            Hashtbl.replace context.kinds core (kind_of_mode mode);
            Hashtbl.replace context.types core info.type_;
            if is_var then context.mutable_locals <- core :: context.mutable_locals
        | Source _ | Temporary | Lent _ -> ())
      body.locals;
    Array.iter
      (fun (block : Mir.basic_block) ->
        List.iter
          (fun (statement : Mir.statement) ->
            match statement.kind with
            | Call { call; _ } | Lend { call; _ } | Slice { call; _ } | Template { call; _ } ->
                record_mode_keywords call
            | _ -> ())
          block.statements)
      body.blocks
  in
  body mir.body;
  Array.iter body mir.lambdas;
  context.parameters <-
    List.rev
      (List.filter_map
         (fun local ->
           match mir.body.locals.(local).kind with
           | Source { local = core; _ } -> Some core
           | Temporary | Lent _ -> None)
         mir.body.parameters)

(* The edits that replace a move by a copy: insert [.copy()] after the place
   and delete the [own] keyword before it. *)
let copy_at context (moved : Core.origin) =
  (match Hashtbl.find_opt context.mode_keywords moved with
    | Some (Own, { written; operand }) ->
        [
          Diagnostic.delete
            (Syntax.Span.make (span context written).start (span context operand).start);
        ]
    | Some ((Read | Mut), _) | None -> [])
  @ [ Diagnostic.insert (Syntax.Span.zero_width (span context moved).stop) ".copy()" ]

(* The span of a place together with the [mut] or [own] keyword before it. *)
let with_mode_keyword context (place : Core.origin) : Syntax.span =
  match Hashtbl.find_opt context.mode_keywords place with
  | Some (_, { written; _ }) -> span context written
  | None -> span context place
