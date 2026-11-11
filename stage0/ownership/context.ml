(* The state of the ownership check of one definition: its locals, its
   source text, and the diagnostics reported so far. *)

module T = Types

(* How a local is bound: it owns its value, it borrows a place read-only, or
   it borrows a place [mut] for a call, an iteration, or a block. *)
type kind = Owned | Borrowed | Borrowed_mut

type context = {
  database : Query.context;
  bounds : T.parameter -> T.trait_reference list;
  spans : Syntax.span array;
  text : string;  (** The definition's source text, in which the spans are offsets. *)
  names : (Core.local, string) Hashtbl.t;
  kinds : (Core.local, kind) Hashtbl.t;
  types : (Core.local, T.ty) Hashtbl.t;
  mutable parameters : Core.local list;
  yields : bool;
      (** The definition is a yielding method. The caller's loop may [break] at a [yield]. *)
  implements_capability : bool;
      (** The definition is a method of an [impl] of a capability. Its callers cannot see the
          implementation, so no view may be stored in [self] or returned from it. *)
  mutable mutable_locals : Core.local list;  (** The locals declared with [var]. *)
  mutable diagnostics : Diagnostic.t list;
  mutable moves : Core.id list;  (** The [Use] nodes that move a place. *)
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
let stores_function context (callee : Core.callee) position =
  let declared (signature : T.signature) =
    let index = if Option.is_some signature.receiver then position - 1 else position in
    match List.nth_opt signature.parameters index with
    | Some parameter when index >= 0 -> List.mem parameter.name signature.stores_functions
    | _ -> false
  in
  match callee with
  | Function { path; _ } ->
      Option.fold ~none:false ~some:declared (Interface.Impls.signature context.database path)
  | Trait_method { trait; name; receiver; _ } ->
      Option.fold ~none:false
        ~some:(fun (method_ : T.trait_method) -> declared method_.method_signature)
        (Infer.Members.trait_method context.database trait.trait name receiver)
  | Capability_method { capability; name } ->
      List.exists
        (fun (method_ : T.trait_method) -> declared method_.method_signature)
        (Infer.Members.trait_methods context.database capability name)
  | Intrinsic _ -> false
  | Indirect _ -> true

let span context (origin : Core.origin) : Syntax.span =
  if origin >= 0 && origin < Array.length context.spans then context.spans.(origin)
  else Syntax.Span.make 0 0

let report context ?(fixes = []) ?(notes = []) code (at : Syntax.span) message =
  context.diagnostics <-
    Diagnostic.make ~fixes
      ~notes:
        (List.map
           (fun ((note : Syntax.span), text) -> (Source.span note.start note.stop, text))
           notes)
      ~code:(Ownership code) (Source.span at.start at.stop) message
    :: context.diagnostics

let kind_of_mode : T.mode -> kind = function Own -> Owned | Read -> Borrowed | Mut -> Borrowed_mut

let kind context (root : Place.root) =
  match root with
  | Constant _ -> Borrowed
  | Environment -> Owned
  | Local local -> Option.value ~default:Owned (Hashtbl.find_opt context.kinds local)

let show_root context (root : Place.root) =
  match root with
  | Local Self -> "self"
  | Local local -> Option.value ~default:"this" (Hashtbl.find_opt context.names local)
  | Constant (Top { name; _ } | Member_constant { name; _ }) -> name
  | Constant path -> Path.show path
  | Environment -> "the lambda's captured variables"

let show context (place : Place.t) =
  show_root context place.root
  ^ String.concat ""
      (List.map (function Place.Field name -> "." ^ name | Element _ -> "[...]") place.steps)

(* The names and kinds of the definition's locals, from its parameters and
   its patterns. *)
let collect context (definition : Core.definition) =
  (match definition with
  | Function { parameters; _ } ->
      List.iter
        (fun (parameter : Core.parameter) ->
          Hashtbl.replace context.names parameter.local parameter.name;
          Hashtbl.replace context.kinds parameter.local (kind_of_mode parameter.mode);
          Hashtbl.replace context.types parameter.local parameter.type_;
          context.parameters <- parameter.local :: context.parameters)
        parameters
  | Type _ | Trait _ | Constant _ | Test _ | Law_proof _ | Empty -> ());
  Core_walk.definition
    {
      Core_walk.ignore_all with
      pattern =
        (fun (node : Core.pattern) ->
          match node.kind with
          | Bind { local; name; mode; mutable_ } ->
              if mutable_ then context.mutable_locals <- local :: context.mutable_locals;
              Hashtbl.replace context.names local name;
              Hashtbl.replace context.kinds local (kind_of_mode mode);
              Hashtbl.replace context.types local node.type_
          | _ -> ());
    }
    definition

(* The start offset of the mark before a place, if the place has that mark.
   The core form does not record marks, so this reads the source text. *)
let mark_start context (place : Syntax.span) ~mark : int option =
  let rec skip_space index =
    if index > 0 && (context.text.[index - 1] = ' ' || context.text.[index - 1] = '\n') then
      skip_space (index - 1)
    else index
  in
  let stop = skip_space (min place.start (String.length context.text)) in
  let length = String.length mark in
  if stop < place.start && stop >= length && String.sub context.text (stop - length) length = mark
  then Some (stop - length)
  else None

(* The edits that replace a move by a copy: insert [.copy()] after the place
   and delete the [own] mark before it. *)
let copy_at context (moved : Syntax.span) =
  (match mark_start context moved ~mark:"own" with
    | Some start -> [ Diagnostic.delete (Source.span start moved.start) ]
    | None -> [])
  @ [ Diagnostic.insert moved.stop ".copy()" ]

(* The span of a place together with the [mut] or [own] mark before it. *)
let with_mark context (place : Syntax.span) : Syntax.span =
  match (mark_start context place ~mark:"mut", mark_start context place ~mark:"own") with
  | Some start, _ | None, Some start -> Syntax.Span.make start place.stop
  | None, None -> place
