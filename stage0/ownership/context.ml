(* What the ownership check knows about a definition: places and how two
   overlap, what each local is, and reachability, which decides how long a
   loan lasts. *)

open Syntax
module T = Types
module C = Checked
module Properties = Interface.Properties

type root = Local of id | Self_root

(* An index or a range whose value the checker cannot compare stands for
   some elements. *)
type step = Field of string | Element of id
type place = { root : root; steps : step list }

let show_root names = function
  | Local id -> Option.value ~default:"this" (Hashtbl.find_opt names id)
  | Self_root -> "self"

let show_place names place =
  show_root names place.root
  ^ String.concat ""
      (List.map (function Field name -> "." ^ name | Element _ -> "[...]") place.steps)

type overlap = No_overlap | Overlap | Maybe_disjoint of id * id

(* Two places overlap when one is a prefix of the other. Two different
   indexes of one collection may not, which the prover decides. *)
let overlap left right =
  if left.root <> right.root then No_overlap
  else
    let rec go left right =
      match (left, right) with
      | [], _ | _, [] -> Overlap
      | Field a :: left, Field b :: right -> if a = b then go left right else No_overlap
      | Element a :: left, Element b :: right -> (
          if a = b then go left right
          else match go left right with No_overlap -> No_overlap | _ -> Maybe_disjoint (a, b))
      | _ :: left, _ :: right -> go left right
    in
    go left.steps right.steps

let is_prefix prefix place =
  prefix.root = place.root
  &&
  let rec go = function
    | [], _ -> true
    | Field a :: prefix, Field b :: place -> a = b && go (prefix, place)
    | Element _ :: prefix, Element _ :: place -> go (prefix, place)
    | _ -> false
  in
  go (prefix.steps, place.steps)

(* Locals *)

(* What a local holds: an owned value, a view of a place, or [mut] access
   to one, which lasts only for its call, iteration, or block. *)
type kind = Owned | Viewing | Mut_access

type context = {
  database : Query.context;
  definition : definition;
  resolved : Resolve.resolved;
  checked : C.t;
  bounds : T.parameter -> T.trait_reference list;
  kinds : (id, kind) Hashtbl.t;
  names : (id, string) Hashtbl.t;
  nodes : (id, expression) Hashtbl.t;  (** Every expression of the definition, by its id. *)
  mutable parameters : id list;  (** The body's parameters, which a returned view may come from. *)
  mutable mutable_parameters : id list;
  mutable self_kind : kind option;
  paths : (int, (id * int) list) Hashtbl.t;
      (** For each position, the branches it is in: a branch's id and the arm. *)
  loops : (int, id list) Hashtbl.t;  (** For each position, the loops it is in. *)
  uses : (id, int list) Hashtbl.t;  (** For each local, where it is read. *)
  declared : (id, int) Hashtbl.t;  (** Where each local is bound. *)
  mutable diagnostics : Diagnostic.t list;
  mutable reported : (root * step list) list;
  mutable moves : id list;
  mutable obligations : C.obligation list;
  marks : (int, int) Hashtbl.t;
      (** Where the [own] mark of a moved place starts, by the place's start. *)
}

let report context ?(fixes = []) ?(notes = []) code (span : span) message =
  context.diagnostics <-
    Diagnostic.make ~fixes
      ~notes:
        (List.map (fun ((span : span), text) -> (Source.span span.start span.stop, text)) notes)
      ~code:(Ownership code)
      (Source.span span.start span.stop)
      message
    :: context.diagnostics

let type_of context (value : expression) = C.type_of context.checked value
let plain context type_ = Properties.plain context.database ~bounds:context.bounds type_
let copyable context type_ = Properties.copyable context.database ~bounds:context.bounds type_
let is_view context type_ = Properties.is_view context.database ~bounds:context.bounds type_

(* The collections whose elements are places the compiler knows: an index
   or a slice of one is a part of it, so two of them can be shown to be
   apart. An index of any other collection is a call of its [at], which
   lends, and may go on after what it lends is used. *)
let storage (type_ : T.ty) =
  match type_ with
  | T.Named
      {
        path =
          Top { module_ = { package = "standard"; modules = [ "list" ] }; name = "List" | "Slice" };
        _;
      } ->
      true
  | _ -> T.is_builtin Array type_

(* The place an expression names, from a definition's resolved and checked
   forms alone. *)
let rec place_in (resolved : Resolve.resolved) (checked : C.t) (value : expression) : place option =
  let place_of () = place_in resolved checked in
  match value.kind with
  | Name path -> (
      match resolved.names.(path.last.id) with
      | Some (Local id) -> Some { root = Local id; steps = [] }
      | _ -> None)
  | Self_value -> Some { root = Self_root; steps = [] }
  | Member (base, member) -> (
      match checked.meanings.(value.id) with
      | Some (Field_read _) ->
          Option.map
            (fun place -> { place with steps = place.steps @ [ Field member.text ] })
            (place_of () base)
      | _ -> None)
  | Bracket (base, [ Item key ])
    when (resolved.brackets.(value.id) = Some Index
         ||
         match checked.calls.(value.id) with
         | Some { callee = Trait_method { name = "at"; _ }; _ } -> true
         | _ -> false)
         && match checked.types.(base.id) with Some type_ -> storage type_ | None -> false ->
      (* A slice, as [items[a..b]], is some elements, as an index is one. *)
      Option.map
        (fun place -> { place with steps = place.steps @ [ Element key.id ] })
        (place_of () base)
  | Parenthesized inner -> place_of () inner
  | _ -> None

let place_of context value = place_in context.resolved context.checked value

(* What lends an expression, when it is a part that is lent: the lending
   call, and how the part is lent. A call of a lending method gives a part,
   and so does an index of a collection that is not storage. A field or an
   element of a lent part is lent with it. *)
let rec lending context (value : expression) : (expression * T.mode) option =
  match value.kind with
  | Call _ -> Option.map (fun mode -> (value, mode)) context.checked.lends.(value.id)
  | Bracket (base, _) when context.resolved.brackets.(value.id) <> Some Type_arguments -> (
      match (place_of context value, context.checked.calls.(value.id)) with
      | Some _, _ -> None
      | None, Some { callee = Trait_method { name = "at"; receiver; _ }; _ }
        when not (storage (type_of context base)) ->
          Some (value, if receiver = Mut then T.Mut else T.Read)
      | None, _ -> lending context base)
  | Member (base, _) | Parenthesized base | Mode (_, base) -> lending context base
  | _ -> None

(* The place a lending call lends from, and how: its receiver, when that is
   a place. *)
let lender context (call : expression) =
  match context.checked.calls.(call.id) with
  | Some { arguments; _ } ->
      Option.bind
        (List.find_opt (fun (argument : C.argument) -> argument.parameter = 0) arguments)
        (fun (argument : C.argument) ->
          Option.bind (Hashtbl.find_opt context.nodes argument.expression)
            (fun (receiver : expression) ->
              let receiver = match receiver.kind with Mode (_, inner) -> inner | _ -> receiver in
              Option.map
                (fun place -> (place, if argument.mode = T.Mut then T.Mut else T.Read))
                (place_of context receiver)))
  | None -> None

let kind_of context = function
  | Local id -> Option.value ~default:Owned (Hashtbl.find_opt context.kinds id)
  | Self_root -> Option.value ~default:Viewing context.self_kind

(* Reachability, for liveness *)

(* Whether the code at [later] can run after the code at [earlier]: it comes
   after it, outside every branch arm the earlier is in that it is not in
   itself; or a loop around both brings it round again. *)
let reachable context ~earlier ~later ~declared =
  let path position = Option.value ~default:[] (Hashtbl.find_opt context.paths position) in
  let loops position = Option.value ~default:[] (Hashtbl.find_opt context.loops position) in
  let exclusive =
    List.exists
      (fun (branch, arm) ->
        match List.assoc_opt branch (path later) with Some other -> other <> arm | None -> false)
      (path earlier)
  in
  (later > earlier && not exclusive)
  || List.exists
       (fun loop ->
         List.mem loop (loops later)
         && not
              (List.mem loop
                 (match Hashtbl.find_opt context.loops declared with
                 | Some loops -> loops
                 | None -> [])))
       (loops earlier)

let live context holder ~at =
  let declared = Option.value ~default:0 (Hashtbl.find_opt context.declared holder) in
  List.exists
    (fun use -> reachable context ~earlier:at ~later:use ~declared)
    (Option.value ~default:[] (Hashtbl.find_opt context.uses holder))

(* The names a pattern binds. *)
let bound_names (written : pattern) =
  let found = ref [] in
  let rec go (written : pattern) =
    match written.kind with
    | Binding_or_constant name -> found := name.id :: !found
    | Variant { fields = Some fields; _ } | Record fields ->
        List.iter
          (fun (field : pattern_field) ->
            match field.kind with Named_field (_, inner) | Field inner -> go inner | Rest -> ())
          fields
    | Alternatives alternatives -> List.iter go alternatives
    | _ -> ()
  in
  go written;
  !found
