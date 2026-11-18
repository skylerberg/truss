type t = {
  types : C_types.t;
  prefix : string;
  bytes : (string, int) Hashtbl.t;
  mutable prototypes : (string * string) list;
  mutable sites : Lowered.site list;
  mutable statics : string list;
  mutable referenced_items : Lowered.Item.t list;
  mutable called : Lowered.Item.t list;
  mutable calls : (Path.t * int) list;
  mutable failures : (C_runtime.failure * Lowered.site) list;
}

let create env ~prefix =
  {
    types = C_types.create env;
    prefix;
    bytes = Hashtbl.create 16;
    prototypes = [];
    sites = [];
    statics = [];
    referenced_items = [];
    called = [];
    calls = [];
    failures = [];
  }

let add_item item items =
  if List.exists (Lowered.Item.equal item) items then items else item :: items

let refer emission item = emission.referenced_items <- add_item item emission.referenced_items

let record_call emission item =
  refer emission item;
  emission.called <- add_item item emission.called

let record_capability_call emission ~capability ~slot =
  emission.calls <- (capability, slot) :: emission.calls

let record_failure emission failure site = emission.failures <- (failure, site) :: emission.failures

let list_referenced_items emission ~referrer =
  List.filter
    (fun item -> not (Lowered.Item.equal item referrer))
    (List.rev emission.referenced_items)

let declare_prototype emission symbol declaration =
  if not (List.mem_assoc symbol emission.prototypes) then
    emission.prototypes <- (symbol, declaration) :: emission.prototypes

let render_site emission site =
  emission.sites <- site :: emission.sites;
  "&" ^ C_runtime.render_site_symbol site

let render_bytes_symbol emission index = Printf.sprintf "%s_bytes_%d" emission.prefix index

let render_bytes_name emission text =
  match Hashtbl.find_opt emission.bytes text with
  | Some index -> render_bytes_symbol emission index
  | None ->
      let index = Hashtbl.length emission.bytes in
      Hashtbl.replace emission.bytes text index;
      render_bytes_symbol emission index

let add_static emission render =
  let name = Printf.sprintf "%s_static_%d" emission.prefix (List.length emission.statics) in
  emission.statics <- render name :: emission.statics;
  name
