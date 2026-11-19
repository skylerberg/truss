type t = {
  types : C_types.t;
  item : Lowered.Item.t;
  bytes : (string, int) Hashtbl.t;
  mutable references : Lowered.Item.t list;
  mutable sites : Lowered.site list;
  mutable capabilities : Path.t list;
  mutable prototypes : (C_text.t * C_text.t) list;
  mutable statics : C_text.t list;
  mutable helpers_used : C_runtime.helper list;
  mutable called : Lowered.Item.t list;
  mutable calls : (Path.t * int) list;
  mutable failures : (C_runtime.failure * Lowered.site) list;
}

let create env ~item =
  {
    types = C_types.create env ~owner:(Some item);
    item;
    bytes = Hashtbl.create 16;
    references = [];
    sites = [];
    capabilities = [];
    prototypes = [];
    statics = [];
    helpers_used = [];
    called = [];
    calls = [];
    failures = [];
  }

let add_once ~equal value values =
  if List.exists (equal value) values then values else value :: values

let render_item emission item : C_text.t =
  if not (Lowered.Item.equal item emission.item) then
    emission.references <- add_once ~equal:Lowered.Item.equal item emission.references;
  Name (Item item)

let render_called_item emission item =
  emission.called <- add_once ~equal:Lowered.Item.equal item emission.called;
  render_item emission item

let render_site emission site : C_text.t =
  emission.sites <- site :: emission.sites;
  Concat [ Text "&"; Name (Site site) ]

let render_capability emission capability : C_text.t =
  emission.capabilities <- add_once ~equal:Path.equal capability emission.capabilities;
  Name (Capability capability)

let record_capability_call emission ~capability ~slot =
  emission.calls <- (capability, slot) :: emission.calls

let record_failure emission failure site = emission.failures <- (failure, site) :: emission.failures

let declare_prototype emission symbol declaration =
  if not (List.mem_assoc symbol emission.prototypes) then
    emission.prototypes <- (symbol, declaration) :: emission.prototypes

let render_bytes_name emission text : C_text.t =
  match Hashtbl.find_opt emission.bytes text with
  | Some index -> Name (Byte_constant index)
  | None ->
      let index = Hashtbl.length emission.bytes in
      Hashtbl.replace emission.bytes text index;
      Name (Byte_constant index)

let use_helper emission helper : C_text.t =
  emission.helpers_used <- add_once ~equal:( = ) helper emission.helpers_used;
  Name (Helper helper)

let add_static emission render : C_text.t =
  let name : C_text.t = Name (Static (List.length emission.statics)) in
  emission.statics <- render name :: emission.statics;
  name

let list_references emission = List.rev emission.references

let list_bytes emission =
  List.sort
    (fun (first, _) (second, _) -> Int.compare first second)
    (Hashtbl.fold (fun text index entries -> (index, text) :: entries) emission.bytes [])
