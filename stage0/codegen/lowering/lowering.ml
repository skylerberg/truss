module Lookups = Lookups
module Positions = Positions

type unsupported = Lower.unsupported = { construct : string; at : Lowered.site option }

type lowered =
  | Compiled of Emit_c.fragment
  | Folded of Lowered.data * Emit_c.fragment
  | Evaluate of Lowered.Item.t * Ground.ty

type unbuildable = Unsupported of unsupported | Todo_types of Path.t list
type 'value ran = Ran of 'value | Unfinished of string | Stopped of string
type evaluation = string ran

type linked =
  | Unit of { item : Lowered.Item.t; text_hash : string; sites : Lowered.site list }
  | Evaluated of { item : Lowered.Item.t; evaluator : Lowered.Item.t }
  | Unbuildable of unbuildable

type lowered_lookups = {
  system : Libc.system;
  read_source : Path.file -> Source.t;
  interface : Interface.Lookups.t;
  find_lowered : Lowered.Item.t -> (lowered, unbuildable) result option;
  find_evaluation : Lowered.Item.t -> evaluation option;
  record_evaluation : Lowered.Item.t -> evaluation -> unit;
  read_test_key : Lowered.Item.t -> (string, unbuildable) result;
  list_linked : Profile.t -> Lowered.Item.t list -> linked list;
  render_unit : Profile.t -> Lowered.Item.t -> string;
}

exception Infinite_size = Memory_layout.Infinite_size

let make (context : Lower.context) (item : Lowered.Item.t) : lowered =
  let env = Lower.env context in
  let drop_and_copy = Lower.drop_and_copy context in
  match item with
  | Code { path; instantiation; assumes_condition } ->
      Compiled (Lower.lower_source_code context ~path ~instantiation ~assumes_condition)
  | Generated generated -> Compiled (Lower.lower_generated context generated)
  | Table table -> Compiled (Emit_c.make_table_fragment env (Lower.lower_table context table))
  | (Constant _ | Assertion _) as evaluated -> (
      match Lower.lower_evaluated context evaluated with
      | Folded data -> Folded (data, Emit_c.make_data_fragment env data)
      | Run ty -> Evaluate (Evaluator evaluated, ty))
  | Drop ty -> Compiled (Drop_and_copy.drop drop_and_copy ty)
  | Copy ty -> Compiled (Drop_and_copy.copy drop_and_copy ty)
  | Untyped_drop ty -> Compiled (Drop_and_copy.build_untyped_drop drop_and_copy ty)
  | Debug ty -> Compiled (Debug_output.build_debug env ty)
  | Encode ty -> Compiled (Encoding.encode env ty)
  | Evaluator evaluated -> Compiled (Lower.lower_evaluator context evaluated)

let make_env system interface =
  Memory_layout.create system
    ~compute_shape:(Monomorphic.compute_shape (Lower.make_monomorphic_context interface))

let lower system (lookups : Lookups.t) item =
  let env = make_env system lookups.interface in
  match
    Compiler_bug.run_while_doing ~stage:"Lowering"
      ("lowering " ^ Lowered.Item.to_string item)
      (fun () -> make (Lower.make_context ~env lookups) item)
  with
  | lowered -> Ok lowered
  | exception Lower.Unsupported unsupported -> Error (Unsupported unsupported)
  | exception Monomorphic.Todo_type path -> Error (Todo_types [ path ])

let test_runner : Lowered.Item.t =
  Lowered.Item.make_code (Well_known.make_path Run_tests) Ground.no_instantiation

let list_references = function
  | Compiled fragment | Folded (_, fragment) -> Emit_c.references fragment
  | Evaluate (evaluator, _) -> [ evaluator; test_runner ]

let list_sites = function
  | Compiled fragment | Folded (_, fragment) -> Emit_c.sites fragment
  | Evaluate _ -> []

let is_evaluated = function Evaluate _ -> true | Compiled _ | Folded _ -> false

let make_data env item ty encoded =
  Emit_c.make_data_fragment env { data_item = item; ty; value = Encoding.decode env ty encoded }

let render_unit system (interface : Interface.Lookups.t) profile ~read_source ~is_worked_on
    ~find_lowered fragment =
  let positions = Positions.create interface.names ~read_source in
  Emit_c.render_unit (make_env system interface) profile
    ~resolve_position:(fun site ->
      let { Positions.file; line; column } = Positions.locate_site positions site in
      { file = Path.show_file file; line; column })
    ~is_worked_on
    ~find_fragment:(fun called ->
      match find_lowered called with
      | Some (Compiled copy | Folded (_, copy)) -> Some copy
      | Some (Evaluate _) | None -> None)
    fragment

let check_calls interface ~find_call_edges item = function
  | Compiled fragment -> Call_edge_check.check interface ~find_call_edges item fragment
  | Folded _ | Evaluate _ -> ()

let evaluated_fragment_hash =
  Blake3.derive_key ~context:"truss 2026-11-16 evaluated constant fragment hash" ""

let hash_fragment = function
  | Compiled fragment | Folded (_, fragment) -> Emit_c.hash fragment
  | Evaluate _ -> evaluated_fragment_hash

module Item_table = Hashtbl.Make (Lowered.Item)

let merge_unbuildable failures =
  match List.concat_map (function Todo_types types -> types | Unsupported _ -> []) failures with
  | [] -> List.nth_opt failures 0
  | types -> Some (Todo_types (List.sort_uniq Path.compare types))

let derive_test_keys ~read_lowered ~read_known_key component =
  let lowered = Item_table.create 8 and known = Item_table.create 8 and failures = ref [] in
  let keep table item = function
    | Ok value -> Item_table.replace table item value
    | Error unbuildable -> failures := unbuildable :: !failures
  in
  List.iter (fun item -> keep lowered item (read_lowered item)) component;
  let is_read reference =
    List.exists (Lowered.Item.equal reference) component || Item_table.mem known reference
  in
  List.iter
    (fun item ->
      List.iter
        (fun reference ->
          if not (is_read reference) then keep known reference (read_known_key reference))
        (Option.fold ~none:[] ~some:list_references (Item_table.find_opt lowered item)))
    component;
  match merge_unbuildable (List.rev !failures) with
  | Some unbuildable -> Error unbuildable
  | None ->
      Ok
        (Test_keys.derive ~read_known_key:(Item_table.find known)
           ~read_hash_and_references:(fun item ->
             let code = Item_table.find lowered item in
             (hash_fragment code, list_references code))
           component)

let make_root (path : Path.t) : Lowered.Item.t =
  match path with Test _ -> Generated (Test_main path) | _ -> Generated (Program_main path)

let list_roots ~tests ~mains =
  (if tests = [] then [] else test_runner :: List.map make_root tests) @ List.map make_root mains

module Encoding = Encoding

module For_testing = struct
  module Intrinsics = Intrinsics

  let drop_and_copy = Drop_and_copy.create
  let is_trivial = Drop_and_copy.is_trivial
  let drop = Drop_and_copy.drop
  let copy = Drop_and_copy.copy
  let copy_signature = Drop_and_copy.For_testing.copy_signature
end
