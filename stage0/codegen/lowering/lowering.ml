module Lookups = Lookups
module Positions = Positions

type unsupported = Lower.unsupported = { construct : string; at : Lowered.site option }

type lowered =
  | Compiled of Emit_c.fragment
  | Folded of Lowered.data * Emit_c.fragment
  | Evaluate of Lowered.Item.t * Ground.ty

type linked =
  | Unit of { item : Lowered.Item.t; text_hash : string; sites : Lowered.site list }
  | Evaluated of { item : Lowered.Item.t; evaluator : Lowered.Item.t; ty : Ground.ty }
  | Unsupported of unsupported

type lowered_lookups = {
  system : Libc.system;
  read_source : Path.file -> Source.t;
  interface : Interface.Lookups.t;
  find_lowered : Lowered.Item.t -> (lowered, unsupported) result option;
  read_test_key : Lowered.Item.t -> (string, unsupported) result;
  list_reached_todo_types : Lowered.Item.t -> Path.t list;
  list_linked : Profile.t -> Lowered.Item.t list -> linked list;
  render_unit : Profile.t -> Lowered.Item.t -> string;
}

exception Todo_type = Monomorphic.Todo_type
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
  | Any_drop ty -> Compiled (Drop_and_copy.build_any_drop drop_and_copy ty)
  | Any_copy ty -> Compiled (Drop_and_copy.build_any_copy drop_and_copy ty)
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
  | exception Lower.Unsupported unsupported -> Error unsupported

let test_runner : Lowered.Item.t =
  Lowered.Item.make_code (Well_known.make_path Run_tests) Ground.no_instantiation

let list_references = function
  | Compiled fragment | Folded (_, fragment) -> Emit_c.references fragment
  | Evaluate (evaluator, _) -> [ evaluator; test_runner ]

let list_sites = function
  | Compiled fragment | Folded (_, fragment) -> Emit_c.sites fragment
  | Evaluate _ -> []

let is_evaluated = function Evaluate _ -> true | Compiled _ | Folded _ -> false

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

let derive_test_keys ~read_lowered ~read_known_key =
  Test_keys.derive ~read_known_key ~read_hash_and_references:(fun item ->
      let lowered = read_lowered item in
      (hash_fragment lowered, list_references lowered))

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
