(* Constants: a constant's value folded exactly from its expression, or
   computed by running its evaluator. *)

open Definitions
open Lowering
open Targets
open Lir_builder

let ( let* ) = Option.bind

(* Every value, if each of them is there. *)
let all values =
  List.fold_right
    (fun value rest ->
      let* value = value in
      let* rest = rest in
      Some (value :: rest))
    values (Some [])

(* An integer of a kind, if the kind holds it. *)
let integer st (kind : Memory_layout.integer) value =
  let low, high = Memory_layout.integer_range (Memory_layout.target st.context.env) kind in
  if Z.leq low value && Z.leq value high then Some (Lir.Static_scalar (Integer (kind, value)))
  else None

(* The integer kind a type is, if it is one. *)
let integer_kind st ty =
  match (Memory_layout.of_type st.context.env ty).form with
  | Scalar (Integer kind) -> Some kind
  | _ -> None

let truth value = Some (Lir.Static_scalar (Bool value))

(* An arithmetic or bitwise operation on two folded numbers, where the
   result is exactly what running the operation gives. Anything else, such
   as a sum that does not fit its type, is left to be run. *)
let arithmetic st ty (operation : Intrinsic.operation) (left : Lir.static_value)
    (right : Lir.static_value) =
  match (left, right) with
  | Static_scalar (Integer (kind, left_value)), Static_scalar (Integer (_, right_value)) -> (
      let bits = 8 * Memory_layout.integer_size (Memory_layout.target st.context.env) kind in
      let number value =
        let* kind = integer_kind st ty in
        integer st kind value
      in
      let shift by =
        if Z.sign right_value >= 0 && Z.lt right_value (Z.of_int bits) then
          number (by left_value (Z.to_int right_value))
        else None
      in
      match operation with
      | Add -> number (Z.add left_value right_value)
      | Subtract -> number (Z.sub left_value right_value)
      | Multiply -> number (Z.mul left_value right_value)
      | Divide -> if Z.equal right_value Z.zero then None else number (Z.div left_value right_value)
      | Remainder ->
          if Z.equal right_value Z.zero then None else number (Z.rem left_value right_value)
      | Bit_and -> number (Z.logand left_value right_value)
      | Bit_or -> number (Z.logor left_value right_value)
      | Bit_xor -> number (Z.logxor left_value right_value)
      | Shift_left -> shift Z.shift_left
      | Shift_right -> shift Z.shift_right
      | _ -> None)
  | Static_scalar (Float64 left_value), Static_scalar (Float64 right_value) -> (
      let number value = Some (Lir.Static_scalar (Float64 (Int64.bits_of_float value))) in
      let left_value = Int64.float_of_bits left_value
      and right_value = Int64.float_of_bits right_value in
      match operation with
      | Add -> number (left_value +. right_value)
      | Subtract -> number (left_value -. right_value)
      | Multiply -> number (left_value *. right_value)
      | Divide -> number (left_value /. right_value)
      | _ -> None)
  | Static_scalar (Float32 left_value), Static_scalar (Float32 right_value) -> (
      let number value = Some (Lir.Static_scalar (Float32 (Int32.bits_of_float value))) in
      let left_value = Int32.float_of_bits left_value
      and right_value = Int32.float_of_bits right_value in
      match operation with
      | Add -> number (left_value +. right_value)
      | Subtract -> number (left_value -. right_value)
      | Multiply -> number (left_value *. right_value)
      | Divide -> number (left_value /. right_value)
      | _ -> None)
  | _ -> None

let negated st (value : Lir.static_value) =
  match value with
  | Static_scalar (Integer (kind, left_value)) -> integer st kind (Z.neg left_value)
  | Static_scalar (Float64 left_value) ->
      Some
        (Lir.Static_scalar
           (Float64 (Int64.bits_of_float (Float.neg (Int64.float_of_bits left_value)))))
  | Static_scalar (Float32 left_value) ->
      Some
        (Lir.Static_scalar
           (Float32 (Int32.bits_of_float (Float.neg (Int32.float_of_bits left_value)))))
  | _ -> None

(* A comparison of two folded integers or two folded [Bool]s. *)
let compared (comparison : Core.comparison) (left : Lir.static_value) (right : Lir.static_value) =
  match (left, right) with
  | Static_scalar (Integer (_, left_value)), Static_scalar (Integer (_, right_value)) ->
      truth
        (match comparison with
        | Equal -> Z.equal left_value right_value
        | Not_equal -> not (Z.equal left_value right_value)
        | Less -> Z.lt left_value right_value
        | Less_equal -> Z.leq left_value right_value
        | Greater -> Z.gt left_value right_value
        | Greater_equal -> Z.geq left_value right_value)
  | Static_scalar (Bool left_value), Static_scalar (Bool right_value) -> (
      match comparison with
      | Equal -> truth (left_value = right_value)
      | Not_equal -> truth (left_value <> right_value)
      | Less | Less_equal | Greater | Greater_equal -> None)
  | _ -> None

(* How deep folding follows calls. A call that is deeper is left to be
   run. *)
let call_depth = 8

(* A constant expression's value, where folding gives exactly what
   running it would. For anything else there is none, and the value is
   computed by running the constant's evaluator. Running is what a
   constant's value means; folding only saves the run.

   What folds: literals, operators on numbers and on [Bool], other constants
   that fold, records, variants, and arrays built from parts that fold, and
   a list literal. A list literal is a block that makes a storage, pushes
   each element, and calls [List.from_storage], so folding follows a block's
   [let]s and pushes, and a call of a function whose body is one expression
   and which has no [requires] clause. [locals] holds the values of the
   locals bound so far. *)
let rec fold ?(depth = call_depth) st (locals : (Core.local, Lir.static_value ref) Hashtbl.t)
    (value : Core.expression) : Lir.static_value option =
  let ty = ground st value.type_ in
  let fold_here = fold ~depth st locals in
  let number literal =
    match constant_of st ty literal with
    | Constant scalar -> Some (Lir.Static_scalar scalar)
    | _ -> None
  in
  match value.kind with
  | Integer integer -> number (Integer_value integer)
  | Float float -> number (Float_value float)
  | Boolean boolean -> truth boolean
  | String text -> (
      match Monomorphic.shape st.context.monomorphic ty with
      | Record [ (field, Typed _) ] ->
          let bytes =
            List.init (String.length text) (fun index ->
                Lir.Static_scalar (Integer (UInt8, Z.of_int (Char.code text.[index]))))
          in
          Some
            (Lir.Static_record
               [
                 ( field,
                   Static_storage
                     { element = Monomorphic.builtin UInt8; elements = bytes; owned = false } );
               ])
      | _ -> None)
  | Use place -> fold_place st locals place
  | Construct { variant; fields } ->
      let* fields =
        all
          (List.map
             (fun (name, field) ->
               let* field = field in
               let* field =
                 match field with Core.Value field -> fold_here field | Place _ -> None
               in
               Some (name, field))
             fields)
      in
      Some
        (match variant with
        | Some variant -> Lir.Static_variant (variant, fields)
        | None -> Static_record fields)
  | Collection_literal { elements; construction = Array } ->
      let* elements = all (List.map fold_here elements) in
      Some (Lir.Static_array elements)
  | Operator { operation = Negate; arguments = [ inner ] } ->
      let* inner = fold_here inner in
      negated st inner
  | Operator { operation; arguments = [ left; right ] } ->
      let* left = fold_here left in
      let* right = fold_here right in
      arithmetic st ty operation left right
  | Compare { comparison; left; right } ->
      let* left = fold_here left in
      let* right = fold_here right in
      compared comparison left right
  | Not inner -> (
      let* inner = fold_here inner in
      match inner with Static_scalar (Bool left_value) -> truth (not left_value) | _ -> None)
  | And (left, right) | Or (left, right) -> (
      let* left = fold_here left in
      let* right = fold_here right in
      match (value.kind, left, right) with
      | And _, Static_scalar (Bool left_value), Static_scalar (Bool right_value) ->
          truth (left_value && right_value)
      | Or _, Static_scalar (Bool left_value), Static_scalar (Bool right_value) ->
          truth (left_value || right_value)
      | _ -> None)
  | Block { statements; value = Some result; _ } ->
      let* _ = all (List.map (fold_statement ~depth st locals) statements) in
      fold_here result
  | Call
      {
        callee = Intrinsic { operation = Storage_with_capacity; type_arguments = [ Type element ] };
        _;
      } ->
      Some (Lir.Static_storage { element = ground st element; elements = []; owned = true })
  | Call { callee = Function { path; type_arguments }; arguments; _ } when depth > 0 -> (
      match demand st.context Infer.core_of_path path with
      | Some
          ( {
              definition =
                Function
                  {
                    parameters;
                    contract = { requires = []; _ };
                    body = Some { statements = []; value = Some result; _ };
                  };
              _;
            },
            _ ) ->
          let* arguments =
            all
              (List.map
                 (fun (argument : Core.argument) ->
                   match argument with
                   | Passed { value = Value value; _ } -> fold_here value
                   | Passed { value = Place place; _ } -> fold_place st locals place
                   | Default -> None)
                 arguments)
          in
          let type_arguments =
            List.map
              (Monomorphic.ground_argument st.context.monomorphic st.frame.code.substitution)
              type_arguments
          in
          let callee =
            enter st.context (frame_of (code_of st.context path type_arguments) ~inlined:[])
          in
          let bound = Hashtbl.create 4 in
          List.iter2
            (fun (parameter : Core.parameter) argument ->
              Hashtbl.replace bound parameter.local (ref argument))
            parameters arguments;
          fold ~depth:(depth - 1) callee bound result
      | _ -> None)
  | _ -> None

(* The folded value at a place: another constant's, or a local's. *)
and fold_place st locals (place : Core.place) =
  match place with
  | Constant { path; _ } -> st.context.constant path
  | Local { local; _ } -> Option.map ( ! ) (Hashtbl.find_opt locals local)
  | Field _ | Lent _ | Temporary _ -> None

(* Folds a statement of a block: a [let] of one name, or a push onto a
   storage that a [let] bound. *)
and fold_statement ~depth st locals (statement : Core.statement) : unit option =
  match statement.kind with
  | Let { pattern = { kind = Bind { local; _ }; _ }; value = Value value; else_ = None } ->
      let* value = fold ~depth st locals value in
      Hashtbl.replace locals local (ref value);
      Some ()
  | Evaluate
      {
        kind =
          Call
            {
              callee = Intrinsic { operation = Storage_push; _ };
              arguments =
                [
                  Passed { value = Place (Local { local; _ }); _ };
                  Passed { value = Value element; _ };
                ];
              _;
            };
        _;
      } -> (
      let* storage = Hashtbl.find_opt locals local in
      let* element = fold ~depth st locals element in
      match !storage with
      | Static_storage contents ->
          storage := Static_storage { contents with elements = contents.elements @ [ element ] };
          Some ()
      | _ -> None)
  | _ -> None

(* The state to lower a constant's expression in, the expression, and its
   type. *)
let constant_state context path =
  let key = key_of context path in
  let value =
    match demand context Infer.core_of_path path with
    | Some ({ definition = Constant value; _ }, _) -> value
    | _ -> bug "%s is not a constant" (Path.show path)
  in
  let ty =
    match demand context Environment.constant_type path with
    | Some ty -> Monomorphic.ground context.monomorphic [] ty
    | None -> bug "%s has no type" (Path.show path)
  in
  let code =
    {
      (unwritten ~definition_key:key ~anchor:path ~substitution:[] ~result:(Returns Types.unit)) with
      text = text_of context key;
    }
  in
  let st = enter context (frame_of code ~inlined:[]) in
  (st, value, ty)

(* A constant's static data, where its value folds, and otherwise the type
   of the value its evaluator computes. *)
type constant = Folded of Lir.data | Run of Ground.ty

let constant context path =
  let st, value, ty = constant_state context path in
  match fold st (Hashtbl.create 4) value with
  | Some value -> Folded { data_key = Constant path; ty; value }
  | None -> Run ty

(* Code run while compiling appends its results, in their binary form,
   to an output it owns, and writes that to standard output as it ends, with
   the standard library's function that writes every byte. *)
let begin_output st =
  let output = temporary st Glue.output_ty in
  emit st.builder (Assign (output, Storage.empty Glue.output_ty));
  output

let write_fully = Well_known.path Write_fully

let write_output st output =
  let builder = st.builder in
  let int32 = Monomorphic.builtin Int32 in
  let view_ty = Storage.view_of_elements (Monomorphic.builtin UInt8) in
  let descriptor = temporary st int32 and view = temporary st view_ty in
  emit builder (Assign (descriptor, Use (Constant (Integer (Int32, Z.one)))));
  emit builder
    (Assign
       ( view,
         Storage.view view_ty
           ~elements:(Copy (Storage.buffer output))
           ~length:(Copy (Storage.length output)) ));
  let signature = signature_of st.context write_fully in
  let result =
    match signature.output with
    | Returns ty -> Monomorphic.ground st.context.monomorphic [] ty
    | Yields _ | Lends _ -> bug "write_fully does not return"
  in
  call_instance st
    (Code { path = write_fully; type_arguments = [] })
    ~signature ~substitution:[]
    ~arguments:[ (Read, int32, descriptor); (Read, view_ty, view) ]
    ~destination:(temporary st result) ()

(* Code run while compiling: computes a constant's value and writes its
   binary form to standard output. *)
let evaluator context path : Lir.t =
  let st, value, ty = constant_state context path in
  start st.builder (block st.builder);
  in_scope st (fun () ->
      let place = temporary st ty in
      Core_form.into st value place;
      let output = begin_output st in
      Glue.encode_call context.glue st.builder
        ~output:(Address { place = output; writable = true })
        ty place;
      write_output st output);
  {
    key = Evaluator path;
    main = finish_function st ~first:[] ~rest:[] ();
    nested = nested_functions st;
  }
