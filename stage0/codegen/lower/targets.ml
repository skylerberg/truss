(* Calls and the evidence they need: what a trait method reaches, how each
   argument is passed, capabilities' and [any] values' tables, and calling
   an instance; with literals and the standard types lowering builds. *)

open Definitions
open Lowering
open Lir_builder

(* Calls *)

(* The instance a trait method's call reaches, once the types are known. *)
let trait_method_key st ~(trait : T.trait_reference) ~name ~receiver ~self_type ~type_arguments
    ~(evidence : C.evidence) =
  let substitute = T.substitute st.frame.code.substitution in
  let impl, arguments =
    match evidence with
    | Impl { impl; arguments } ->
        ( impl,
          List.map (fun (p, a) -> (p, T.substitute_argument st.frame.code.substitution a)) arguments
        )
    | Bound _ -> (
        let self = st.context.monomorphic.normalize (substitute self_type) in
        match
          Interface.Impls.implements st.context.database
            ~bounds:(fun _ -> [])
            self
            (T.substitute_trait st.frame.code.substitution trait)
        with
        | Some (From_impl { impl; substitution }) -> (impl, substitution)
        | _ -> bug "no impl of %s for %s" (T.show_trait trait) (T.show self))
    | Dynamic -> bug "a call through any, which reaches no one instance"
    | Built_in -> bug "a built-in trait's method"
  in
  let impl_interface =
    match Interface.Impls.impl_interface st.context.database impl with
    | Some i -> i
    | None -> bug "no interface for %s" (Path.show impl)
  in
  let impl_arguments =
    List.map
      (fun (generic : T.generic) ->
        match List.assoc_opt generic.generic arguments with
        | Some argument -> Monomorphic.ground_argument st.context.monomorphic [] argument
        | None -> bug "the impl's parameter %s is not bound" generic.generic.name)
      impl_interface.impl_generics
  in
  Instance.Code
    {
      path = Method { owner = impl; name; receiver };
      type_arguments =
        impl_arguments
        @ List.map
            (Monomorphic.ground_argument st.context.monomorphic st.frame.code.substitution)
            type_arguments;
    }

(* An argument as it is passed: by value, by address, or as an owned
   value. *)
(* The operand that gives a place to a parameter that takes it as
   [lir_ty]. *)
let operand_as st (mode : T.mode) ty (place : Lir.place) (lir_ty : Lir.ty option) =
  match lir_ty with
  | None -> None
  | Some (Pointer _) when mode = T.Own -> Some (Lir.Moved_address place)
  | Some (Pointer { writable; _ }) -> Some (Lir.Address { place; writable })
  | Some _ -> ( match mode with Own -> Some (owned st place ty) | Read | Mut -> Some (Copy place))

let pass st (mode : T.mode) ty place =
  operand_as st mode ty place (Convention.parameter st.context.env (Monomorphic.mode mode) ty)

(* How a cursor holds an argument for its method's parameter: an [own]
   argument as a value of its own, since the cursor owns it and may outlive
   the caller's statement, and any other as the parameter takes it. *)
let held context (mode : T.mode) ty =
  match mode with
  | Own -> if (Memory_layout.of_type context.env ty).size = 0 then None else Some (Lir.Value ty)
  | Read | Mut -> Convention.parameter context.env (Monomorphic.mode mode) ty

let hold st mode ty place = operand_as st mode ty place (held st.context mode ty)

(* Calls a function instance with arguments that are places of their
   parameter types, writing the result to [destination]. *)
(* A capability's method: its slot in every table of the capability, and
   its signature. *)
let capability_method context capability name =
  let interface =
    match demand context Environment.trait_interface capability with
    | Some i -> i
    | None -> bug "no interface for %s" (Path.show capability)
  in
  let rec find i = function
    | [] -> bug "%s has no method %s" (Path.show capability) name
    | (m : T.trait_method) :: rest ->
        if m.method_name = name then (i, m.method_signature) else find (i + 1) rest
  in
  find 0 interface.methods

(* The C signature of an entry in a capability's table, which every caller
   and every entry agree on: the evidence, then the method's own. *)
let entry_signature context (signature : T.signature) =
  let lir, result =
    lir_signature context []
      ~parameters:(interface_parameters { signature with receiver = None })
      ~has_defaults:false signature.output
  in
  ({ lir with parameters = Convention.evidence :: lir.parameters }, result)

(* Whether a trait's method can be called through [any]: it has no generic
   parameters of its own, and neither takes nor returns [Self]. *)
let callable_through_any trait (m : T.trait_method) =
  let self = T.Parameter { owner = trait; name = "Self" } in
  let mentions ty = T.equal ty self in
  m.method_receiver <> Static
  && List.for_all
       (fun (g : T.generic) -> Path.equal g.generic.owner trait)
       m.method_signature.generics
  && List.for_all
       (fun (p : T.parameter_info) -> not (mentions p.type_))
       m.method_signature.parameters
  && match m.method_signature.output with Returns ty -> not (mentions ty) | _ -> false

(* The methods of a trait an [any] table has an entry for, in order. *)
let any_methods context trait =
  match demand context Environment.trait_interface trait with
  | Some i -> List.filter (callable_through_any trait) i.methods
  | None -> bug "no interface for %s" (Path.show trait)

(* A method's slot in an [any] table, after the drop in slot 0. *)
let dynamic_slot context trait name =
  let rec find i = function
    | [] -> bug "%s cannot be called through any" name
    | (m : T.trait_method) :: rest ->
        if m.method_name = name then (i, m.method_signature) else find (i + 1) rest
  in
  find 1 (any_methods context trait)

(* The C signature of an entry in an [any] table: the value's pointer, then
   the method's own, with the evidence for what it uses. *)
let any_entry_signature context (signature : T.signature) =
  let lir, result =
    lir_signature context []
      ~parameters:(interface_parameters { signature with receiver = None })
      ~has_defaults:false ~uses:signature.uses signature.output
  in
  ({ lir with parameters = Lir.Raw (Pointer Opaque) :: lir.parameters }, result)

(* The evidence for a capability, where the code being lowered has it. *)
(* The evidence for a capability, where the code being lowered has it. In a
   method of an [impl] of the capability that does not use it, a function
   value that uses it means the implementation itself, so the evidence is
   the implementation's own, made on the stack: its [self], its table, and
   what it captured. *)
let evidence_of st capability =
  match List.find_opt (fun (path, _) -> Path.equal path capability) st.evidence with
  | Some (_, operand) -> operand
  | None -> (
      let missing () = bug "no evidence for %s here" (Path.show capability) in
      (* An [impl]'s methods are anchored at the [impl]. *)
      match st.frame.code.anchor with
      | Impl _ as impl when Path.equal (impl_interface st.context impl).implements.trait capability
        ->
          let interface = impl_interface st.context impl in
          let self_ty =
            Monomorphic.ground st.context.monomorphic st.frame.code.substitution interface.for_type
          in
          let implementation =
            match st.frame.self_place with
            | _ when (Memory_layout.of_type st.context.env self_ty).size = 0 -> Lir.Constant Null
            | Some self -> Lir.Address { place = self; writable = true }
            | None -> missing ()
          in
          let type_arguments =
            List.map
              (fun (g : T.generic) ->
                match List.assoc_opt g.generic st.frame.code.substitution with
                | Some a -> Monomorphic.ground_argument st.context.monomorphic [] a
                | None -> bug "an unbound parameter of %s" (Path.show impl))
              interface.impl_generics
          in
          let outer =
            List.map
              (fun captured ->
                match List.find_opt (fun (path, _) -> Path.equal path captured) st.evidence with
                | Some (_, operand) -> operand
                | None -> bug "no evidence for %s here" (Path.show captured))
              (evidence_for [] interface.impl_uses)
          in
          let slot = local st.b (Evidence (List.length outer)) in
          emit st.b
            (Call
               {
                 target = Intrinsic Evidence_fill;
                 arguments =
                   Address { place = at slot; writable = true }
                   :: implementation
                   :: Constant (Symbol_address (Table { impl; type_arguments }))
                   :: outer;
                 result = Discarded;
               });
          Lir.Address { place = at slot; writable = false }
      | _ -> missing ())

let call_instance st key ~(signature : T.signature) ~substitution
    ~(arguments : (T.mode * Ground.ty * Lir.place) list) ~mask ~destination =
  let lir_signature, result =
    lir_signature st.context substitution ~parameters:(interface_parameters signature)
      ~has_defaults:(has_defaults signature) ~uses:signature.uses signature.output
  in
  let passed = List.filter_map (fun (mode, ty, place) -> pass st mode ty place) arguments in
  let mask =
    (if has_defaults signature then [ constant_int UInt64 (Z.of_int mask) ] else [])
    @ List.map (evidence_of st) (evidence_for substitution signature.uses)
  in
  let target = Lir.Direct { function_ = Instance key; signature = lir_signature } in
  emit st.b
    (Call { target; arguments = passed @ mask; result = Convention.destination result destination });
  if not lir_signature.returns then unreachable_block st

(* Expressions *)

let literal st (id : S.id) =
  match st.frame.code.checked.literals.(id) with
  | Some literal -> literal
  | None -> bug "no literal for %d" id

let constant_of st ty (literal : C.literal) : Lir.operand =
  match (literal, scalar_of st ty) with
  | Integer_value value, Integer integer -> constant_int integer value
  | Integer_value value, Character -> Constant (Character (Z.to_int value))
  | Float_value value, Float64 -> Constant (Float64 (Int64.bits_of_float value))
  | Float_value value, Float32 -> Constant (Float32 (Int32.bits_of_float value))
  | _ -> bug "a literal of type %s" (Ground.to_string ty)

(* A string literal's [String]: its bytes as static data, with capacity
   0. *)
let string_value st ty text =
  match Monomorphic.shape st.context.monomorphic ty with
  | Record [ (field, Typed storage) ] ->
      let storage_value =
        Lir.Build
          {
            ty = storage;
            variant = None;
            fields =
              [
                ("buffer", Constant (Bytes text));
                ("length", usize (String.length text));
                ("capacity", usize 0);
              ];
          }
      in
      (field, storage, storage_value)
  | _ -> bug "%s is not a record of storage" (Ground.to_string ty)

(* What a yielding method yields, in an instance. *)
let cursor_element context (yielding : Ground.yielding) =
  let signature = signature_of context yielding.method_ in
  match signature.output with
  | Yields (_, ty) ->
      Monomorphic.ground context.monomorphic (bind signature.generics yielding.type_arguments) ty
  | _ -> bug "%s does not yield" (Path.show yielding.method_)

(* What a cursor's [next] returns: an [Option] of what it yields. *)
let cursor_result context yielding : Ground.ty =
  Named
    {
      path = Top { module_ = { package = "standard"; modules = [ "option" ] }; name = "Option" };
      arguments = [ Type (cursor_element context yielding) ];
    }

(* Calls a trait's method on a value of a ground type, through the [impl]
   the type has, with arguments that are places. *)
(* A trait of the standard library's [core] module. *)
let core name : Path.t = Top { module_ = { package = "standard"; modules = [ "core" ] }; name }

let trait_call st ~trait ~name ~(receiver : Path.receiver) ~self ~arguments ~destination =
  match
    Interface.Impls.implements st.context.database
      ~bounds:(fun _ -> [])
      (back self)
      { trait; trait_arguments = []; associated = [] }
  with
  | Some (From_impl { impl; substitution }) ->
      let interface = impl_interface st.context impl in
      let type_arguments =
        List.map
          (fun (g : T.generic) ->
            match List.assoc_opt g.generic substitution with
            | Some argument -> Monomorphic.ground_argument st.context.monomorphic [] argument
            | None -> bug "an unbound parameter of %s" (Path.show impl))
          interface.impl_generics
      in
      let path = Path.Method { owner = impl; name; receiver } in
      let signature = signature_of st.context path in
      call_instance st
        (Code { path; type_arguments })
        ~signature
        ~substitution:(bind signature.generics type_arguments)
        ~arguments ~mask:0 ~destination
  | _ -> bug "%s has no impl of %s" (Ground.to_string self) (Path.show trait)
