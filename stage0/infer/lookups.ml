(* What checking an expression looks up without checking another: names,
   fields, and members; traits' methods and the [impl]s that answer them; a
   collection's [each]; and finishing a call's record. See TYPECHECKER.md,
   "Members". *)

open Syntax
module T = Types
module C = Checked
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Properties = Interface.Properties
module Lower = Interface.Lower
open State

let rec coerce state (value : expression) ~found ~expected =
  match resolve state found with
  | Never -> ()
  | _ -> if not (unify state expected found) then mismatch state value.span ~expected ~found

and literal_type state ~expected kind =
  match Option.map (resolve state) expected with
  | Some expected when Unify.literal_fits kind expected -> expected
  | _ -> Unify.fresh_literal state.unifier kind

and name state env (value : expression) (path : path) =
  match target state path.last with
  | Some (Local id) -> (
      state.references <- id :: state.references;
      state.tables.meanings.(value.id) <- Some (Local_value id);
      match Hashtbl.find_opt state.locals id with Some local -> local.type_ | None -> T.Error)
  | Some (Generic id) -> (
      match Hashtbl.find_opt state.context.parameters id with
      | Some parameter when path.last.text.[0] >= 'a' && path.last.text.[0] <= 'z' ->
          state.tables.meanings.(value.id) <- Some (Generic_value parameter);
          T.builtin USize
      | _ ->
          report state Not_a_value value.span
            (Printf.sprintf "`%s` is a type, not a value." path.last.text);
          T.Error)
  | Some (Definition definition_path) -> (
      match intrinsic_signature definition_path with
      | Some signature ->
          let instance = instantiate state ~span:value.span signature in
          state.tables.meanings.(value.id) <-
            Some (Global { path = definition_path; type_arguments = instance.type_arguments });
          T.Function (T.function_type_of instance.signature)
      | None -> (
          match Interface.Summary.kind_of state.database definition_path with
          | Some (Function | Theorem) -> (
              match function_signature state definition_path with
              | Some signature ->
                  let instance = instantiate state ~span:value.span signature in
                  state.tables.meanings.(value.id) <-
                    Some
                      (Global { path = definition_path; type_arguments = instance.type_arguments });
                  T.Function (T.function_type_of instance.signature)
              | None -> T.Error)
          | Some Constant -> (
              state.tables.meanings.(value.id) <-
                Some (Global { path = definition_path; type_arguments = [] });
              match Query.demand state.database Environment.constant_type definition_path with
              | Some type_ -> type_
              | None -> T.Error)
          | Some (Type | Trait | Capability) | None ->
              if Intrinsic.builtin_of_path definition_path = Some Unit then begin
                state.tables.meanings.(value.id) <-
                  Some (Variant_value { type_ = T.unit; variant = "Unit" });
                T.unit
              end
              else begin
                (match Interface.Summary.kind_of state.database definition_path with
                | Some Type -> (
                    match Members.shape state.database definition_path with
                    | Some (Record []) -> ()
                    | _ ->
                        report state Not_a_value value.span
                          (Printf.sprintf "`%s` is a type. Build a value with `%s(...)`."
                             path.last.text path.last.text))
                | _ ->
                    report state Not_a_value value.span
                      (Printf.sprintf "`%s` is not a value." path.last.text));
                T.Error
              end
          | Some _ -> T.Error))
  | Some (Variant (type_path, variant)) ->
      variant_value state value type_path variant ~arguments:(fresh_arguments state type_path)
  | Some (Field field) -> (
      match env.self with
      | Some (T.Named { path = self_path; arguments }) -> (
          match Members.fields state.database self_path arguments with
          | Some fields -> (
              match
                List.find_opt (fun (written : T.field) -> written.field_name = field) fields
              with
              | Some written -> written.field_type
              | None -> T.Error)
          | None -> T.Error)
      | _ -> T.Error)
  | Some Result_value -> (
      state.tables.meanings.(value.id) <- Some Specification_value;
      match env.output with Some output -> output_type output | None -> T.Error)
  | Some (Old | Identical | Cost_function _) ->
      state.tables.meanings.(value.id) <- Some Specification_value;
      T.Error
  | Some (Binding | Module _ | Unknown) | None -> T.Error

(* A variant used as a value: one with no fields is a value, and one with
   fields is a function that builds it. *)
and variant_value state (value : expression) type_path variant ~arguments =
  let type_ = T.Named { path = type_path; arguments } in
  state.tables.meanings.(value.id) <- Some (Variant_value { type_; variant });
  match Members.variants state.database type_path arguments with
  | Some variants -> (
      match
        List.find_opt (fun (written : T.variant) -> written.variant_name = variant) variants
      with
      | Some { fields = None; _ } -> type_
      | Some { fields = Some fields; _ } ->
          T.Function
            {
              inputs = List.map (fun (field : T.field) -> (T.Own, field.field_type)) fields;
              output = Returns type_;
              uses = [];
              costs = [ { amortized = false; resource = "time"; bound = "O(...)" } ];
            }
      | None ->
          report state Unknown_variant value.span
            (Printf.sprintf "`%s` has no variant `%s`." (T.show type_) variant);
          T.Error)
  | None -> T.Error

and field state (value : expression) base_type (member : name) =
  let unknown candidates =
    report state Unknown_member member.span
      ~fixes:
        (match Resolve.closest member.text candidates with
        | Some candidate ->
            [ fix (Printf.sprintf "Write `%s`." candidate) [ replace member.span candidate ] ]
        | None -> [])
      (Printf.sprintf "`%s` has no field `%s`." (show state base_type) member.text);
    T.Error
  in
  match base_type with
  | T.Named { path; arguments } -> (
      match Members.fields state.database path arguments with
      | Some fields -> (
          match
            List.find_opt (fun (written : T.field) -> written.field_name = member.text) fields
          with
          | Some written ->
              if not (Members.fields_visible state.database ~package:state.package path) then begin
                report state Private_field member.span
                  (Printf.sprintf
                     "`%s` is opaque, so its fields can be read only in its own package."
                     (show state base_type));
                T.Error
              end
              else begin
                state.tables.meanings.(value.id) <-
                  Some (Field_read { type_ = base_type; field = member.text });
                written.field_type
              end
          | None ->
              if Members.own_methods state.database path member.text <> [] then begin
                report state Not_a_value member.span
                  (Printf.sprintf "`%s` is a method, so it is called: `%s()`." member.text
                     member.text);
                T.Error
              end
              else unknown (List.map (fun (written : T.field) -> written.field_name) fields))
      | None ->
          if Members.own_methods state.database path member.text <> [] then begin
            report state Not_a_value member.span
              (Printf.sprintf "`%s` is a method, so it is called: `%s()`." member.text member.text);
            T.Error
          end
          else unknown [])
  | _ -> unknown []

(* [Type.name] read as a value: a variant, a constant under the type, or a
   method as a function. *)
and static_member state (value : expression) type_ (member : name) =
  match type_ with
  | T.Named { path; arguments } ->
      if member.text.[0] >= 'A' && member.text.[0] <= 'Z' then
        variant_value state value path member.text ~arguments
      else
        begin match Members.own_constant state.database path member.text with
        | Some constant -> (
            state.tables.meanings.(value.id) <-
              Some (Global { path = constant; type_arguments = [] });
            match Query.demand state.database Environment.constant_type constant with
            | Some type_ -> type_
            | None -> T.Error)
        | None -> (
            match Members.own_methods state.database path member.text with
            | (_, method_path) :: _ -> (
                match function_signature state method_path with
                | Some signature ->
                    let instance = instantiate state signature in
                    (match instance.signature.receiver with
                    | Some (_, receiver) -> ignore (unify state receiver type_)
                    | None -> ());
                    state.tables.meanings.(value.id) <-
                      Some (Global { path = method_path; type_arguments = instance.type_arguments });
                    T.Function (T.function_type_of instance.signature)
                | None -> T.Error)
            | [] ->
                report state Unknown_member member.span
                  (Printf.sprintf "`%s` has no member `%s`." (show state type_) member.text);
                T.Error)
        end
  | _ -> T.Error

(* Explicit type arguments give the function's own generic parameters, in
   order, after those of a method's type head: exactly one for each, of its
   kind. *)
and explicit_type_arguments ?(head = 0) state (value : expression) instance items =
  if items <> [] then begin
    let given =
      List.filter_map
        (function
          | Item item -> Some (type_argument_of_expression state item) | Item_constraint _ -> None)
        items
    in
    let own = List.filteri (fun index _ -> index >= head) instance.type_arguments in
    if List.length given <> List.length own then
      report state Arity value.span
        (Printf.sprintf "This takes %d type %s, and %d %s given." (List.length own)
           (if List.length own = 1 then "argument" else "arguments")
           (List.length given)
           (if List.length given = 1 then "is" else "are"))
    else
      List.iter2
        (fun given own ->
          match (given, own) with
          | T.Type given, T.Type own -> ignore (unify state given own)
          | T.Value given, T.Value own -> ignore (Unify.unify_value state.unifier given own)
          | T.Type _, T.Value _ ->
              report state Arity value.span
                "A type argument is given where a `USize` value is expected."
          | T.Value _, T.Type _ ->
              report state Arity value.span
                "A `USize` value is given where a type argument is expected."
          | _ -> ())
        given own
  end

and finish_call state (value : expression) callee (instance : instance) arguments left_out =
  let result = output_type instance.signature.output in
  state.tables.calls.(value.id) <-
    Some
      {
        callee;
        arguments;
        defaults_left_out = left_out;
        uses = instance.signature.uses;
        capability_arguments = [];
        result;
      };
  (* A call to a [yields] method outside a [for] loop makes a cursor. *)
  match instance.signature.output with
  | Yields _ -> cursor_type state callee instance
  | _ -> result

and cursor_type _state callee (instance : instance) =
  match callee with
  | C.Function { path; _ } -> T.Cursor { method_ = path; arguments = instance.type_arguments }
  | C.Trait_method { trait; name; receiver; _ } ->
      T.Cursor
        {
          method_ = Method { owner = trait.trait; name; receiver };
          arguments = instance.type_arguments;
        }
  | _ -> T.Error

and check_specification_call state env (value : expression) (signature : T.signature) =
  if signature.specification_only && not env.specification then
    report state Specification_only value.span
      "This function mentions `Integer`, so it can be called only in specifications."

(* Whether a type could implement a trait, with fresh arguments for the
   trait's own parameters, which the call's arguments then decide. *)
and could_implement state type_ trait =
  let arguments =
    match Query.demand state.database Environment.trait_interface trait with
    | Some interface ->
        List.map (fun (_ : T.generic) -> T.Type (fresh state)) interface.trait_generics
    | None -> []
  in
  Option.is_some (implements state type_ (trait_reference ~arguments trait))

and trait_static_method state path name =
  List.concat_map
    (fun package ->
      List.filter_map
        (fun trait ->
          match
            List.find_opt
              (fun (method_ : T.trait_method) -> method_.method_name = name)
              (Members.trait_methods state.database trait name)
          with
          | Some method_ ->
              let reference = trait_reference trait in
              if
                could_implement state
                  (T.Named { path; arguments = fresh_arguments state path })
                  trait
              then Some (reference, method_)
              else None
          | None -> None)
        (Query.demand state.database Members.traits_declaring (package, name)))
    (Members.visible_packages state.database state.package)

(* The [impl] a trait method call means is found once its types are known,
   which may be at the end of the statement. *)
and resolve_evidence state (value : expression) self_type (reference : T.trait_reference) =
  defer state (fun () ->
      let self_type = zonk state self_type
      and reference = Unify.zonk_trait state.unifier reference in
      if
        T.contains_unsolved self_type
        || List.exists
             (function T.Type type_ -> T.contains_unsolved type_ | _ -> false)
             reference.trait_arguments
      then false
      else begin
        (match implements state self_type reference with
        | Some evidence -> (
            match state.tables.calls.(value.id) with
            | Some ({ callee = Trait_method method_; _ } as call) ->
                state.tables.calls.(value.id) <-
                  Some
                    {
                      call with
                      callee =
                        Trait_method
                          { method_ with trait = reference; evidence = evidence_of evidence };
                    }
            | _ -> ())
        | None ->
            if self_type <> T.Error then
              report state No_impl value.span
                (Printf.sprintf "`%s` does not implement `%s`." (T.show self_type)
                   (T.show_trait reference)));
        true
      end)

(* The traits that give a type a method with a name. *)
and trait_candidates state receiver_type name =
  let with_method (trait : T.trait_reference) =
    match
      List.filter
        (fun (method_ : T.trait_method) -> method_.method_receiver <> Path.Static)
        (Members.trait_methods state.database trait.trait name)
    with
    | [] -> None
    | methods -> Some (trait, methods)
  in
  let unique candidates =
    List.fold_left
      (fun acc ((trait : T.trait_reference), methods) ->
        if
          List.exists
            (fun ((other : T.trait_reference), _) -> Path.equal other.trait trait.trait)
            acc
        then acc
        else acc @ [ (trait, methods) ])
      [] candidates
  in
  match receiver_type with
  | T.Parameter parameter ->
      unique
        (List.filter_map with_method
           (Properties.known_bounds state.database ~bounds:(bounds state) (T.Parameter parameter)))
  | T.Any trait ->
      unique
        (List.filter_map with_method
           (Properties.bound_closure state.database ~self:receiver_type trait))
  | _ ->
      unique
        (List.concat_map
           (fun package ->
             List.filter_map
               (fun trait ->
                 let reference = trait_reference trait in
                 let has_generics =
                   match Query.demand state.database Environment.trait_interface trait with
                   | Some interface -> interface.trait_generics <> []
                   | None -> false
                 in
                 ignore has_generics;
                 if could_implement state receiver_type trait then with_method reference else None)
               (Query.demand state.database Members.traits_declaring (package, name)))
           (Members.visible_packages state.database state.package))

and function_output state (call : C.call) =
  match call.callee with
  | Function { path; _ } ->
      Option.map (fun (signature : T.signature) -> signature.output) (function_signature state path)
  | Trait_method _ -> Some (T.Yields (Read, call.result))
  | _ -> None

and each_call state type_ mode =
  let receiver : Path.receiver = match mode with T.Read -> Read | Mut -> Mut | Own -> Own in
  match type_ with
  | T.Named { path; _ } -> (
      match List.assoc_opt receiver (Members.own_methods state.database path "each") with
      | Some method_path -> (
          match function_signature state method_path with
          | Some signature -> (
              let instance = instantiate state signature in
              (match instance.signature.receiver with
              | Some (_, self_type) -> ignore (unify state self_type type_)
              | None -> ());
              match instance.signature.output with
              | Yields (_, element) ->
                  Some
                    ( {
                        C.callee =
                          Function { path = method_path; type_arguments = instance.type_arguments };
                        arguments = [];
                        defaults_left_out = [];
                        uses = instance.signature.uses;
                        capability_arguments = [];
                        result = element;
                      },
                      element )
              | _ -> None)
          | None -> None)
      | None -> None)
  | T.Parameter _ | T.Any _ -> (
      match trait_candidates state type_ "each" with
      | [ (trait, methods) ] -> (
          match
            List.find_opt
              (fun (method_ : T.trait_method) -> method_.method_receiver = receiver)
              methods
          with
          | Some method_ -> (
              let instance =
                instantiate state
                  ~extra:[ ({ owner = trait.trait; name = "Self" }, T.Type type_) ]
                  method_.method_signature
              in
              match instance.signature.output with
              | Yields (_, element) ->
                  let element = normalize state element in
                  Some
                    ( {
                        C.callee =
                          Trait_method
                            {
                              trait;
                              name = "each";
                              receiver;
                              self_type = type_;
                              type_arguments = [];
                              evidence =
                                (match type_ with
                                | T.Any _ -> Dynamic
                                | T.Parameter parameter -> Bound parameter
                                | _ -> Built_in);
                            };
                        arguments = [];
                        defaults_left_out = [];
                        uses = [];
                        capability_arguments = [];
                        result = element;
                      },
                      element )
              | _ -> None)
          | None -> None)
      | _ -> None)
  | _ -> None

(* What a value's [each] yields for a loop's mode. *)
and yielded state type_ mode =
  let receiver : Path.receiver = match mode with T.Read -> Read | Mut -> Mut | Own -> Own in
  match type_ with
  | T.Named { path; _ } -> (
      match List.assoc_opt receiver (Members.own_methods state.database path "each") with
      | Some method_path -> (
          match function_signature state method_path with
          | Some signature -> (
              let instance = instantiate state signature in
              (match instance.signature.receiver with
              | Some (_, self_type) -> ignore (unify state self_type type_)
              | None -> ());
              match instance.signature.output with Yields (_, element) -> Some element | _ -> None)
          | None -> None)
      | None -> None)
  | _ -> None
