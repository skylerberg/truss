(* What checking an expression looks up without checking another: names,
   fields, and members; traits' methods and the [impl]s that answer them; a
   collection's [each]; and finishing a call's record. *)

open Syntax
module T = Types
module C = Checked
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Properties = Interface.Properties
module Lower = Interface.Lower
open State

(* One version of a method: a type's own, or a trait's. *)
type version = Own_version of Path.t | Trait_version of T.trait_reference * T.trait_method

(* The version a call's receiver asks for: the one its mark names, and the
   read-only one when it has none. *)
let marked_receiver (receiver : expression) : Path.receiver =
  match receiver.kind with Mode (Mut, _) -> Mut | Mode (Own, _) -> Own | _ -> Read

(* An expression's value where a type is expected of it. *)
let rec coerce state env ?argument (value : expression) ~found ~expected =
  convert state env ?argument ~expression:value.id value.span ~found ~expected

and literal_type state ~expected kind =
  match Option.map (resolve state) expected with
  | Some expected when Unify.literal_fits kind expected -> expected
  | _ -> Unify.fresh_literal state.unifier kind

(* What a name is as a value, by what it means. *)
and named state env (value : expression) ({ name; target; type_arguments } : Resolve.head) =
  let text = name.text in
  match target with
  | Local id -> (
      state.references <- id :: state.references;
      state.tables.meanings.(value.id) <- Some (Local_value id);
      register_expression state value (fun () -> Use (Local (Named id)));
      match Hashtbl.find_opt state.locals id with
      | Some local -> local.type_
      | None -> bug "the local `%s` has no type" text)
  | Value_parameter parameter ->
      state.tables.meanings.(value.id) <- Some (Generic_value parameter);
      register_expression state value (fun () -> Value_parameter parameter);
      T.builtin USize
  | Type_parameter _ | Capability_parameter _ ->
      error state Not_a_value value.span (Printf.sprintf "`%s` is a type, not a value." text)
  | Definition ((Function | Theorem), path) -> (
      match function_signature state path with
      | Some (Ok signature) ->
          let instance = instantiate state value.span signature in
          Option.iter (explicit_type_arguments state value instance) type_arguments;
          state.tables.meanings.(value.id) <-
            Some (Global { path; type_arguments = instance.type_arguments });
          register_expression state value (fun () -> Form.function_value state value);
          T.Function (T.function_type_of instance.signature)
      | Some (Error report) -> T.Error report
      | None -> bug "`%s` has no signature" (Path.show path))
  | Definition (Constant, path) -> (
      state.tables.meanings.(value.id) <- Some (Global { path; type_arguments = [] });
      register_expression state value (fun () -> Use (Constant path));
      match Query.demand state.database Environment.constant_type path with
      | Some type_ -> type_
      | None -> bug "the constant `%s` has no type" (Path.show path))
  | Definition (Type, path) ->
      if Intrinsic.builtin_of_path path = Some Unit then begin
        state.tables.meanings.(value.id) <-
          Some (Variant_value { type_ = T.unit; variant = "Unit" });
        register_expression state value (fun () -> Construct { variant = None; fields = [] });
        T.unit
      end
      else
        error state Not_a_value value.span
          (Printf.sprintf "`%s` is a type. Build a value with `%s(...)`." text text)
  | Definition ((Trait | Capability), _) ->
      error state Not_a_value value.span (Printf.sprintf "`%s` is not a value." text)
  | Variant (type_path, variant) ->
      variant_value state value type_path variant
        ~arguments:(instantiate_type state value.span type_path)
  | Field field -> (
      match env.self with
      | Some (T.Named { path = self_path; arguments }) -> (
          match Members.fields state.database self_path arguments with
          | Some fields -> (
              match
                List.find_opt (fun (written : T.field) -> written.field_name = field) fields
              with
              | Some written ->
                  register_expression state value (fun () ->
                      Use (Field { base = Local Self; field; type_ = Form.type_of state value }));
                  written.field_type
              | None -> bug "the field `%s` is not in its record" field)
          | None -> bug "the field `%s` is not in a record" field)
      | _ -> bug "the field `%s` is named outside its type" field)
  | Result_value -> (
      state.tables.meanings.(value.id) <- Some Specification_value;
      register_expression state value (fun () -> Result);
      match env.output with
      | Some output -> output_type output
      | None -> bug "`result` is named where nothing is returned")
  | Old | Identical | Cost_function _ ->
      state.tables.meanings.(value.id) <- Some Specification_value;
      error state Not_a_value value.span
        (Printf.sprintf "`%s` is applied to what it is about, as in `%s(...)`." text text)
  | Yielded -> (
      (* The parts handed out so far, in order. *)
      state.tables.meanings.(value.id) <- Some Specification_value;
      register_expression state value (fun () -> Yielded);
      let part =
        match (env.loop_element, env.output) with
        | Some element, _ -> Some element
        | None, Some (Yields (_, part) | Lends (_, part)) -> Some part
        | _ -> None
      in
      match part with
      | Some part -> T.Named { path = sequence_path; arguments = [ T.Type part ] }
      | None -> bug "`yielded` is named where nothing is handed out")
  | Finished ->
      state.tables.meanings.(value.id) <- Some Specification_value;
      register_expression state value (fun () -> Finished);
      T.bool
  | Unknown report -> T.Error report
  | Binding | Module _ -> bug "the name `%s` is not resolved" text

(* A variant used as a value: one with no fields is a value, and one with
   fields is a function that builds it. *)
and variant_value state (value : expression) type_path variant ~arguments =
  let type_ = T.Named { path = type_path; arguments } in
  state.tables.meanings.(value.id) <- Some (Variant_value { type_; variant });
  register_expression state value (fun () -> Form.variant_value state value type_path variant);
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
              costs = [ { amortized = false; resource = Time; bound = Order_of } ];
            }
      | None ->
          error state Unknown_variant value.span
            (Printf.sprintf "`%s` has no variant `%s`." (T.show type_) variant))
  | None -> (
      match Members.broken state.database type_path with
      | Some report -> T.Error report
      | None ->
          error state Unknown_variant value.span
            (Printf.sprintf "`%s` has no variants." (T.show type_)))

and field state (value : expression) base_type (member : name) =
  let unknown candidates =
    error state Unknown_member member.span
      ~fixes:
        (match Resolve.closest member.text candidates with
        | Some candidate ->
            [ fix (Printf.sprintf "Write `%s`." candidate) [ replace member.span candidate ] ]
        | None -> [])
      (Printf.sprintf "`%s` has no field `%s`." (show state base_type) member.text)
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
                error state Private_field member.span
                  (Printf.sprintf
                     "`%s` is opaque, so its fields can be read only in its own package."
                     (show state base_type))
              end
              else begin
                state.tables.meanings.(value.id) <-
                  Some (Field_read { type_ = base_type; field = member.text });
                written.field_type
              end
          | None ->
              if Members.own_methods state.database path member.text <> [] then begin
                error state Not_a_value member.span
                  (Printf.sprintf "`%s` is a method, so it is called: `%s()`." member.text
                     member.text)
              end
              else unknown (List.map (fun (written : T.field) -> written.field_name) fields))
      | None -> (
          match Members.broken state.database path with
          | Some report -> T.Error report
          | None ->
              if Members.own_methods state.database path member.text <> [] then
                error state Not_a_value member.span
                  (Printf.sprintf "`%s` is a method, so it is called: `%s()`." member.text
                     member.text)
              else unknown []))
  | _ -> unknown []

(* [Type.name] read as a value: a variant, a constant under the type, or a
   method as a function. *)
and static_member state (value : expression) type_ (member : name) =
  match type_ with
  | T.Named { path; arguments } ->
      if names_variant member then variant_value state value path member.text ~arguments
      else
        begin match Members.own_constant state.database path member.text with
        | Some constant -> (
            state.tables.meanings.(value.id) <-
              Some (Global { path = constant; type_arguments = [] });
            register_expression state value (fun () -> Use (Constant constant));
            match Query.demand state.database Environment.constant_type constant with
            | Some type_ -> type_
            | None -> bug "the constant `%s` has no type" (Path.show constant))
        | None -> (
            match Members.own_methods state.database path member.text with
            | (_, method_path) :: _ -> (
                match function_signature state method_path with
                | Some (Ok signature) ->
                    let instance = instantiate state value.span signature in
                    (match instance.signature.receiver with
                    | Some (_, receiver) -> ignore (unify state receiver type_)
                    | None -> ());
                    state.tables.meanings.(value.id) <-
                      Some (Global { path = method_path; type_arguments = instance.type_arguments });
                    register_expression state value (fun () -> Form.function_value state value);
                    T.Function (T.function_type_of instance.signature)
                | Some (Error report) -> T.Error report
                | None -> bug "the method `%s` has no signature" (Path.show method_path))
            | [] ->
                error state Unknown_member member.span
                  (Printf.sprintf "`%s` has no member `%s`." (show state type_) member.text))
        end
  | T.Error _ | T.Hole -> type_
  | _ ->
      error state Unknown_member member.span
        (Printf.sprintf "`%s` has no member `%s`." (show state type_) member.text)

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
    Some { callee; arguments; defaults_left_out = left_out; uses = instance.signature.uses; result };
  note_lending state value instance.signature.output;
  Form.register_call state value;
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
  | _ -> bug "a call that yields is not a call of a method"

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

and trait_static_method state path name receiver =
  List.concat_map
    (fun package ->
      List.filter_map
        (fun trait ->
          match Members.trait_method state.database trait name receiver with
          | Some method_ ->
              let reference = trait_reference trait in
              if
                could_implement state
                  (T.Named { path; arguments = fresh_arguments state path })
                  trait
              then Some (reference, method_)
              else None
          | None -> None)
        (Query.demand state.database Names.traits_declaring (package, name)))
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
            if not (T.is_error self_type) then
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
               (Query.demand state.database Names.traits_declaring (package, name)))
           (Members.visible_packages state.database state.package))

(* Whether the traits that declare a method of the same name are related:
   each requires, or is required by, another trait in the list. Only then
   are their methods versions of one method (such as a [self] version and a
   [mut self] version). Unrelated traits that share a method name stay
   ambiguous, whatever receiver each method takes. Otherwise a trait added
   later could take over a call on a temporary without an error. *)
and one_family state (traits : T.trait_reference list) =
  let requires (first : T.trait_reference) (second : T.trait_reference) =
    List.exists
      (fun (bound : T.trait_reference) -> Path.equal bound.trait second.trait)
      (Properties.bound_closure state.database
         ~self:(T.Parameter { owner = first.trait; name = "Self" })
         first)
  in
  let related first second = requires first second || requires second first in
  let rec grow reached left =
    match List.partition (fun trait -> List.exists (related trait) reached) left with
    | [], [] -> true
    | [], _ -> false
    | more, left -> grow (more @ reached) left
  in
  match traits with [] -> true | first :: rest -> grow [ first ] rest

(* The versions of a name on a type, by how each takes [self]: the type's
   own methods and those of the one family of traits that gives it the
   name, together. The traits themselves, when they are not one family. A
   type's own version stands where a trait gives the same one, since that
   clash is reported where the [impl] is. *)
and versions state receiver_type name :
    ((Path.receiver * version) list, T.trait_reference list) Result.t =
  let candidates = trait_candidates state receiver_type name in
  if not (one_family state (List.map fst candidates)) then Error (List.map fst candidates)
  else
    let own =
      match receiver_type with
      | T.Named { path; _ } ->
          List.filter_map
            (fun (receiver, method_path) ->
              if receiver = Path.Static then None else Some (receiver, Own_version method_path))
            (Members.own_methods state.database path name)
      | _ -> []
    in
    let from_traits =
      List.concat_map
        (fun ((trait : T.trait_reference), methods) ->
          List.map
            (fun (method_ : T.trait_method) ->
              (method_.method_receiver, Trait_version (trait, method_)))
            methods)
        candidates
    in
    Ok
      (List.filter_map
         (fun (receiver : Path.receiver) ->
           Option.map
             (fun version -> (receiver, version))
             (List.assoc_opt receiver (own @ from_traits)))
         [ Read; Mut; Own ])

and each_call state (span : span) type_ mode =
  let receiver : Path.receiver = match mode with T.Read -> Read | Mut -> Mut | Own -> Own in
  let found = match versions state type_ "each" with Ok found -> found | Error _ -> [] in
  match List.assoc_opt receiver found with
  | Some (Own_version method_path) -> (
      match function_signature state method_path with
      | Some (Ok signature) -> (
          let instance = instantiate state span signature in
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
                    result = element;
                  },
                  element )
          | _ -> None)
      | Some (Error _) | None -> None)
  | Some (Trait_version (trait, method_)) -> (
      let instance =
        instantiate state span
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
                        | T.Parameter _ -> Bound
                        | _ -> (
                            match implements state type_ trait with
                            | Some evidence -> evidence_of evidence
                            | None -> Built_in));
                    };
                arguments = [];
                defaults_left_out = [];
                uses = instance.signature.uses;
                result = element;
              },
              element )
      | _ -> None)
  | None -> None

(* What a value's [each] yields for a loop's mode. *)
and yielded state (span : span) type_ mode =
  Option.map (fun ((_ : C.call), element) -> element) (each_call state span type_ mode)
