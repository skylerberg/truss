(* Lookups that the expression checker makes: names, fields, and members;
   trait methods and the [impl]s that provide them; the [each] method of a
   collection; and the final record of a call. *)

open Syntax
module T = Types
module C = Tables
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Properties = Interface.Properties
module Lower = Interface.Lower
open State

(* One version of a method: a method of the type, or a trait method. *)
type version = Own_version of Path.t | Trait_version of T.trait_reference * T.trait_method

(* The version of a method that a receiver selects: the version its mark
   names, or the read-only version if it has no mark. *)
let marked_receiver (receiver : expression) : Path.receiver =
  match receiver.kind with Mode (Mut, _) -> Mut | Mode (Own, _) -> Own | _ -> Read

(* Checks a value of type [found] against an expected type, and records the
   conversion in the core form. *)
let rec coerce state env ?argument (value : expression) ~found ~expected =
  convert state env ?argument ~expression:value.id value.span ~found ~expected

and literal_type state ~expected kind =
  match Option.map (resolve state) expected with
  | Some expected when Unify.literal_fits kind expected -> expected
  | _ -> Unify.fresh_literal state.unifier kind

(* The type of a name that is used as a value, according to its referent. *)
and named state env (value : expression) ({ name; target; type_arguments } : Resolve.head) =
  let text = name.text in
  match target with
  | Local id -> (
      state.references <- id :: state.references;
      state.tables.resolutions.(value.id) <- Some (Local_value id);
      register_expression state value (fun () -> Form.local_use state ~origin:value.id id);
      match Hashtbl.find_opt state.locals id with
      | Some local -> local.type_
      | None -> bug "the local `%s` has no type" text)
  | Law_parameter index -> (
      match List.nth_opt state.law_parameters index with
      | Some (_, type_) ->
          register_expression state value (fun () ->
              Use (Local { local = Synthetic index; type_ = final state type_; origin = value.id }));
          type_
      | None -> bug "the law has no parameter `%s`" text)
  | Value_parameter parameter ->
      state.tables.resolutions.(value.id) <- Some (Value_parameter parameter);
      register_expression state value (fun () -> Value_parameter parameter);
      T.builtin USize
  | Type_parameter _ | Capability_parameter _ ->
      error state Not_a_value value.span (Printf.sprintf "`%s` is a type, not a value." text)
  | Definition ((Function | Theorem), path) -> (
      match function_signature state path with
      | Some (Ok signature) ->
          let instance = instantiate state value.span signature in
          Option.iter (explicit_type_arguments state value instance) type_arguments;
          state.tables.resolutions.(value.id) <-
            Some (Global { path; type_arguments = instance.type_arguments });
          register_expression state value (fun () -> Form.function_value state value);
          T.Function (T.function_type_of instance.signature)
      | Some (Error report) -> T.Error report
      | None -> bug "`%s` has no signature" (Path.show path))
  | Definition (Constant, path) -> (
      state.tables.resolutions.(value.id) <- Some (Global { path; type_arguments = [] });
      register_expression state value (fun () ->
          Use (Form.constant_place state ~origin:value.id path));
      match Query.demand state.database Environment.constant_type path with
      | Some type_ -> type_
      | None -> bug "the constant `%s` has no type" (Path.show path))
  | Definition (Type, path) ->
      if Intrinsic.builtin_of_path path = Some Unit then begin
        state.tables.resolutions.(value.id) <-
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
                      Use
                        (Field
                           {
                             base = Form.self_local state env ~origin:value.id;
                             field;
                             type_ = Form.type_of state value;
                             origin = value.id;
                           }));
                  written.field_type
              | None -> bug "the field `%s` is not in its record" field)
          | None -> bug "the field `%s` is not in a record" field)
      | _ -> bug "the field `%s` is named outside its type" field)
  | Result_value -> (
      state.tables.resolutions.(value.id) <- Some Specification_value;
      register_expression state value (fun () -> Result);
      match env.output with
      | Some output -> output_type output
      | None -> bug "`result` is named where nothing is returned")
  | Old | Identical | Specification_function _ ->
      state.tables.resolutions.(value.id) <- Some Specification_value;
      error state Not_a_value value.span
        (Printf.sprintf "`%s` is applied to what it is about, as in `%s(...)`." text text)
  | Yielded -> (
      (* The sequence of the parts yielded so far. *)
      state.tables.resolutions.(value.id) <- Some Specification_value;
      register_expression state value (fun () -> Yielded);
      let part =
        match (env.loop_element, env.output) with
        | Some element, _ -> Some element
        | None, Some (Yields (_, part) | Lends (_, part)) -> Some part
        | _ -> None
      in
      match part with
      | Some part -> T.Named { path = Well_known.path Sequence; arguments = [ T.Type part ] }
      | None -> bug "`yielded` is named where nothing is handed out")
  | Finished ->
      state.tables.resolutions.(value.id) <- Some Specification_value;
      register_expression state value (fun () -> Finished);
      T.bool
  | Unknown report -> T.Error report
  | Binding | Module _ -> bug "the name `%s` is not resolved" text

(* A variant used as a value. A variant without fields is a value. A variant
   with one field is a function that constructs it. A variant with more
   fields is not a function, because its fields have no order. *)
and variant_value state (value : expression) type_path variant ~arguments =
  let type_ = T.Named { path = type_path; arguments } in
  state.tables.resolutions.(value.id) <- Some (Variant_value { type_; variant });
  register_expression state value (fun () -> Form.variant_value state value type_path variant);
  match Members.variants state.database type_path arguments with
  | Some variants -> (
      match
        List.find_opt (fun (written : T.variant) -> written.variant_name = variant) variants
      with
      | Some { fields = None; _ } -> type_
      | Some { fields = Some [ field ]; _ } ->
          T.Function
            {
              inputs = [ (T.Own, field.field_type) ];
              output = Returns type_;
              uses = [];
              costs = [ { amortized = false; resource = Time; bound = Order_of } ];
            }
      | Some { fields = Some fields; _ } ->
          error state Not_a_value value.span
            (Printf.sprintf
               "`%s` has %d fields, so it is not a function: a function takes its arguments by \
                position, and fields have no order. Build it with named fields, as in `%s(%s)`."
               variant (List.length fields) variant
               (String.concat ", "
                  (List.map (fun (field : T.field) -> field.field_name ^ ": ...") fields)))
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
                state.tables.resolutions.(value.id) <-
                  Some (Field_access { type_ = base_type; field = member.text });
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

(* [Type.name] used as a value: a variant, a constant of the type, or a
   method as a function value. *)
and static_member state (value : expression) type_ (member : name) =
  match type_ with
  | T.Named { path; arguments } ->
      if names_variant member then variant_value state value path member.text ~arguments
      else
        begin match Members.own_constant state.database path member.text with
        | Some constant -> (
            state.tables.resolutions.(value.id) <-
              Some (Global { path = constant; type_arguments = [] });
            register_expression state value (fun () ->
                Use (Form.constant_place state ~origin:value.id constant));
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
                    state.tables.resolutions.(value.id) <-
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

(* Explicit type arguments are for the function's own generic parameters, in
   order, after the parameters of a method's type. There must be exactly one
   for each parameter, of the parameter's kind. *)
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
        omitted_defaults = left_out;
        uses = instance.signature.uses;
        callee_result = result;
      };
  note_lending state value instance.signature.output;
  Form.register_call state value;
  (* A call of a yielding method outside a [for] loop creates a cursor. *)
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

(* Whether a type could implement a trait for some type arguments of the
   trait. The call's arguments determine them later. *)
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

(* Finds the [impl] that a trait method call resolves to. The search is
   deferred until the types are inferred, which may be at the end of the
   statement. *)
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

(* The traits that declare a method with the given name and that the type
   could implement. *)
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

(* The versions of a method name on a type, by receiver mode: the methods of
   the type together with the methods of the related traits that declare the
   name. [Error] with the traits if they are not related. If the type and a
   trait both declare a version with the same receiver, the type's version
   is used; the clash is reported at the [impl]. *)
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

(* When a call of a trait's yielding method resolves to a known [impl] that
   defines the method, the callee is the [impl]'s method. The cursor's type
   and a loop's contract then come from that method. The trait's method
   cannot provide them, because [Self.Element] is abstract there. *)
and impl_method_if_resolved state type_ (version : version) =
  match version with
  | Trait_version (trait, ({ method_signature = { output = Yields _; _ }; _ } as method_)) -> (
      match implements state type_ trait with
      | Some (Impls.From_impl { impl; _ }) ->
          let path : Path.t =
            Method { owner = impl; name = method_.method_name; receiver = method_.method_receiver }
          in
          if Option.is_some (Query.demand state.database Environment.signature path) then
            Own_version path
          else version
      | _ -> version)
  | _ -> version

and each_call state (span : span) type_ mode =
  let receiver : Path.receiver = match mode with T.Read -> Read | Mut -> Mut | Own -> Own in
  let found = match versions state type_ "each" with Ok found -> found | Error _ -> [] in
  match Option.map (impl_method_if_resolved state type_) (List.assoc_opt receiver found) with
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
                    omitted_defaults = [];
                    uses = instance.signature.uses;
                    callee_result = element;
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
                omitted_defaults = [];
                uses = instance.signature.uses;
                callee_result = element;
              },
              element )
      | _ -> None)
  | None -> None

(* The type that the [each] method of a value yields for a loop with the
   given mode. *)
and yielded state (span : span) type_ mode =
  Option.map (fun ((_ : C.call), element) -> element) (each_call state span type_ mode)
