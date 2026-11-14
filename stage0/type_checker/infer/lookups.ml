(* Lookups that the expression checker makes: names, fields, and members;
   trait methods and the [impl]s that provide them; the [each] method of a
   collection; and the final record of a call. *)

open Syntax
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Properties = Interface.Properties
module Lower = Interface.Lower
open State
open Modes
open Instantiation

(* One overload of a method: a method of the type, or a trait method. *)
type overload =
  | Type_overload of Path.t
  | Trait_overload of Types.trait_reference * Types.trait_method

(* The overload of a method that a receiver selects: the overload its mode keyword
   names, or the read-only overload if it has no mode keyword. *)
let marked_receiver (receiver : expression) : Path.receiver =
  match receiver.kind with Mode (Mut, _) -> Mut | Mode (Own, _) -> Own | _ -> Read

(* Checks a value of type [found] against an expected type, and records the
   conversion in the core form. *)
let rec coerce state env ?argument (value : expression) ~actual ~expected =
  convert state env ?argument ~expression:value.id value.span ~actual ~expected

and literal_type state ~expected kind =
  match Option.map (resolve state) expected with
  | Some expected when Unify.literal_fits state.unifier kind expected -> expected
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
              Use
                (Local
                   { local = Synthetic index; type_ = final_type state type_; origin = value.id }));
          type_
      | None -> bug "the law has no parameter `%s`" text)
  | Value_parameter parameter ->
      state.tables.resolutions.(value.id) <- Some (Value_parameter parameter);
      register_expression state value (fun () -> Value_parameter parameter);
      Types.builtin USize
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
          Types.Function (Types.function_type_of instance.signature)
      | Some (Error report) -> Types.Error report
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
          Some (Variant_value { type_ = Types.unit; variant = "Unit" });
        register_expression state value (fun () -> Construct { variant = None; fields = [] });
        Types.unit
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
      | Some (Types.Named { path = self_path; arguments }) -> (
          match Members.fields state.database self_path arguments with
          | Some fields -> (
              match
                List.find_opt (fun (written : Types.field) -> written.field_name = field) fields
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
      | Some output -> Types.result_type output
      | None -> bug "`result` is named where nothing is returned")
  | Old | Identical | Final | Specification_function _ ->
      state.tables.resolutions.(value.id) <- Some Specification_value;
      error state Not_a_value value.span
        (Printf.sprintf "`%s` is applied to its subject, as in `%s(...)`." text text)
  | Visited -> (
      (* The sequence of the values of the loop's iterations before. *)
      state.tables.resolutions.(value.id) <- Some Specification_value;
      register_expression state value (fun () -> Yielded);
      match env.loop_element with
      | Some element ->
          Types.Named { path = Well_known.path Sequence; arguments = [ Types.Type element ] }
      | None -> bug "`visited` is named outside a loop's clauses")
  | Unknown report -> Types.Error report
  | Binding | Module _ -> bug "the name `%s` is not resolved" text

(* A variant used as a value. A variant without fields is a value. A variant
   with one field is a function that constructs it. A variant with more
   fields is not a function, because its fields have no order. *)
and variant_value state (value : expression) type_path variant ~arguments =
  let type_ = Types.Named { path = type_path; arguments } in
  state.tables.resolutions.(value.id) <- Some (Variant_value { type_; variant });
  register_expression state value (fun () -> Form.variant_value state value type_path variant);
  match Members.variants state.database type_path arguments with
  | Some variants -> (
      match
        List.find_opt (fun (written : Types.variant) -> written.variant_name = variant) variants
      with
      | Some { fields = None; _ } -> type_
      | Some { fields = Some [ field ]; _ } ->
          Types.Function
            {
              inputs = [ (Types.Own, field.field_type) ];
              output = Returns type_;
              uses = Types.no_capabilities;
              costs = [ { amortized = false; resource = Time; bound = Order_of } ];
            }
      | Some { fields = Some fields; _ } ->
          error state Not_a_value value.span
            (Printf.sprintf
               "`%s` has %d fields, so it is not a function: a function takes its arguments by \
                position, and fields have no order. Build it with named fields, as in `%s(%s)`."
               variant (List.length fields) variant
               (String.concat ", "
                  (List.map (fun (field : Types.field) -> field.field_name ^ ": ...") fields)))
      | None ->
          error state Unknown_variant value.span
            (Printf.sprintf "`%s` has no variant `%s`." (Types.show type_) variant))
  | None -> (
      match Members.broken state.database type_path with
      | Some report -> Types.Error report
      | None ->
          error state Unknown_variant value.span
            (Printf.sprintf "`%s` has no variants." (Types.show type_)))

and field state (value : expression) base_type (member : name) =
  let unknown candidates =
    error state Unknown_member member.span
      ~fixes:
        (match Diagnostic.closest member.text candidates with
        | Some candidate ->
            [ fix (Printf.sprintf "Write `%s`." candidate) [ replace member.span candidate ] ]
        | None -> [])
      (Printf.sprintf "`%s` has no field `%s`." (show state base_type) member.text)
  in
  match base_type with
  | Types.Named { path; arguments } -> (
      match Members.fields state.database path arguments with
      | Some fields -> (
          match
            List.find_opt (fun (written : Types.field) -> written.field_name = member.text) fields
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
              else unknown (List.map (fun (written : Types.field) -> written.field_name) fields))
      | None -> (
          match Members.broken state.database path with
          | Some report -> Types.Error report
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
  | Types.Named { path; arguments } ->
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
                    Types.Function (Types.function_type_of instance.signature)
                | Some (Error report) -> Types.Error report
                | None -> bug "the method `%s` has no signature" (Path.show method_path))
            | [] ->
                error state Unknown_member member.span
                  (Printf.sprintf "`%s` has no member `%s`." (show state type_) member.text))
        end
  | Types.Error _ | Types.Hole -> type_
  | _ ->
      error state Unknown_member member.span
        (Printf.sprintf "`%s` has no member `%s`." (show state type_) member.text)

(* Explicit type arguments are for the function's own generic parameters, in
   order, after the parameters of a method's type. There must be exactly one
   for each parameter, of the parameter's kind. *)
and explicit_type_arguments ?(head = 0) state (value : expression) instance items =
  if items <> [] then begin
    let written =
      List.filter_map
        (function
          | Item item -> Some (type_argument_of_expression state item) | Item_constraint _ -> None)
        items
    in
    let own = List.filteri (fun index _ -> index >= head) instance.type_arguments in
    if List.length written <> List.length own then
      report state Arity value.span
        (Printf.sprintf "This takes %d type %s, and %d %s given." (List.length own)
           (if List.length own = 1 then "argument" else "arguments")
           (List.length written)
           (if List.length written = 1 then "is" else "are"))
    else
      List.iter2
        (fun written own ->
          match (written, own) with
          | Types.Type written, Types.Type own -> ignore (unify state written own)
          | Types.Value written, Types.Value own ->
              ignore (Unify.unify_value state.unifier written own)
          | Types.Type _, Types.Value _ ->
              report state Argument_kind value.span
                "A type argument is given where a `USize` value is expected."
          | Types.Value _, Types.Type _ ->
              report state Argument_kind value.span
                "A `USize` value is given where a type argument is expected."
          | _ -> ())
        written own
  end

and finish_call state (value : expression) callee (instance : instance) arguments left_out =
  let result = Types.result_type instance.signature.output in
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
  result

and check_specification_call state env (value : expression) (signature : Types.signature) =
  if signature.specification_only && not env.specification then
    report state Specification_only value.span
      "This function mentions `Integer`, so it can be called only in specifications."

(* Whether a type could implement a trait for some type arguments of the
   trait. The call's arguments determine them later. *)
and could_implement state type_ trait =
  let arguments =
    match Query.demand state.database Environment.trait_interface trait with
    | Some interface ->
        List.map (fun (_ : Types.generic) -> Types.Type (fresh state)) interface.trait_generics
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
                  (Types.Named { path; arguments = fresh_arguments state path })
                  trait
              then Some (reference, method_)
              else None
          | None -> None)
        (Query.demand state.database Names.traits_declaring (package, name)))
    (Members.visible_packages state.database state.package)

(* Finds the [impl] that a trait method call resolves to. The search is
   deferred until the types are inferred, which may be at the end of the
   statement. *)
and resolve_evidence state (value : expression) self_type (reference : Types.trait_reference) =
  defer state (fun () ->
      let self_type = zonk state self_type
      and reference = Unify.zonk_trait state.unifier reference in
      if
        Types.contains_unsolved self_type
        || List.exists
             (function Types.Type type_ -> Types.contains_unsolved type_ | _ -> false)
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
            if not (Types.is_error self_type) then
              report state No_impl value.span
                (Printf.sprintf "`%s` does not implement `%s`." (Types.show self_type)
                   (Types.show_trait reference)));
        true
      end)

(* The traits that declare a method with the given name and that the type
   could implement. *)
and trait_candidates state receiver_type name =
  let with_method (trait : Types.trait_reference) =
    match
      List.filter
        (fun (method_ : Types.trait_method) -> method_.method_receiver <> Path.Static)
        (Members.trait_methods state.database trait.trait name)
    with
    | [] -> None
    | methods -> Some (trait, methods)
  in
  let unique candidates =
    List.fold_left
      (fun acc ((trait : Types.trait_reference), methods) ->
        if
          List.exists
            (fun ((other : Types.trait_reference), _) -> Path.equal other.trait trait.trait)
            acc
        then acc
        else acc @ [ (trait, methods) ])
      [] candidates
  in
  match receiver_type with
  | Types.Parameter parameter ->
      unique
        (List.filter_map with_method
           (Properties.known_bounds state.database ~bounds:(bounds state)
              (Types.Parameter parameter)))
  | Types.Any trait ->
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
   are their methods overloads of one method (such as a [self] overload and a
   [mut self] overload). Unrelated traits that share a method name stay
   ambiguous, whatever receiver each method takes. Otherwise a trait added
   later could take over a call on a temporary without an error. *)
and one_family state (traits : Types.trait_reference list) =
  let requires (first : Types.trait_reference) (second : Types.trait_reference) =
    List.exists
      (fun (bound : Types.trait_reference) -> Path.equal bound.trait second.trait)
      (Properties.bound_closure state.database
         ~self:(Types.Parameter { owner = first.trait; name = "Self" })
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

(* The overloads of a method name on a type, by receiver mode: the methods of
   the type together with the methods of the related traits that declare the
   name. [Error] with the traits if they are not related. If the type and a
   trait both declare an overload with the same receiver, the type's overload
   is used; the clash is reported at the [impl]. *)
and overloads state receiver_type name :
    ((Path.receiver * overload) list, Types.trait_reference list) Result.t =
  let candidates = trait_candidates state receiver_type name in
  if not (one_family state (List.map fst candidates)) then Error (List.map fst candidates)
  else
    let own =
      match receiver_type with
      | Types.Named { path; _ } ->
          List.filter_map
            (fun (receiver, method_path) ->
              if receiver = Path.Static then None else Some (receiver, Type_overload method_path))
            (Members.own_methods state.database path name)
      | _ -> []
    in
    let from_traits =
      List.concat_map
        (fun ((trait : Types.trait_reference), methods) ->
          List.map
            (fun (method_ : Types.trait_method) ->
              (method_.method_receiver, Trait_overload (trait, method_)))
            methods)
        candidates
    in
    Ok
      (List.filter_map
         (fun (receiver : Path.receiver) ->
           Option.map
             (fun overload -> (receiver, overload))
             (List.assoc_opt receiver (own @ from_traits)))
         [ Read; Mut; Own ])

(* The callee of the overload of a method of a type that takes [self] with
   [receiver], and the method's signature as a call instantiates it. *)
and method_version state (span : span) type_ name (receiver : Path.receiver) :
    (Tables.callee * Types.signature) option =
  let found = match overloads state type_ name with Ok found -> found | Error _ -> [] in
  match List.assoc_opt receiver found with
  | Some (Type_overload method_path) -> (
      match function_signature state method_path with
      | Some (Ok signature) ->
          let instance = instantiate state span signature in
          (match instance.signature.receiver with
          | Some (_, self_type) -> ignore (unify state self_type type_)
          | None -> ());
          Some
            ( Function { path = method_path; type_arguments = instance.type_arguments },
              instance.signature )
      | Some (Error _) | None -> None)
  | Some (Trait_overload (trait, method_)) ->
      let instance =
        instantiate state span
          ~extra:[ ({ owner = trait.trait; name = "Self" }, Types.Type type_) ]
          method_.method_signature
      in
      Some
        ( Trait_method
            {
              trait;
              name;
              receiver;
              self_type = type_;
              type_arguments = [];
              evidence =
                (match type_ with
                | Types.Any _ -> Dynamic
                | Types.Parameter _ -> Bound
                | _ -> (
                    match implements state type_ trait with
                    | Some evidence -> evidence_of evidence
                    | None -> Built_in));
            },
          instance.signature )
  | None -> None

and argumentless_call callee (signature : Types.signature) result : Tables.call =
  { callee; arguments = []; omitted_defaults = []; uses = signature.uses; callee_result = result }

(* The calls that a [for] loop over a collection makes to visit its
   elements by position: of its [count], and of the overload of its
   [element] that takes [self] with the loop's mode. The loop, the type of
   its elements, and the mode it binds each with. *)
and elements_calls state (span : span) type_ (mode : Types.mode) =
  let receiver : Path.receiver = match mode with Read -> Read | Mut -> Mut | Own -> Own in
  let is_usize type_ = Types.is_builtin USize (normalize state type_) in
  match
    ( method_version state span type_ "count" Read,
      method_version state span type_ "element" receiver )
  with
  | Some (count, counted), Some (element, lent) -> (
      match (counted.parameters, counted.output, lent.parameters, lent.output) with
      | [], Returns count_type, [ position ], Lends (lends, part)
        when is_usize count_type && is_usize position.type_ ->
          let part = normalize state part in
          Some
            ( Tables.Elements
                {
                  count = argumentless_call count counted (Types.builtin USize);
                  element = argumentless_call element lent part;
                  lends;
                },
              part,
              lends )
      | _ -> None)
  | _ -> None

(* The call of a collection's [cursor] that a [for] loop makes to consume
   the collection: the overload that takes [self] as [own], whose result is
   a [Cursor]. The loop and the type of its elements. *)
and consuming_cursor state (span : span) type_ =
  match method_version state span type_ "cursor" Own with
  | Some (callee, ({ parameters = []; output = Returns cursor; _ } as signature)) -> (
      let cursor = normalize state cursor in
      let trait = trait_reference (Well_known.path Cursor) in
      match implements state cursor trait with
      | Some _ ->
          Some
            ( Tables.Pulled
                {
                  cursor;
                  made_by = Some (argumentless_call callee signature cursor);
                  remaining = remaining_call state span cursor;
                },
              associated state cursor trait "Element" ~at:span )
      | None -> None)
  | _ -> None

(* The call of a cursor's [remaining], if its type has one that takes
   [self] read-only and gives a [USize]: a bound on the values the cursor
   has left. *)
and remaining_call state (span : span) cursor =
  match method_version state span cursor "remaining" Read with
  | Some (callee, ({ parameters = []; output = Returns bound; _ } as signature))
    when Types.is_builtin USize (normalize state bound) ->
      Some (argumentless_call callee signature (Types.builtin USize))
  | _ -> None
