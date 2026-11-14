(* Checks calls: resolving the callee, and calls of methods of types, of
   trait methods (in full form or with a receiver), and of capability
   methods. *)

open Syntax
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Properties = Interface.Properties
module Lower = Interface.Lower
open State
open Modes
open Instantiation
open Hooks
open Lookups
open Calls

let rec call state env ?expected (value : expression) (callee : expression)
    (arguments : argument list) : Types.ty =
  match callee.kind with
  | Member (base, member) -> (
      match static_ state base with
      | Some (Static_type type_) -> static_call state env ?expected value type_ member arguments
      | Some (Static_trait (trait, trait_arguments)) ->
          trait_call_in_full state env value trait ~trait_arguments member arguments
      | Some (Static_capability capability) ->
          capability_call state env value capability member arguments
      | None -> method_call state env ?expected value base member ~type_arguments:[] arguments)
  | Bracket ({ kind = Member (base, member); _ }, items)
    when state.resolved.brackets.(callee.id) = Some Method_bracket ->
      method_call state env ?expected value base member ~type_arguments:items arguments
  | _ -> (
      match head state callee with
      | Some resolution -> call_named state env ?expected value callee resolution arguments
      | None -> function_value_call state env value callee arguments)

(* A call whose callee is a name. The callee is the name's referent. *)
and call_named state env ?expected (value : expression) (callee : expression)
    ({ name; target; type_arguments } : Resolve.head) arguments =
  match target with
  | Old -> (
      match arguments with
      | [ argument ] ->
          register_expression state value (fun () -> Old (build_expression state argument.value));
          expression state env ?expected argument.value
      | _ ->
          arguments_alone state env arguments
            (error state
               (if arguments = [] then Missing_argument else Too_many_arguments)
               value.span "`old` takes one value: `old(value)`."))
  | Identical -> (
      (* [identical(first, second)] compares two values of the same type
         with the solver's equality. *)
      match arguments with
      | [ first; second ] ->
          let first_type = expression state env first.value in
          let second_type = expression state env ~expected:first_type second.value in
          if not (unify state first_type second_type) then
            mismatch state second.value.span ~expected:first_type ~actual:second_type;
          register_expression state value (fun () ->
              let first = build_expression state first.value in
              Identical (first, build_expression state second.value));
          Types.bool
      | _ ->
          report state
            (if List.length arguments < 2 then Missing_argument else Too_many_arguments)
            value.span "`identical` takes two values of one type.";
          arguments_alone state env arguments Types.bool)
  | Specification_function function_ -> (
      let bound_method =
        match (function_, arguments) with
        | Time, [ { value = { kind = Member (base, member); _ }; _ } ] -> (
            match static_ state base with
            | Some (Static_type (Types.Parameter _ as type_)) -> Some (type_, member)
            | _ -> None)
        | _ -> None
      in
      match bound_method with
      | Some (type_, member) -> method_time state value type_ member
      | None ->
          register_expression state value (fun () ->
              Specification_function
                {
                  function_ =
                    (match function_ with
                    | Log -> Log
                    | Power -> Power
                    | Time -> Time
                    | Calls -> Calls);
                  arguments =
                    List.map
                      (fun (argument : argument) -> build_expression state argument.value)
                      arguments;
                });
          arguments_alone state env arguments Types.Integer)
  | Definition (Type, path) -> (
      match named_type state callee path type_arguments with
      | Types.Named { arguments = type_arguments; _ } ->
          construct state env ?expected ~type_arguments value path None arguments
      | _ -> construct state env ?expected value path None arguments)
  | Variant (type_path, variant) ->
      construct state env ?expected value type_path (Some variant) arguments
  | Definition ((Function | Theorem), path) -> (
      match function_signature state path with
      | Some (Ok signature) ->
          named_call state env ?expected value path signature
            ~type_arguments:(Option.value ~default:[] type_arguments)
            arguments
      | Some (Error report) -> arguments_alone state env arguments (Types.Error report)
      | None -> bug "`%s` has no signature" (Path.show path))
  | Definition ((Trait | Capability), _) | Type_parameter _ | Capability_parameter _ ->
      arguments_alone state env arguments
        (error state Not_callable callee.span
           (Printf.sprintf "`%s` is not a function or a type, so it cannot be called." name.text))
  | Unknown report -> arguments_alone state env arguments (Types.Error report)
  | Local _ | Law_parameter _ | Value_parameter _
  | Definition (Constant, _)
  | Field _ | Result_value | Yielded ->
      function_value_call state env value callee arguments
  | Binding | Module _ -> bug "the name `%s` is not resolved" name.text

(* [time(Element.equal)] in a [cost] bound: a bound on the time of any one
   call of a method of a trait that bounds a type parameter. If the bounds
   have several versions of the method, the term names the read-only
   version. *)
and method_time state (value : expression) (type_ : Types.ty) (member : name) =
  let versions =
    List.fold_left
      (fun methods (bound : Types.trait_reference) ->
        List.fold_left
          (fun methods (method_ : Types.trait_method) ->
            if
              List.exists
                (fun ((other : Types.trait_reference), (known : Types.trait_method)) ->
                  Path.equal other.trait bound.trait
                  && known.method_receiver = method_.method_receiver)
                methods
            then methods
            else methods @ [ (bound, method_) ])
          methods
          (Members.trait_methods state.database bound.trait member.text))
      []
      (Properties.known_bounds state.database ~bounds:(bounds state) type_)
  in
  let chosen =
    match versions with
    | [ only ] -> Some only
    | several -> (
        match
          List.filter
            (fun (_, (method_ : Types.trait_method)) -> method_.method_receiver = Read)
            several
        with
        | [ read_only ] -> Some read_only
        | _ -> None)
  in
  match (chosen, versions) with
  | Some (trait, method_), _ ->
      register_expression state value (fun () ->
          Method_time
            (Trait_method
               {
                 trait;
                 name = member.text;
                 receiver = method_.method_receiver;
                 self_type = type_;
                 type_arguments = [];
                 evidence = Bound;
               }));
      Types.Integer
  | None, [] ->
      error state Unknown_member member.span
        (Printf.sprintf "`%s` has no method `%s`: no trait that bounds it declares one."
           (show state type_) member.text)
  | None, _ ->
      error state Ambiguous_method member.span
        (Printf.sprintf
           "`%s` has more than one method `%s`, and none of them is the only one that takes `self` \
            read-only, so `time` cannot tell which one is meant."
           (show state type_) member.text)

(* [Type.name(...)]: a variant constructor, a static method, or a method
   called in full form with its receiver as the first argument. *)
and static_call state env ?expected (value : expression) type_ (member : name) arguments =
  let ambiguous (traits : Types.trait_reference list) =
    arguments_alone state env arguments
      (error state Ambiguous_method member.span
         (Printf.sprintf
            "More than one trait gives `%s` a method `%s`: %s. Call it through the trait to say \
             which."
            (show state type_) member.text
            (String.concat ", " (List.map (fun trait -> "`" ^ Types.show_trait trait ^ "`") traits))))
  in
  let wrong_receiver () =
    arguments_alone state env arguments
      (error state Wrong_receiver member.span
         (Printf.sprintf
            "`%s` has no version for this receiver's mark; mark the receiver `mut` or `own` as its \
             versions take."
            member.text))
  in
  (* A method with [self] called in full form. The first argument is the
     receiver, and its mark selects the version of the method, as it does in
     a call with a dot. *)
  let wanted : Path.receiver =
    match arguments with receiver :: _ -> marked_receiver receiver.value | [] -> Read
  in
  match type_ with
  | Types.Named { path; arguments = type_arguments } when names_variant member ->
      construct state env ?expected ~type_arguments value path (Some member.text) arguments
  | Types.Named { path; _ } -> (
      match List.assoc_opt Path.Static (Members.own_methods state.database path member.text) with
      | Some method_path -> (
          match function_signature state method_path with
          | Some (Ok signature) ->
              let instance = instantiate state value.span signature in
              (* The type's arguments, written or inferred, are the type
                 arguments of the method's type. *)
              let head =
                List.filteri
                  (fun index _ ->
                    index
                    < List.length
                        (match type_ with Types.Named { arguments; _ } -> arguments | _ -> []))
                  instance.type_arguments
              in
              ignore
                (Unify.unify_arguments state.unifier head
                   (match type_ with Types.Named { arguments; _ } -> arguments | _ -> []));
              (match (expected, instance.signature.output) with
              | Some expected, Returns output -> unify_as_hint state output expected
              | _ -> ());
              let matched, left_out =
                match_arguments state value instance.signature.parameters arguments ~record:false
              in
              let checked =
                check_arguments state env instance.signature.parameters matched ~offset:0
              in
              check_specification_call state env value signature;
              finish_call state value
                (Tables.Function { path = method_path; type_arguments = instance.type_arguments })
                instance checked left_out
          | Some (Error report) -> arguments_alone state env arguments (Types.Error report)
          | None -> bug "the method `%s` has no signature" (Path.show method_path))
      | None -> (
          (* A static trait method, as in [Int64.from(count)]. *)
          match trait_static_method state path member.text Static with
          | [ (trait, method_) ] ->
              trait_method_through_type state env ?expected value type_ trait method_ arguments
          | _ :: _ :: _ as several -> ambiguous (List.map fst several)
          | [] -> (
              match versions state type_ member.text with
              | Error traits -> ambiguous traits
              | Ok versions -> (
                  match (arguments, List.assoc_opt wanted versions) with
                  | receiver :: rest, Some (Own_version method_path) ->
                      let inner =
                        match receiver.value.kind with
                        | Mode (_, inner) -> inner
                        | _ -> receiver.value
                      in
                      let receiver_type = expression state env inner in
                      if inner != receiver.value then begin
                        record state receiver.value receiver_type;
                        alias_expression state receiver.value inner
                      end;
                      if not (unify state receiver_type type_) then
                        mismatch state inner.span ~expected:type_ ~actual:receiver_type;
                      let mode : Types.mode =
                        match wanted with Mut -> Mut | Own -> Own | _ -> Read
                      in
                      check_mode state env receiver.value
                        { name = "self"; mode; type_; has_default = false }
                        receiver_type;
                      method_with_receiver state env ?expected value ~receiver:receiver.value
                        ~receiver_type method_path rest
                  | _ :: _, Some (Trait_version (trait, method_)) ->
                      trait_method_through_type state env ?expected value type_ trait method_
                        arguments
                  | _ :: _, None when versions <> [] -> wrong_receiver ()
                  | [], _ when versions <> [] ->
                      error state Missing_argument value.span
                        "A method written in full takes its receiver as its first argument."
                  | _ ->
                      arguments_alone state env arguments
                        (match Members.broken state.database path with
                        | Some report -> Types.Error report
                        | None ->
                            error state Unknown_member member.span
                              (Printf.sprintf "`%s` has no method `%s`." (show state type_)
                                 member.text))))))
  | Types.Parameter parameter -> (
      (* A method of a trait bound: the static method, or the version that
         the first argument's mark selects. Two bounds on the same trait
         differ only in the trait's type arguments, which the call's
         arguments determine. *)
      let without_self =
        List.fold_left
          (fun methods (bound : Types.trait_reference) ->
            match Members.trait_method state.database bound.trait member.text Static with
            | Some method_
              when not
                     (List.exists
                        (fun ((other : Types.trait_reference), _) ->
                          Path.equal other.trait bound.trait)
                        methods) ->
                methods @ [ (bound, method_) ]
            | _ -> methods)
          []
          (Properties.known_bounds state.database ~bounds:(bounds state) (Types.Parameter parameter))
      in
      match (without_self, versions state type_ member.text) with
      | [ (trait, method_) ], _ ->
          trait_method_through_type state env ?expected value type_ trait method_ arguments
      | (_ :: _ :: _ as several), _ -> ambiguous (List.map fst several)
      | [], Error traits -> ambiguous traits
      | [], Ok versions -> (
          match List.assoc_opt wanted versions with
          | Some (Trait_version (trait, method_)) ->
              trait_method_through_type state env ?expected value type_ trait method_ arguments
          | Some (Own_version _) -> bug "a generic parameter has a method of its own"
          | None when versions <> [] -> wrong_receiver ()
          | None ->
              error state Unknown_member member.span
                (Printf.sprintf "`%s` has no method `%s`." parameter.name member.text)))
  | Types.Error _ | Types.Hole -> arguments_alone state env arguments type_
  | _ ->
      arguments_alone state env arguments
        (error state Unknown_member member.span
           (Printf.sprintf "`%s` has no method `%s`." (show state type_) member.text))

(* A static trait method called on a type, which is [Self]: a constructor
   such as [Int64.from(count)] or [Self.empty()]. The trait's type arguments
   are inferred from the call's arguments, never from the expected type. *)
and trait_method_through_type state env ?expected:_ ?trait_arguments (value : expression) self_type
    (trait : Types.trait_reference) (method_ : Types.trait_method) arguments =
  let trait_generics =
    match Query.demand state.database Environment.trait_interface trait.trait with
    | Some interface -> interface.trait_generics
    | None -> []
  in
  (* The trait's type arguments as written, as in
     [From[UInt32].from(count)], or fresh inference variables that the
     call's arguments determine. *)
  let trait_arguments =
    match trait_arguments with
    | Some written when List.length written = List.length trait_generics -> written
    | Some written ->
        report state Arity value.span
          (Printf.sprintf "`%s` takes %d type %s, and %d %s given." (Types.show_trait trait)
             (List.length trait_generics)
             (if List.length trait_generics = 1 then "argument" else "arguments")
             (List.length written)
             (if List.length written = 1 then "is" else "are"));
        List.map (fun (_ : Types.generic) -> Types.Type (fresh state)) trait_generics
    | None -> List.map (fun (_ : Types.generic) -> Types.Type (fresh state)) trait_generics
  in
  let extra =
    (({ owner = trait.trait; name = "Self" } : Types.parameter), Types.Type self_type)
    :: Option.value ~default:[] (Types.substitution_of trait_generics trait_arguments)
  in
  let instance = instantiate state value.span ~extra method_.method_signature in
  let parameters = instance.signature.parameters in
  let receiver_argument, receiver_offset, parameters, arguments =
    match instance.signature.receiver with
    | Some (receiver, receiver_type) -> (
        match arguments with
        | first :: rest ->
            let mode : Types.mode = match receiver with Mut -> Mut | Own -> Own | _ -> Read in
            let parameter : Types.parameter_info =
              { name = "self"; mode; type_ = receiver_type; has_default = false }
            in
            let mode = check_argument state env first.value parameter in
            ignore (default_literal state ~at:value.span self_type);
            ( [ { Tables.expression = first.value.id; parameter_index = 0; mode; mark = None } ],
              1,
              parameters,
              rest )
        | [] -> ([], 1, parameters, []))
    | None -> ([], 0, parameters, arguments)
  in
  let matched, left_out = match_arguments state value parameters arguments ~record:false in
  let checked =
    receiver_argument @ check_arguments state env parameters matched ~offset:receiver_offset
  in
  let reference = { trait with trait_arguments } in
  let result = Types.result_type instance.signature.output in
  note_lending state value instance.signature.output;
  let own_arguments =
    List.filteri
      (fun index _ -> index < List.length method_.method_signature.generics)
      instance.type_arguments
  in
  state.tables.calls.(value.id) <-
    Some
      {
        callee =
          Trait_method
            {
              trait = reference;
              name = method_.method_name;
              receiver = method_.method_receiver;
              self_type;
              type_arguments = own_arguments;
              evidence = Built_in;
            };
        arguments = checked;
        omitted_defaults = left_out;
        uses = instance.signature.uses;
        callee_result = result;
      };
  Form.register_call state value;
  resolve_evidence state value self_type reference;
  normalize state result

(* [Ordered.compare(first, second)]: a trait method called in full form,
   with its receiver as the first argument. *)
and trait_call_in_full state env (value : expression) trait ~trait_arguments (member : name)
    arguments =
  (* The static method, or the version that the receiver's mark selects, as
     in a call with a dot. *)
  let wanted : Path.receiver =
    match arguments with receiver :: _ -> marked_receiver receiver.value | [] -> Read
  in
  let version = Members.trait_method state.database trait member.text in
  match match version Static with None -> version wanted | trait_method -> trait_method with
  | Some method_ ->
      (* [Self] is the receiver's type. Checking the receiver as the first
         argument infers it. *)
      trait_method_through_type state env ?trait_arguments value (fresh state)
        (trait_reference trait) method_ arguments
  | None when Members.trait_methods state.database trait member.text <> [] ->
      arguments_alone state env arguments
        (error state Wrong_receiver member.span
           (Printf.sprintf
              "`%s` has no version for this receiver's mark; mark the receiver `mut` or `own` as \
               its versions take."
              member.text))
  | None ->
      error state Unknown_member member.span
        (Printf.sprintf "`%s` has no method `%s`." (Path.show trait) member.text)

(* [Clock.now()]: a call to a capability's method. *)
and capability_call state env (value : expression) capability (member : name) arguments =
  match Members.trait_method state.database capability member.text Static with
  | Some method_ ->
      let instance = instantiate state value.span method_.method_signature in
      let matched, left_out =
        match_arguments state value instance.signature.parameters arguments ~record:false
      in
      let checked = check_arguments state env instance.signature.parameters matched ~offset:0 in
      let result = Types.result_type instance.signature.output in
      state.tables.calls.(value.id) <-
        Some
          {
            callee = Capability_method { capability; name = member.text };
            arguments = checked;
            omitted_defaults = left_out;
            uses = Types.capability_set [ Types.Capability capability ];
            callee_result = result;
          };
      Form.register_call state value;
      result
  | None ->
      arguments_alone state env arguments
        (error state Unknown_member member.span
           (Printf.sprintf "`%s` has no method `%s`." (Path.show capability) member.text))

(* [receiver.name(...)]: a method of the receiver's type, or a trait method. *)
and method_call state env ?expected (value : expression) (base : expression) (member : name)
    ~type_arguments arguments =
  let receiver_type =
    default_literal state ~at:value.span (normalize state (expression state env base))
  in
  let marked = List.mem_assoc value.id state.receiver_modes in
  (* A part that is lent [mut] takes no mark of its own to call a [mut self]
     method: the mark is on the place that lends it. *)
  let lent_mode = if marked then None else lent state base in
  let wanted : Path.receiver =
    match (List.assoc_opt value.id state.receiver_modes, lent_mode) with
    | Some Mut, _ | None, Some Mut -> Mut
    | Some Own, _ -> Own
    | _ -> Read
  in
  let place = is_place state base || Option.is_some lent_mode in
  let choose versions =
    (* Without a mark, the call selects the read-only version. On a
       temporary it selects the [own] version if there is one. A [Plain]
       place can be copied for an [own] version. *)
    match List.assoc_opt wanted versions with
    | Some method_path -> Some (wanted, method_path)
    | None when lent_mode = Some Types.Mut && List.mem_assoc Path.Read versions ->
        Some (Path.Read, List.assoc Path.Read versions)
    | None when (not marked) && ((not place) || plain state receiver_type) -> (
        match List.assoc_opt Path.Own versions with
        | Some method_path -> Some (Path.Own, method_path)
        | None -> None)
    | None -> None
  in
  let choose_temporary versions =
    let chosen =
      if (not marked) && not place then
        match List.assoc_opt Path.Own versions with
        | Some method_path -> Some (Path.Own, method_path)
        | None -> choose versions
      else choose versions
    in
    (* A [mut self] method mutates its receiver, so every index expression
       in the receiver must use the [mut self] version of [at]. *)
    (match chosen with Some (Path.Mut, _) -> mutate state env ~by:Mut_mark base | _ -> ());
    chosen
  in
  let wrong_receiver versions =
    error state Wrong_receiver member.span
      (Printf.sprintf "`%s` has no version that takes %s here; it has %s." member.text
         (Path.show_receiver wanted)
         (String.concat ", " (List.map (fun (receiver, _) -> Path.show_receiver receiver) versions)))
  in
  (* A place that calls a method with only a [mut] or an [own] version lacks
     its mark. The fix adds the mark. *)
  let missing_receiver_mark : 'a. (Path.receiver * 'a) list -> Types.ty =
   fun versions ->
    let has receiver = List.exists (fun (version, _) -> version = receiver) versions in
    if (not marked) && place && (has Path.Mut || has Path.Own) then begin
      let mark = if has Path.Mut then "mut" else "own" in
      error state Missing_mark base.span
        ~fixes:[ fix (Printf.sprintf "Mark it `%s`." mark) [ insert base.span.start (mark ^ " ") ] ]
        (Printf.sprintf "`%s` takes `%s self`, so the call marks its receiver `%s`." member.text
           mark mark)
    end
    else wrong_receiver (List.map (fun (receiver, _) -> (receiver, ())) versions)
  in
  match receiver_type with
  | Types.Error _ | Types.Hole ->
      List.iter
        (fun (argument : argument) -> ignore (expression state env argument.value))
        arguments;
      receiver_type
  | _ -> (
      match versions state receiver_type member.text with
      | Ok [] ->
          let candidates =
            match receiver_type with
            | Types.Named { path; arguments } -> (
                match Members.fields state.database path arguments with
                | Some fields -> List.map (fun (field : Types.field) -> field.field_name) fields
                | None -> [])
            | _ -> []
          in
          let broken =
            match receiver_type with
            | Types.Named { path; _ } -> Members.broken state.database path
            | _ -> None
          in
          arguments_alone state env arguments
            (match broken with
            | Some report -> Types.Error report
            | None ->
                error state Unknown_member member.span
                  ~fixes:
                    (match Diagnostic.closest member.text candidates with
                    | Some candidate ->
                        [
                          fix
                            (Printf.sprintf "Write `%s`." candidate)
                            [ replace member.span candidate ];
                        ]
                    | None -> [])
                  (Printf.sprintf "`%s` has no method `%s`." (show state receiver_type) member.text))
      | Ok versions -> (
          match choose_temporary versions with
          | None -> missing_receiver_mark versions
          | Some (_, Own_version method_path) ->
              method_with_receiver state env ?expected ~type_arguments value ~receiver:base
                ~receiver_type method_path arguments
          | Some (_, Trait_version (trait, method_)) ->
              trait_method_call state env value ~receiver:base ~receiver_type trait method_
                ~type_arguments arguments)
      | Error traits ->
          (* The call in full form: the receiver first, then the arguments
             as written. *)
          let receiver_text = source state base.span in
          let arguments_text =
            List.map
              (fun (argument : argument) ->
                let start =
                  match argument.label with
                  | Some label -> label.span.start
                  | None -> argument.value.span.start
                in
                source state (Span.make start argument.value.span.stop))
              arguments
          in
          error state Ambiguous_method member.span
            ~fixes:
              (List.map
                 (fun (trait : Types.trait_reference) ->
                   let name =
                     match trait.trait with Top { name; _ } -> name | path -> Path.show path
                   in
                   fix
                     (Printf.sprintf "Call `%s`'s `%s`." name member.text)
                     [
                       replace value.span
                         (Printf.sprintf "%s.%s(%s)" name member.text
                            (String.concat ", " (receiver_text :: arguments_text)));
                     ])
                 traits)
            (Printf.sprintf
               "More than one trait gives `%s` a method `%s`. Write the call in full to say which."
               (show state receiver_type) member.text))

and method_with_receiver state env ?expected ?(type_arguments = []) (value : expression)
    ~(receiver : expression) ~receiver_type method_path arguments =
  match function_signature state method_path with
  | None -> bug "the method `%s` has no signature" (Path.show method_path)
  | Some (Error report) -> arguments_alone state env arguments (Types.Error report)
  | Some (Ok signature) ->
      let instance = instantiate state value.span signature in
      explicit_type_arguments
        ~head:
          (match receiver_type with
          | Types.Named { arguments; _ } -> List.length arguments
          | _ -> 0)
        state value instance type_arguments;
      (match instance.signature.receiver with
      | Some (_, self_type) ->
          if not (unify state self_type receiver_type) then
            mismatch state receiver.span ~expected:self_type ~actual:receiver_type
      | None -> ());
      (match (expected, instance.signature.output) with
      | Some expected, Returns output -> unify_as_hint state output expected
      | _ -> ());
      let matched, left_out =
        match_arguments state value instance.signature.parameters arguments ~record:false
      in
      let checked = check_arguments state env instance.signature.parameters matched ~offset:1 in
      let receiver_argument =
        {
          Tables.expression = receiver.id;
          parameter_index = 0;
          mode =
            (match signature.receiver with
            | Some (Mut, _) -> Mut
            | Some (Own, _) -> Own
            | _ -> Read);
          mark = None;
        }
      in
      check_specification_call state env value signature;
      finish_call state value
        (Tables.Function { path = method_path; type_arguments = instance.type_arguments })
        instance (receiver_argument :: checked) left_out

and trait_method_call state env (value : expression) ~(receiver : expression) ~receiver_type
    (trait : Types.trait_reference) (method_ : Types.trait_method) ~type_arguments arguments =
  let trait_generics =
    match Query.demand state.database Environment.trait_interface trait.trait with
    | Some interface -> interface.trait_generics
    | None -> []
  in
  let trait_arguments =
    if List.length trait.trait_arguments = List.length trait_generics then trait.trait_arguments
    else List.map (fun (_ : Types.generic) -> Types.Type (fresh state)) trait_generics
  in
  let extra =
    (({ owner = trait.trait; name = "Self" } : Types.parameter), Types.Type receiver_type)
    :: Option.value ~default:[] (Types.substitution_of trait_generics trait_arguments)
  in
  (match receiver_type with
  | Types.Any _ -> (
      match Impls.through_any ~trait:trait.trait method_ with
      | Callable -> ()
      | Has_generics ->
          report state Not_callable value.span
            (Printf.sprintf
               "`%s` has generic parameters of its own, so it cannot be called through `%s`: an \
                `any` value holds one version of each method, and this one has a version for each \
                set of arguments. Call it on a value whose type is known."
               method_.method_name (show state receiver_type))
      | Names_self ->
          report state Not_callable value.span
            (Printf.sprintf
               "`%s` takes or returns a type that names `Self`, which is the type `%s` hides, so \
                it cannot be called through it. Call it on a value whose type is known."
               method_.method_name (show state receiver_type)))
  | _ -> ());
  let instance = instantiate state value.span ~extra method_.method_signature in
  explicit_type_arguments state value instance type_arguments;
  let matched, left_out =
    match_arguments state value instance.signature.parameters arguments ~record:false
  in
  let checked = check_arguments state env instance.signature.parameters matched ~offset:1 in
  let reference = { trait with trait_arguments } in
  let result = Types.result_type instance.signature.output in
  note_lending state value instance.signature.output;
  let receiver_argument =
    {
      Tables.expression = receiver.id;
      parameter_index = 0;
      mode = (match method_.method_receiver with Mut -> Mut | Own -> Own | _ -> Read);
      mark = None;
    }
  in
  let evidence = match receiver_type with Types.Any _ -> Tables.Dynamic | _ -> Tables.Built_in in
  state.tables.calls.(value.id) <-
    Some
      {
        callee =
          Trait_method
            {
              trait = reference;
              name = method_.method_name;
              receiver = method_.method_receiver;
              self_type = receiver_type;
              type_arguments = instance.type_arguments;
              evidence;
            };
        arguments = receiver_argument :: checked;
        omitted_defaults = left_out;
        uses = instance.signature.uses;
        callee_result = result;
      };
  Form.register_call state value;
  (match receiver_type with
  | Types.Any _ -> ()
  | _ -> resolve_evidence state value receiver_type reference);
  normalize state result
