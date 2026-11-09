(* A call: which callee it names, and the calls of types' own methods,
   traits' methods, written in full or through a receiver, and
   capabilities'. See TYPECHECKER.md, "Members" and "Modes at calls". *)

open Syntax
module T = Types
module C = Checked
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Properties = Interface.Properties
module Lower = Interface.Lower
open State
open Hooks
open Lookups
open Pattern_typing
open Calls

let rec call state env ?expected (value : expression) (callee : expression)
    (arguments : argument list) : T.ty =
  match callee.kind with
  | Name { modules = []; last } when target state last = Some Old -> (
      match arguments with
      | [ argument ] -> expression state env ?expected argument.value
      | _ -> T.Error)
  | Name { modules = []; last }
    when match target state last with Some (Cost_function _) -> true | _ -> false ->
      List.iter
        (fun (argument : argument) -> ignore (expression state env argument.value))
        arguments;
      T.Integer
  | Member (base, member) -> (
      match static_ state base with
      | Some (Static_type type_) -> static_call state env ?expected value type_ member arguments
      | Some (Static_trait trait) -> trait_call_in_full state env value trait member arguments
      | Some (Static_capability capability) ->
          capability_call state env value capability member arguments
      | None -> method_call state env ?expected value base member ~type_arguments:[] arguments)
  | Bracket ({ kind = Member (base, member); _ }, items)
    when state.resolved.brackets.(callee.id) = Some Method_bracket ->
      method_call state env ?expected value base member ~type_arguments:items arguments
  | Name path -> (
      match target state path.last with
      | Some (Definition definition_path) -> (
          match Interface.Summary.kind_of state.database definition_path with
          | Some Type -> construct state env ?expected value definition_path None arguments
          | _ -> (
              match function_signature state definition_path with
              | Some signature ->
                  named_call state env ?expected value definition_path signature ~type_arguments:[]
                    arguments
              | None -> function_value_call state env value callee arguments))
      | Some (Variant (type_path, variant)) ->
          construct state env ?expected value type_path (Some variant) arguments
      | _ -> function_value_call state env value callee arguments)
  | Bracket ({ kind = Name path; _ }, items)
    when state.resolved.brackets.(callee.id) = Some Type_arguments -> (
      match target state path.last with
      | Some (Definition definition_path) -> (
          match Interface.Summary.kind_of state.database definition_path with
          | Some Type -> (
              match static_ state callee with
              | Some (Static_type (Named { arguments = type_arguments; _ })) ->
                  construct state env ?expected ~type_arguments value definition_path None arguments
              | _ -> T.Error)
          | _ -> (
              match function_signature state definition_path with
              | Some signature ->
                  named_call state env ?expected value definition_path signature
                    ~type_arguments:items arguments
              | None -> T.Error))
      | _ -> T.Error)
  | _ -> function_value_call state env value callee arguments

(* A call through a function value: by position, with no labels. *)

and static_call state env ?expected (value : expression) type_ (member : name) arguments =
  match type_ with
  | T.Named { path; arguments = type_arguments }
    when member.text.[0] >= 'A' && member.text.[0] <= 'Z' ->
      construct state env ?expected ~type_arguments value path (Some member.text) arguments
  | T.Named { path; _ } -> (
      match Members.own_methods state.database path member.text with
      | [] -> (
          (* A trait method written through the type, as [Int64.from(count)]. *)
          match trait_static_method state path member.text with
          | [ (trait, method_) ] ->
              trait_method_through_type state env ?expected value type_ trait method_ arguments
          | _ :: _ :: _ as several ->
              report state Ambiguous_method member.span
                (Printf.sprintf
                   "More than one trait gives `%s` a method `%s`: %s. Call it through the trait to \
                    say which."
                   (show state type_) member.text
                   (String.concat ", "
                      (List.map
                         (fun ((trait : T.trait_reference), _) -> "`" ^ T.show_trait trait ^ "`")
                         several)));
              List.iter
                (fun (argument : argument) -> ignore (expression state env argument.value))
                arguments;
              T.Error
          | [] ->
              report state Unknown_member member.span
                (Printf.sprintf "`%s` has no method `%s`." (show state type_) member.text);
              List.iter
                (fun (argument : argument) -> ignore (expression state env argument.value))
                arguments;
              T.Error)
      | versions -> (
          let static_version = List.assoc_opt Path.Static versions in
          match static_version with
          | Some method_path -> (
              match function_signature state method_path with
              | Some signature ->
                  let instance = instantiate state ~span:value.span signature in
                  (* The type's arguments, as written or inferred, are the
                     head's generic arguments. *)
                  let head =
                    List.filteri
                      (fun index _ ->
                        index
                        < List.length
                            (match type_ with T.Named { arguments; _ } -> arguments | _ -> []))
                      instance.type_arguments
                  in
                  ignore
                    (Unify.unify_arguments state.unifier head
                       (match type_ with T.Named { arguments; _ } -> arguments | _ -> []));
                  (match (expected, instance.signature.output) with
                  | Some expected, Returns output -> ignore (unify state output expected)
                  | _ -> ());
                  let matched, left_out =
                    match_arguments state value instance.signature.parameters arguments
                      ~record:false
                  in
                  let checked =
                    check_arguments state env instance.signature.parameters matched ~offset:0
                  in
                  check_specification_call state env value signature;
                  finish_call state value
                    (C.Function { path = method_path; type_arguments = instance.type_arguments })
                    instance checked left_out
              | None -> T.Error)
          | None -> (
              (* A method with [self], written in full: the first argument is the receiver. *)
              match arguments with
              | receiver :: rest -> (
                  (* The receiver's mark chooses the version, as with a dot. *)
                  let wanted : Path.receiver =
                    match receiver.value.kind with
                    | Mode (Mut, _) -> Mut
                    | Mode (Own, _) -> Own
                    | _ -> Read
                  in
                  let inner =
                    match receiver.value.kind with Mode (_, inner) -> inner | _ -> receiver.value
                  in
                  let receiver_type = expression state env inner in
                  if inner != receiver.value then record state receiver.value receiver_type;
                  if not (unify state receiver_type type_) then
                    mismatch state inner.span ~expected:type_ ~found:receiver_type;
                  match List.assoc_opt wanted versions with
                  | Some method_path ->
                      let mode : T.mode = match wanted with Mut -> Mut | Own -> Own | _ -> Read in
                      check_mode state receiver.value
                        { name = "self"; mode; type_; has_default = false }
                        receiver_type;
                      method_with_receiver state env ?expected value ~receiver:receiver.value
                        ~receiver_type method_path rest
                  | None ->
                      report state Wrong_receiver member.span
                        (Printf.sprintf
                           "`%s` has no version for this receiver's mark; mark the receiver `mut` \
                            or `own` as its versions take."
                           member.text);
                      T.Error)
              | [] ->
                  report state Missing_argument value.span
                    "A method written in full takes its receiver as its first argument.";
                  T.Error)))
  | T.Parameter parameter -> (
      match
        List.find_map
          (fun (bound : T.trait_reference) ->
            List.find_map
              (fun (method_ : T.trait_method) ->
                if method_.method_name = member.text then Some (bound, method_) else None)
              (Members.trait_methods state.database bound.trait member.text))
          (Properties.known_bounds state.database ~bounds:(bounds state) (T.Parameter parameter))
      with
      | Some (trait, method_) ->
          trait_method_through_type state env ?expected value type_ trait method_ arguments
      | None ->
          report state Unknown_member member.span
            (Printf.sprintf "`%s` has no method `%s`." parameter.name member.text);
          T.Error)
  | _ -> T.Error

(* Whether a type could implement a trait, with fresh arguments for the
   trait's own parameters, which the call's arguments then decide. *)

and trait_method_through_type state env ?expected:_ (value : expression) self_type
    (trait : T.trait_reference) (method_ : T.trait_method) arguments =
  let trait_generics =
    match Query.demand state.database Environment.trait_interface trait.trait with
    | Some interface -> interface.trait_generics
    | None -> []
  in
  let trait_arguments = List.map (fun (_ : T.generic) -> T.Type (fresh state)) trait_generics in
  let extra =
    (({ owner = trait.trait; name = "Self" } : T.parameter), T.Type self_type)
    :: List.combine
         (List.map (fun (generic : T.generic) -> generic.generic) trait_generics)
         trait_arguments
  in
  let instance = instantiate state ~span:value.span ~extra method_.method_signature in
  let parameters = instance.signature.parameters in
  let receiver_argument, receiver_offset, parameters, arguments =
    match instance.signature.receiver with
    | Some (receiver, receiver_type) -> (
        match arguments with
        | first :: rest ->
            let mode : T.mode = match receiver with Mut -> Mut | Own -> Own | _ -> Read in
            let parameter : T.parameter_info =
              { name = "self"; mode; type_ = receiver_type; has_default = false }
            in
            let conversion = argument_value state env first.value parameter in
            ( [ { C.expression = first.value.id; parameter = 0; mode; conversion } ],
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
  let result = output_type instance.signature.output in
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
        defaults_left_out = left_out;
        uses = instance.signature.uses;
        capability_arguments = [];
        result;
      };
  resolve_evidence state value self_type reference;
  normalize state result

(* The [impl] a trait method call means is found once its types are known,
   which may be at the end of the statement. *)

and trait_call_in_full state env (value : expression) trait (member : name) arguments =
  match Members.trait_methods state.database trait member.text with
  | method_ :: _ -> (
      match arguments with
      | _ ->
          (* [Self] is the receiver's type, which checking it as the first
             argument decides. *)
          trait_method_through_type state env value (fresh state) (trait_reference trait) method_
            arguments)
  | [] ->
      report state Unknown_member member.span
        (Printf.sprintf "`%s` has no method `%s`." (Path.show trait) member.text);
      T.Error

(* [Clock.now()]: a call to a capability's method. *)

and capability_call state env (value : expression) capability (member : name) arguments =
  match Members.trait_methods state.database capability member.text with
  | method_ :: _ ->
      let instance = instantiate state method_.method_signature in
      let matched, left_out =
        match_arguments state value instance.signature.parameters arguments ~record:false
      in
      let checked = check_arguments state env instance.signature.parameters matched ~offset:0 in
      let result = output_type instance.signature.output in
      state.tables.calls.(value.id) <-
        Some
          {
            callee = Capability_method { capability; name = member.text };
            arguments = checked;
            defaults_left_out = left_out;
            uses = [ T.Capability capability ];
            capability_arguments = [];
            result;
          };
      result
  | [] ->
      report state Unknown_member member.span
        (Printf.sprintf "`%s` has no method `%s`." (Path.show capability) member.text);
      List.iter
        (fun (argument : argument) -> ignore (expression state env argument.value))
        arguments;
      T.Error

(* [receiver.name(...)]: the type's own method, or a trait's. *)

and method_call state env ?expected (value : expression) (base : expression) (member : name)
    ~type_arguments arguments =
  let receiver_type = normalize state (expression state env base) in
  (* A literal receiver, as in [5.wrapping_add(3)], has its default type. *)
  let receiver_type =
    match resolve state receiver_type with
    | T.Literal (Integer_literal, _) ->
        ignore (unify state receiver_type (T.builtin Int64));
        T.builtin Int64
    | T.Literal (Float_literal, _) ->
        ignore (unify state receiver_type (T.builtin Float64));
        T.builtin Float64
    | _ -> receiver_type
  in
  let wanted : Path.receiver =
    match List.assoc_opt value.id state.receiver_modes with
    | Some Mut -> Mut
    | Some Own -> Own
    | _ -> Read
  in
  let marked = List.mem_assoc value.id state.receiver_modes in
  let place = is_place state base in
  let choose versions =
    (* No mark picks the read-only version; on a temporary, the [own]
       version if there is one; a [Plain] place may give its [own] version a
       copy. *)
    match List.assoc_opt wanted versions with
    | Some found -> Some (wanted, found)
    | None when (not marked) && ((not place) || plain state receiver_type) -> (
        match List.assoc_opt Path.Own versions with
        | Some found -> Some (Path.Own, found)
        | None -> None)
    | None -> None
  in
  let choose_temporary versions =
    if (not marked) && not place then
      match List.assoc_opt Path.Own versions with
      | Some found -> Some (Path.Own, found)
      | None -> choose versions
    else choose versions
  in
  let wrong_receiver versions =
    let shown = function
      | Path.Read -> "`self`"
      | Mut -> "`mut self`"
      | Own -> "`own self`"
      | Static -> "no `self`"
    in
    report state Wrong_receiver member.span
      (Printf.sprintf "`%s` has no version that takes %s here; it has %s." member.text
         (shown wanted)
         (String.concat ", " (List.map (fun (receiver, _) -> shown receiver) versions)))
  in
  (* A place that calls a method with only a [mut] or [own] version is
     missing its mark, which the fix adds. *)
  let missing_receiver_mark : 'a. (Path.receiver * 'a) list -> unit =
   fun versions ->
    let has receiver = List.exists (fun (found, _) -> found = receiver) versions in
    if (not marked) && place && (has Path.Mut || has Path.Own) then begin
      let mark = if has Path.Mut then "mut" else "own" in
      report state Missing_mark base.span
        ~fixes:[ fix (Printf.sprintf "Mark it `%s`." mark) [ insert base.span.start (mark ^ " ") ] ]
        (Printf.sprintf "`%s` takes `%s self`, so the call marks its receiver `%s`." member.text
           mark mark)
    end
    else wrong_receiver (List.map (fun (receiver, _) -> (receiver, ())) versions)
  in
  match receiver_type with
  | T.Error | T.Hole ->
      List.iter
        (fun (argument : argument) -> ignore (expression state env argument.value))
        arguments;
      receiver_type
  | _ -> (
      let own =
        match receiver_type with
        | T.Named { path; _ } ->
            List.filter
              (fun (receiver, _) -> receiver <> Path.Static)
              (Members.own_methods state.database path member.text)
        | _ -> []
      in
      match own with
      | _ :: _ -> (
          match choose_temporary own with
          | Some (_, method_path) ->
              method_with_receiver state env ?expected ~type_arguments value ~receiver:base
                ~receiver_type method_path arguments
          | None ->
              missing_receiver_mark own;
              T.Error)
      | [] -> (
          match trait_candidates state receiver_type member.text with
          | [ (trait, versions) ] -> (
              match
                choose_temporary
                  (List.map
                     (fun (method_ : T.trait_method) -> (method_.method_receiver, method_))
                     versions)
              with
              | Some (_, method_) ->
                  trait_method_call state env value ~receiver:base ~receiver_type trait method_
                    ~type_arguments arguments
              | None ->
                  missing_receiver_mark
                    (List.map
                       (fun (method_ : T.trait_method) -> (method_.method_receiver, ()))
                       versions);
                  T.Error)
          | [] ->
              let candidates =
                match receiver_type with
                | T.Named { path; arguments } -> (
                    match Members.fields state.database path arguments with
                    | Some fields -> List.map (fun (field : T.field) -> field.field_name) fields
                    | None -> [])
                | _ -> []
              in
              report state Unknown_member member.span
                ~fixes:
                  (match Resolve.closest member.text candidates with
                  | Some candidate ->
                      [
                        fix
                          (Printf.sprintf "Write `%s`." candidate)
                          [ replace member.span candidate ];
                      ]
                  | None -> [])
                (Printf.sprintf "`%s` has no method `%s`." (show state receiver_type) member.text);
              List.iter
                (fun (argument : argument) -> ignore (expression state env argument.value))
                arguments;
              T.Error
          | several ->
              (* The call written in full: the receiver first, then the
                 arguments as written. *)
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
              report state Ambiguous_method member.span
                ~fixes:
                  (List.map
                     (fun ((trait : T.trait_reference), _) ->
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
                     several)
                (Printf.sprintf
                   "More than one trait gives `%s` a method `%s`. Write the call in full to say \
                    which."
                   (show state receiver_type) member.text);
              T.Error))

(* The traits that give a type a method with a name. *)

and method_with_receiver state env ?expected ?(type_arguments = []) (value : expression)
    ~(receiver : expression) ~receiver_type method_path arguments =
  match function_signature state method_path with
  | None -> T.Error
  | Some signature ->
      let instance = instantiate state ~span:value.span signature in
      explicit_type_arguments
        ~head:
          (match receiver_type with T.Named { arguments; _ } -> List.length arguments | _ -> 0)
        state value instance type_arguments;
      (match instance.signature.receiver with
      | Some (_, self_type) ->
          if not (unify state self_type receiver_type) then
            mismatch state receiver.span ~expected:self_type ~found:receiver_type
      | None -> ());
      (match (expected, instance.signature.output) with
      | Some expected, Returns output -> ignore (unify state output expected)
      | _ -> ());
      let matched, left_out =
        match_arguments state value instance.signature.parameters arguments ~record:false
      in
      let checked = check_arguments state env instance.signature.parameters matched ~offset:1 in
      let receiver_argument =
        {
          C.expression = receiver.id;
          parameter = 0;
          mode =
            (match signature.receiver with
            | Some (Mut, _) -> Mut
            | Some (Own, _) -> Own
            | _ -> Read);
          conversion = None;
        }
      in
      check_specification_call state env value signature;
      finish_call state value
        (C.Function { path = method_path; type_arguments = instance.type_arguments })
        instance (receiver_argument :: checked) left_out

and trait_method_call state env (value : expression) ~(receiver : expression) ~receiver_type
    (trait : T.trait_reference) (method_ : T.trait_method) ~type_arguments arguments =
  let trait_generics =
    match Query.demand state.database Environment.trait_interface trait.trait with
    | Some interface -> interface.trait_generics
    | None -> []
  in
  let trait_arguments =
    if List.length trait.trait_arguments = List.length trait_generics then trait.trait_arguments
    else List.map (fun (_ : T.generic) -> T.Type (fresh state)) trait_generics
  in
  let extra =
    (({ owner = trait.trait; name = "Self" } : T.parameter), T.Type receiver_type)
    :: List.combine
         (List.map (fun (generic : T.generic) -> generic.generic) trait_generics)
         trait_arguments
  in
  let instance = instantiate state ~span:value.span ~extra method_.method_signature in
  explicit_type_arguments state value instance type_arguments;
  let matched, left_out =
    match_arguments state value instance.signature.parameters arguments ~record:false
  in
  let checked = check_arguments state env instance.signature.parameters matched ~offset:1 in
  let reference = { trait with trait_arguments } in
  let result = output_type instance.signature.output in
  let receiver_argument =
    {
      C.expression = receiver.id;
      parameter = 0;
      mode = (match method_.method_receiver with Mut -> Mut | Own -> Own | _ -> Read);
      conversion = None;
    }
  in
  let evidence = match receiver_type with T.Any _ -> C.Dynamic | _ -> C.Built_in in
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
        defaults_left_out = left_out;
        uses = instance.signature.uses;
        capability_arguments = [];
        result;
      };
  (match receiver_type with
  | T.Any _ -> ()
  | _ -> resolve_evidence state value receiver_type reference);
  match instance.signature.output with
  | Yields _ ->
      T.Cursor
        {
          method_ =
            Method
              {
                owner = trait.trait;
                name = method_.method_name;
                receiver = method_.method_receiver;
              };
          arguments = instance.type_arguments;
        }
  | _ -> normalize state result

(* [?]: a [Result] whose error is the function's, or an [Option] in a
   function that returns one. *)
