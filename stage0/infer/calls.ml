(* Calls: matching arguments to parameters by label and position, with
   defaults, their modes and conversions, and the calls of named functions
   and constructors. See TYPECHECKER.md, "Calls and arguments". *)

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

let rec function_value_call state env (value : expression) (callee : expression) arguments =
  let callee_type = normalize state (expression state env callee) in
  match callee_type with
  | T.Function function_type ->
      if List.length function_type.inputs <> List.length arguments then
        report state Too_many_arguments value.span
          (Printf.sprintf "This function takes %d arguments, and %d are given."
             (List.length function_type.inputs)
             (List.length arguments));
      let pairs =
        List.filteri (fun index _ -> index < List.length function_type.inputs) arguments
      in
      let checked =
        List.mapi
          (fun index (argument : argument) ->
            (match argument.label with
            | Some label ->
                report state Unknown_label label.span
                  ~fixes:
                    [
                      fix "Remove the label."
                        [
                          Diagnostic.delete (Source.span label.span.start argument.value.span.start);
                        ];
                    ]
                  "A call through a function value passes its arguments by position, without \
                   labels."
            | None -> ());
            let mode, input = List.nth function_type.inputs index in
            let parameter : T.parameter_info =
              { name = "the function value"; mode; type_ = input; has_default = false }
            in
            let conversion = argument_value state env argument.value parameter in
            { C.expression = argument.value.id; parameter = index; mode; conversion })
          pairs
      in
      let result = output_type function_type.output in
      state.tables.calls.(value.id) <-
        Some
          {
            callee = Function_value;
            arguments = checked;
            defaults_left_out = [];
            uses = function_type.uses;
            capability_arguments = [];
            result;
          };
      result
  | T.Error | T.Hole ->
      List.iter
        (fun (argument : argument) -> ignore (expression state env argument.value))
        arguments;
      callee_type
  | _ ->
      report state Not_callable callee.span
        (Printf.sprintf "`%s` is not a function, so it cannot be called." (show state callee_type));
      List.iter
        (fun (argument : argument) -> ignore (expression state env argument.value))
        arguments;
      T.Error

(* One argument: checked against its parameter's type, with its mark, and
   with the one implicit conversion, from an owned collection to its view. *)

and argument_value state env (value : expression) (parameter : T.parameter_info) =
  let inner =
    match value.kind with
    | Mode (_, inner) when Option.is_none (marked_call state inner) -> inner
    | _ -> value
  in
  let found = expression state env ~expected:parameter.type_ inner in
  if inner != value then record state value found;
  let expected = normalize state parameter.type_ and found_resolved = normalize state found in
  let to_view =
    (is_named slice_path expected && is_named list_path found_resolved)
    || (is_named string_slice_path expected && is_named string_path found_resolved)
  in
  let conversion : C.conversion option =
    if to_view then begin
      (match (expected, found_resolved) with
      | T.Named { arguments = expected_arguments; _ }, T.Named { arguments = found_arguments; _ } ->
          if not (Unify.unify_arguments state.unifier expected_arguments found_arguments) then
            mismatch state value.span ~expected ~found
      | _ -> ());
      Some Owned_to_view
    end
    else if env.specification && resolve state found = T.Integer && T.is_integer_type expected then begin
      state.obligations <-
        Integer_fits { expression = value.id; type_ = expected } :: state.obligations;
      Some From_integer
    end
    else if
      env.specification && T.is_integer_type found_resolved && resolve state expected = T.Integer
    then Some To_integer
    else begin
      coerce state inner ~found ~expected;
      match (resolve state found, expected, found_resolved) with
      | T.Never, _, _ -> Some From_never
      | _, T.Function expected_function, T.Function found_function
        when expected_function.uses <> found_function.uses
             || expected_function.costs <> found_function.costs ->
          Some Function_widening
      | _ -> None
    end
  in
  check_mode state value parameter found;
  conversion

(* Matches arguments to parameters: a label, a bare name that matches a
   parameter, or the first argument, in that order; then the arguments
   must come in the order of the parameters. *)

and match_arguments state (value : expression) (parameters : T.parameter_info list)
    (arguments : argument list) ~record =
  let named =
    List.mapi (fun index (parameter : T.parameter_info) -> (parameter.name, index)) parameters
  in
  let bare_name (argument : argument) =
    let rec name_of (expression : expression) =
      match expression.kind with
      | Name { modules = []; last } -> Some last.text
      | Mode (_, inner) -> name_of inner
      | _ -> None
    in
    name_of argument.value
  in
  let assigned = Hashtbl.create 8 in
  let matched =
    List.mapi
      (fun position (argument : argument) ->
        let found =
          match argument.label with
          | Some label -> (
              match List.assoc_opt label.text named with
              | Some index -> Some index
              | None ->
                  report state Unknown_label label.span
                    ~fixes:
                      (match Resolve.closest label.text (List.map fst named) with
                      | Some candidate ->
                          [
                            fix
                              (Printf.sprintf "Write `%s`." candidate)
                              [ replace label.span candidate ];
                          ]
                      | None -> [])
                    (Printf.sprintf "No parameter is named `%s`." label.text);
                  None)
          | None -> (
              match Option.bind (bare_name argument) (fun name -> List.assoc_opt name named) with
              | Some index -> Some index
              | None ->
                  if position = 0 && (not record) && parameters <> [] then Some 0
                  else if record && List.length parameters = 1 && List.length arguments = 1 then
                    Some 0
                  else begin
                    (* The label is known only when one parameter is left for
                       the one argument without one. *)
                    let claimed =
                      List.concat
                        (List.mapi
                           (fun position (other : argument) ->
                             match other.label with
                             | Some label -> Option.to_list (List.assoc_opt label.text named)
                             | None -> (
                                 match
                                   Option.bind (bare_name other) (fun name ->
                                       List.assoc_opt name named)
                                 with
                                 | Some index -> [ index ]
                                 | None -> if position = 0 && not record then [ 0 ] else []))
                           arguments)
                    in
                    let unlabeled =
                      List.length
                        (List.filteri
                           (fun position (other : argument) ->
                             other.label = None
                             && Option.is_none
                                  (Option.bind (bare_name other) (fun name ->
                                       List.assoc_opt name named))
                             && (position > 0 || record))
                           arguments)
                    in
                    let open_parameters =
                      List.filter (fun (_, index) -> not (List.mem index claimed)) named
                    in
                    let fixes =
                      match (open_parameters, unlabeled) with
                      | [ (label, _) ], 1 ->
                          [
                            fix
                              (Printf.sprintf "Label it `%s`." label)
                              [ insert argument.value.span.start (label ^ ": ") ];
                          ]
                      | _ -> []
                    in
                    report state Missing_label argument.value.span ~fixes
                      (if record then
                         "Every field after the first needs a label or a variable of its name, \
                          since fields have no order."
                       else
                         "Every argument after the first needs a label, or a variable with its \
                          parameter's name.");
                    None
                  end)
        in
        (match found with
        | Some index ->
            if Hashtbl.mem assigned index then begin
              report state Repeated_argument argument.value.span
                (Printf.sprintf "`%s` is given more than once." (List.nth parameters index).name)
            end
            else Hashtbl.replace assigned index ()
        | None -> ());
        (argument, found))
      arguments
  in
  (* Arguments come in the order of the parameters, except a record's. *)
  (if not record then
     let indexes = List.filter_map snd matched in
     let sorted = List.sort compare indexes in
     if indexes <> sorted && List.length matched = List.length indexes then
       match (arguments, List.rev arguments) with
       | first :: _, last :: _ ->
           let ordered =
             List.map fst
               (List.sort
                  (fun (_, left) (_, right) -> compare left right)
                  (List.map (fun (argument, index) -> (argument, Option.get index)) matched))
           in
           let written (argument : argument) =
             let start =
               match argument.label with
               | Some label -> label.span.start
               | None -> argument.value.span.start
             in
             source state (Span.make start argument.value.span.stop)
           in
           let start =
             match first.label with
             | Some label -> label.span.start
             | None -> first.value.span.start
           in
           report state Out_of_order value.span
             ~fixes:
               [
                 fix "Put the arguments in the order of the parameters."
                   [
                     replace
                       (Span.make start last.value.span.stop)
                       (String.concat ", " (List.map written ordered));
                   ];
               ]
             "The arguments must come in the order of the parameters."
       | _ -> ());
  let missing =
    List.filter
      (fun (_, index) ->
        (not (Hashtbl.mem assigned index)) && not (List.nth parameters index).has_default)
      named
  in
  (* When an argument went to no parameter, which one was meant is not
     known, so the parameters left open are not reported too. *)
  if List.for_all (fun (_, found) -> Option.is_some found) matched then
    List.iter
      (fun (name, _) ->
        report state Missing_argument value.span
          (Printf.sprintf "`%s` is not given, and has no default." name))
      missing;
  let left_out =
    List.filter_map
      (fun (name, index) ->
        if (not (Hashtbl.mem assigned index)) && (List.nth parameters index).has_default then
          Some name
        else None)
      named
  in
  ( List.filter_map
      (fun (argument, found) -> Option.map (fun index -> (argument, index)) found)
      matched,
    left_out )

(* Checks matched arguments: every argument that is not a lambda first, in
   order, then each lambda, whose parameters then have their types. *)

and check_arguments state env (parameters : T.parameter_info list) matched ~offset =
  let is_lambda ((argument : argument), _) =
    match argument.value.kind with Lambda _ -> true | _ -> false
  in
  let check ((argument : argument), index) =
    let parameter = List.nth parameters index in
    let conversion = argument_value state env argument.value parameter in
    {
      C.expression = argument.value.id;
      parameter = index + offset;
      mode = parameter.mode;
      conversion;
    }
  in
  let first = List.map check (List.filter (fun pair -> not (is_lambda pair)) matched) in
  let lambdas = List.map check (List.filter is_lambda matched) in
  let order = List.map (fun ((argument : argument), _) -> argument.value.id) matched in
  List.filter_map
    (fun id ->
      List.find_opt (fun (checked : C.argument) -> checked.expression = id) (first @ lambdas))
    order

and named_call state env ?expected (value : expression) path (signature : T.signature)
    ~type_arguments arguments =
  let instance = instantiate state ~span:value.span signature in
  explicit_type_arguments state value instance type_arguments;
  (match (expected, instance.signature.output) with
  | Some expected, Returns output -> ignore (unify state output expected)
  | _ -> ());
  let matched, left_out =
    match_arguments state value instance.signature.parameters arguments ~record:false
  in
  let checked = check_arguments state env instance.signature.parameters matched ~offset:0 in
  let callee =
    match Intrinsic.operation_of_path path with
    | Some operation -> C.Intrinsic { operation; type_arguments = instance.type_arguments }
    | None -> C.Function { path; type_arguments = instance.type_arguments }
  in
  check_specification_call state env value signature;
  finish_call state value callee instance checked left_out

and construct state env ?expected ?type_arguments (value : expression) type_path variant arguments =
  let type_arguments =
    match type_arguments with Some given -> given | None -> fresh_arguments state type_path
  in
  let type_ = T.Named { path = type_path; arguments = type_arguments } in
  (match expected with Some expected -> ignore (unify state type_ expected) | None -> ());
  let fields =
    match variant with
    | None -> (
        match Members.fields state.database type_path type_arguments with
        | Some fields -> Some fields
        | None ->
            (match Members.shape state.database type_path with
            | Some Error_shape -> ()
            | _ ->
                report state Not_a_record value.span
                  (Printf.sprintf "`%s` is not a record, so it cannot be built this way."
                     (show state type_)));
            None)
    | Some variant -> (
        match Members.variants state.database type_path type_arguments with
        | Some variants -> (
            match
              List.find_opt (fun (written : T.variant) -> written.variant_name = variant) variants
            with
            | Some { fields = Some fields; _ } -> Some fields
            | Some { fields = None; _ } ->
                report state Too_many_arguments value.span
                  (Printf.sprintf "`%s` has no fields." variant);
                None
            | None ->
                report state Unknown_variant value.span
                  (Printf.sprintf "`%s` has no variant `%s`." (show state type_) variant);
                None)
        | None -> None)
  in
  if not (Members.fields_visible state.database ~package:state.package type_path) then
    report state Private_field value.span
      (Printf.sprintf "`%s` is opaque, so only its own package can build it." (show state type_));
  match fields with
  | None ->
      List.iter
        (fun (argument : argument) -> ignore (expression state env argument.value))
        arguments;
      type_
  | Some fields ->
      let parameters =
        List.map
          (fun (field : T.field) ->
            {
              T.name = field.field_name;
              mode = Own;
              type_ = field.field_type;
              has_default = field.field_has_default;
            })
          fields
      in
      let matched, left_out = match_arguments state value parameters arguments ~record:true in
      let checked = check_arguments state env parameters matched ~offset:0 in
      state.tables.calls.(value.id) <-
        Some
          {
            callee = Constructor { type_ = type_path; variant; type_arguments };
            arguments = checked;
            defaults_left_out = left_out;
            uses = [];
            capability_arguments = [];
            result = type_;
          };
      type_

(* [Type.name(...)]: a variant, a method without [self], or a method
   written in full with its receiver first. *)
