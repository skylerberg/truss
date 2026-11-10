(* The core form's nodes for what checking records of a call: its callee,
   its arguments in the callee's order, and the nodes a call turns out to
   be. *)

open Syntax
module T = Types
module C = Checked
module Impls = Interface.Impls
module Properties = Interface.Properties
open State

let node state (id : id) : Core.expression =
  match state.form.expressions.(id) with
  | Some build -> build ()
  | None -> bug "an expression of a call has no node in the core form"

(* What a parameter is given: a place where it only borrows one, and a value
   otherwise. *)
let operand (mode : T.mode) (node : Core.expression) : Core.operand =
  match (mode, node.kind) with (Read | Mut), Use place -> Place place | _ -> Value node

let recorded state (id : id) : C.call =
  match state.tables.calls.(id) with
  | Some call -> call
  | None -> bug "a call of the core form was not recorded"

let evidence : C.evidence -> Core.evidence = function
  | Impl { impl; arguments } -> Impl { impl; arguments }
  | Bound -> Bound
  | Dynamic -> Dynamic
  | Built_in -> bug "a method the compiler implements is called as another is"

let callee (callee : C.callee) : Core.callee =
  match callee with
  | Function { path; type_arguments } -> Function { path; type_arguments }
  | Trait_method { trait; name; receiver; self_type; type_arguments; evidence = found } ->
      Trait_method { trait; name; receiver; self_type; type_arguments; evidence = evidence found }
  | Capability_method { capability; name } -> Capability_method { capability; name }
  | Intrinsic { operation; type_arguments } -> Intrinsic { operation; type_arguments }
  | Constructor _ | Function_value | Built_in_operator ->
      bug "what is called is not something the core form calls"

(* One argument for each parameter, in the callee's order: the parameters
   that nothing was passed for take their defaults. *)
let arguments state (call : C.call) : Core.argument list =
  List.init
    (List.length call.arguments + List.length call.defaults_left_out)
    (fun index ->
      match
        List.find_opt (fun (argument : C.argument) -> argument.parameter = index) call.arguments
      with
      | Some argument ->
          Core.Passed
            { mode = argument.mode; value = operand argument.mode (node state argument.expression) }
      | None -> Default)

let call_of state ~lends ?through (call : C.call) : Core.call =
  {
    callee =
      (match (call.callee, through) with
      | Function_value, Some function_ -> Through (operand Read function_)
      | found, _ -> callee found);
    arguments = arguments state call;
    lends;
    uses = call.uses;
  }

let call state (id : id) : Core.call =
  call_of state ~lends:state.tables.lends.(id) (recorded state id)

(* The traits whose methods on a built-in number are the operation itself. *)
let arithmetic : (string * string * Intrinsic.operation) list =
  [
    ("Add", "add", Add);
    ("Subtract", "subtract", Subtract);
    ("Multiply", "multiply", Multiply);
    ("Divide", "divide", Divide);
    ("Remainder", "remainder", Remainder);
    ("Negate", "negate", Negate);
  ]

let number type_ = T.is_integer_type type_ || T.is_float_type type_
let built_in_value type_ = number type_ || T.is_builtin Bool type_ || T.is_builtin Character type_

(* The operation a trait's method is on a built-in number: [left + right]
   and [left.add(right)] alike. *)
let operation (trait : T.trait_reference) name self_type =
  if
    number self_type
    && List.for_all (fun argument -> argument = T.Type self_type) trait.trait_arguments
  then
    List.find_map
      (fun (trait_name, method_, operation) ->
        if method_ = name && Path.equal trait.trait (core trait_name) then Some operation else None)
      arithmetic
  else None

let values state (call : C.call) =
  List.map
    (fun (argument : C.argument) -> node state argument.expression)
    (List.sort
       (fun (left : C.argument) (right : C.argument) -> compare left.parameter right.parameter)
       call.arguments)

(* The fields of the record or the variant a constructor builds, in the
   order they are declared. *)
let constructed state type_ variant type_arguments =
  let fields =
    match variant with
    | None -> Members.fields state.database type_ type_arguments
    | Some variant ->
        Option.bind (Members.variants state.database type_ type_arguments) (fun variants ->
            Option.bind
              (List.find_opt (fun (written : T.variant) -> written.variant_name = variant) variants)
              (fun (written : T.variant) -> written.fields))
  in
  match fields with
  | Some fields -> fields
  | None -> bug "`%s` is built and has no fields" (Path.show type_)

(* What a recorded call is as a node: a call, the part a lending call
   lends, a value built, or an operation that needs no call. *)
let call_kind ?lends ?through state (value : expression) : Core.kind =
  let recorded = recorded state value.id in
  let lends = match lends with Some lends -> Some lends | None -> state.tables.lends.(value.id) in
  match recorded.callee with
  | Trait_method { trait; evidence = Built_in; _ }
    when Path.equal trait.trait Properties.copyable_trait -> (
      match recorded.arguments with
      | [ receiver ] -> Copy (operand Read (node state receiver.expression))
      | _ -> bug "a copy of other than one value")
  | Trait_method { trait; evidence = Built_in; _ } when Path.equal trait.trait Impls.cursor_trait
    -> (
      match recorded.arguments with
      | [ receiver ] -> Next (place_of (node state receiver.expression))
      | _ -> bug "a cursor is pulled with arguments")
  | Trait_method { trait; name; self_type; _ } when Option.is_some (operation trait name self_type)
    ->
      Operator
        {
          operation = Option.get (operation trait name self_type);
          arguments = values state recorded;
        }
  | Trait_method { trait; name = "equal"; self_type; _ }
    when built_in_value self_type && Path.equal trait.trait (core "Equal") -> (
      match values state recorded with
      | [ left; right ] -> Compare { comparison = Equal; left; right }
      | _ -> bug "`equal` of other than two values")
  | Constructor { type_; variant; type_arguments } ->
      Construct
        {
          variant;
          fields =
            List.mapi
              (fun index (field : T.field) ->
                ( field.field_name,
                  Option.map
                    (fun (argument : C.argument) -> node state argument.expression)
                    (List.find_opt
                       (fun (argument : C.argument) -> argument.parameter = index)
                       recorded.arguments) ))
              (constructed state type_ variant type_arguments);
        }
  | Built_in_operator -> bug "an operator is recorded as a call"
  | Function_value | Function _ | Trait_method _ | Capability_method _ | Intrinsic _ -> (
      let through = Option.map (built state) through in
      let made = Core.Call (call_of state ~lends ?through recorded) in
      match lends with
      | Some _ -> Use (Lent (make state ~origin:value.id recorded.result made))
      | None -> made)

let draft_call ?through state (value : expression) =
  draft state value (fun () -> call_kind ?through state value)

(* An index is the part its [at] lends, read-only or to change, as the
   version of [at] that was chosen takes [self]. *)
let draft_index state (value : expression) =
  draft state value (fun () ->
      match (recorded state value.id).callee with
      | Trait_method { receiver = Mut; _ } -> call_kind ~lends:Mut state value
      | _ -> call_kind ~lends:Read state value)

(* A literal's node, with the value its type settled. *)
let literal state (id : id) : Core.kind =
  match state.tables.literals.(id) with
  | Some (Integer_value number) -> Integer number
  | Some (Float_value number) -> Float number
  | None -> bug "a literal has no value"

let type_of state (value : expression) =
  match state.tables.types.(value.id) with
  | Some type_ -> type_
  | None -> bug "`%s` has a node and no type" (source state value.span)

(* A named function or method as a value, with the type arguments its use
   settled. *)
let function_value state (value : expression) : Core.kind =
  match state.tables.meanings.(value.id) with
  | Some (Global { path; type_arguments }) -> Function_value { path; type_arguments }
  | _ -> bug "`%s` is not recorded as a function" (source state value.span)

(* A variant named as a value: the value itself when it has no fields, and
   otherwise a function that builds it from them. *)
let variant_value state (value : expression) type_path variant : Core.kind =
  match type_of state value with
  | T.Function { output = Returns (T.Named { arguments; _ } as built); _ } ->
      let fields =
        List.map
          (fun (field : T.field) -> (field, made_local state))
          (constructed state type_path (Some variant) arguments)
      in
      Lambda
        {
          parameters =
            List.map
              (fun ((field : T.field), local) : Core.pattern ->
                {
                  id = next_id state;
                  origin = value.id;
                  type_ = field.field_type;
                  kind = Bind { local; name = field.field_name; mutable_ = false; mode = Own };
                })
              fields;
          captures = [];
          body =
            {
              statements = [];
              value =
                Some
                  (make state ~origin:value.id built
                     (Construct
                        {
                          variant = Some variant;
                          fields =
                            List.map
                              (fun ((field : T.field), local) ->
                                ( field.field_name,
                                  Some
                                    (make state ~origin:value.id field.field_type
                                       (Core.Use (Local local))) ))
                              fields;
                        }));
              ends = true;
            };
          result = built;
        }
  | _ -> Construct { variant = Some variant; fields = [] }

let local_type state (id : id) =
  match state.tables.local_types.(id) with
  | Some type_ -> type_
  | None -> bug "a local of the core form has no type"

(* A range written as a value: the range type's record, built from its
   ends. *)
let range state (value : expression) start stop ~inclusive : Core.kind =
  match (start, stop, type_of state value) with
  | Some start, Some stop, T.Named { path; arguments } ->
      let start = built state start in
      let stop = built state stop in
      let inclusive = make state ~origin:value.id T.bool (Core.Boolean inclusive) in
      Construct
        {
          variant = None;
          fields =
            List.map2
              (fun (field : T.field) given -> (field.field_name, Some given))
              (constructed state path None arguments)
              [ start; stop; inclusive ];
        }
  | _ -> bug "a range with an end left out is a value only where it slices"

(* The capabilities a type implements, each with the [impl] that provides
   it, its generic arguments, and its interface. An [impl] lives with its
   type or its capability, so it is in the type's package, this one, or the
   standard library, where the capabilities a dependency could not see are
   not. *)
let capability_impls (state : state) (type_ : T.ty) =
  match type_ with
  | T.Named { path; _ } ->
      List.filter_map
        (fun (trait, _) ->
          if Interface.Summary.kind_of state.database trait = Some Capability then
            match implements state type_ (trait_reference trait) with
            | Some (Interface.Impls.From_impl { impl; substitution }) ->
                Option.map
                  (fun interface ->
                    ({ Core.capability = trait; impl; arguments = substitution }, interface))
                  (Interface.Impls.impl_interface state.database impl)
            | _ -> None
          else None)
        (List.concat_map
           (fun package -> Interface.Impls.impls_for state.database path package)
           (List.sort_uniq compare [ Path.package path; state.package; "standard" ]))
  | _ -> []

(* What a [provide] gives its body: each implementation, as the place it
   is or the value it makes, with what its type provides. *)
let provide state (implementations : expression list) (body : block) : Core.kind =
  let implementations =
    List.map
      (fun (implementation : expression) : Core.implementation ->
        let mode : T.mode = match implementation.kind with Mode (Mut, _) -> Mut | _ -> Read in
        let given = built state implementation in
        {
          origin = implementation.id;
          mode;
          value = operand mode given;
          type_ = given.type_;
          provides = List.map fst (capability_impls state given.type_);
        })
      implementations
  in
  Provide { implementations; body = built_block state body }

(* Strings *)

let text name : Path.t = standard [ "text" ] name

let builder_method name receiver : Core.callee =
  Function { path = Method { owner = text "TextBuilder"; name; receiver }; type_arguments = [] }

let template_record state (literal : string_literal) =
  match state.tables.templates.(literal.id) with
  | Some recorded -> recorded
  | None -> bug "a string has no record of its parts"

(* A plain string: its text when nothing is interpolated, and otherwise the
   pieces it is written out from. *)
let interpolated state (literal : string_literal) : Core.kind =
  match literal.rest with
  | [] -> String literal.first.value
  | rest ->
      let piece (written : Syntax.text) : Core.piece list =
        if written.value = "" then [] else [ Text written.value ]
      in
      let pieces =
        piece literal.first
        @ List.concat
            (List.map2
               (fun (part, after) (conversion : C.call option) ->
                 let value = operand Read (built state part) in
                 match conversion with
                 | Some call ->
                     Core.Displayed { value; display = callee call.callee } :: piece after
                 | None -> bug "an interpolated value has no `display`")
               rest (template_record state literal).part_conversions)
      in
      Interpolated
        {
          pieces;
          start = builder_method "new" Static;
          write = builder_method "write" Mut;
          finish = builder_method "finish" Own;
        }

(* A list of some elements: a storage with room for them, each pushed onto
   it, made into the list. *)
let list state ~origin (element : T.ty) (elements : Core.expression list) : Core.kind =
  let make = make state ~origin in
  let statement kind : Core.statement = { id = next_id state; origin; kind } in
  let storage_type =
    T.Named { path = Intrinsic.builtin_path Storage; arguments = [ T.Type element ] }
  in
  let storage = made_local state in
  let intrinsic operation type_ arguments =
    make type_
      (Call
         {
           callee = Intrinsic { operation; type_arguments = [ T.Type element ] };
           arguments;
           lends = None;
           uses = [];
         })
  in
  let room = make (T.builtin USize) (Integer (Z.of_int (List.length elements))) in
  let bound =
    statement
      (Let
         {
           pattern =
             {
               id = next_id state;
               origin;
               type_ = storage_type;
               kind = Bind { local = storage; name = "storage"; mutable_ = true; mode = Own };
             };
           value =
             Value
               (intrinsic Storage_with_capacity storage_type
                  [ Passed { mode = Read; value = Value room } ]);
           otherwise = None;
         })
  in
  let pushed =
    List.map
      (fun element ->
        statement
          (Evaluate
             (intrinsic Storage_push T.unit
                [
                  Passed { mode = Mut; value = Place (Local storage) };
                  Passed { mode = Own; value = Value element };
                ])))
      elements
  in
  Block
    {
      statements = bound :: pushed;
      value =
        Some
          (make (T.named list_path [ element ])
             (Call
                {
                  callee =
                    Function
                      {
                        path =
                          Method { owner = list_path; name = "from_storage"; receiver = Static };
                        type_arguments = [ T.Type element ];
                      };
                  arguments =
                    [
                      Passed { mode = Own; value = Value (make storage_type (Use (Local storage))) };
                    ];
                  lends = None;
                  uses = [];
                }));
      ends = true;
    }

(* A tagged string: the tag's [from_template], given the template that
   holds its texts and its parts, each already the tag's part. *)
let template state (value : expression) (literal : string_literal) ~(part : T.ty) : Core.kind =
  let recorded = template_record state literal in
  let from_template =
    match recorded.from_template with
    | Some call -> call
    | None -> bug "a tagged string has no `from_template`"
  in
  let make = make state ~origin:value.id in
  let record path arguments given =
    Core.Construct
      {
        variant = None;
        fields =
          List.map2
            (fun (field : T.field) given -> (field.field_name, Some given))
            (constructed state path None arguments)
            given;
      }
  in
  let list element elements =
    make (T.named list_path [ element ]) (list state ~origin:value.id element elements)
  in
  let literal_type = T.named (text "Literal") [] in
  let texts =
    List.map
      (fun (written : Syntax.text) ->
        make literal_type
          (record (text "Literal") []
             [ make (T.named string_slice_path []) (String written.value) ]))
      (literal.first :: List.map snd literal.rest)
  in
  let parts =
    List.map2
      (fun ((written : expression), _) (conversion : C.call option) ->
        match conversion with
        | Some call ->
            State.make state ~origin:written.id call.result (Call (call_of state ~lends:None call))
        | None -> built state written)
      literal.rest recorded.part_conversions
  in
  let texts = list literal_type texts in
  let template =
    make
      (T.named (text "Template") [ part ])
      (record (text "Template") [ T.Type part ] [ texts; list part parts ])
  in
  Template
    {
      literals =
        List.map
          (fun (written : Syntax.text) -> written.value)
          (literal.first :: List.map snd literal.rest);
      made =
        make from_template.result
          (Call
             {
               callee = callee from_template.callee;
               arguments = [ Passed { mode = Own; value = Value template } ];
               lends = None;
               uses = from_template.uses;
             });
    }

(* Patterns *)

let pattern_type state (id : id) =
  match state.tables.pattern_types.(id) with
  | Some type_ -> type_
  | None -> bug "a pattern of the core form has no type"

(* A value a pattern compares what it matches with: as built-in values, or
   with the type's [Equal], which matching it agrees with. *)
let equals state ~origin type_ (value : Core.kind) : Core.pattern_kind =
  let value = make state ~origin type_ value in
  if built_in_value type_ then Literal value
  else
    let equal = trait_reference (core "Equal") in
    match implements state type_ equal with
    | Some found ->
        Equals
          {
            value;
            equal =
              Trait_method
                {
                  trait = equal;
                  name = "equal";
                  receiver = Read;
                  self_type = type_;
                  type_arguments = [];
                  evidence = evidence (evidence_of found);
                };
          }
    | None -> bug "a pattern compares values of `%s`, which has no `Equal`" (T.show type_)

(* A constant in a pattern, or at an end of a range. *)
let pattern_constant state (id : id) : Core.kind =
  match state.tables.patterns.(id) with
  | Some (Constant_pattern path) -> Constant path
  | _ -> bug "a pattern names a constant that was not recorded"

(* A literal in a pattern, or at an end of a range. *)
let pattern_literal state (id : id) (written : Syntax.literal) : Core.kind =
  match (written, state.tables.literals.(id)) with
  | _, Some (Integer_value number) -> Integer number
  | Literal_true, _ -> Boolean true
  | Literal_false, _ -> Boolean false
  | Literal_string text, _ -> String text.first.value
  | Literal_integer _, _ -> bug "an integer pattern has no value"

(* The fields a pattern looks at, in the order their type declares them. *)
let pattern_fields state (fields : T.field list) (matched : (string * pattern) list) =
  List.filter_map
    (fun (field : T.field) ->
      Option.map
        (fun written -> (field.field_name, built_pattern state written))
        (List.assoc_opt field.field_name matched))
    fields

(* Operators *)

(* A built-in integer where a specification works on [Integer]s. *)
let as_integer state (node : Core.expression) : Core.expression =
  if node.type_ = T.Integer || not (T.is_integer_type node.type_) then node
  else make state ~origin:node.origin T.Integer (Convert { conversion = To_integer; value = node })

let operation_of : binary -> Intrinsic.operation = function
  | Add -> Add
  | Subtract -> Subtract
  | Multiply -> Multiply
  | Divide -> Divide
  | Remainder -> Remainder
  | Bit_and -> Bit_and
  | Bit_or -> Bit_or
  | Bit_xor -> Bit_xor
  | Shift_left -> Shift_left
  | Shift_right -> Shift_right
  | Equal | Not_equal | Less | Less_equal | Greater | Greater_equal | And | Or | Implies ->
      bug "an operator that is no operation"

(* An operator on values of built-in types, or of types a [todo] left
   undecided. Where a specification's arithmetic is on [Integer]s, its
   built-in operands become [Integer]s first. *)
let operator state (value : expression) operation (operands : expression list) : Core.kind =
  let arguments = List.map (built state) operands in
  Operator
    {
      operation;
      arguments =
        (if type_of state value = T.Integer then List.map (as_integer state) arguments
         else arguments);
    }

let comparison_of : binary -> Core.comparison = function
  | Equal -> Equal
  | Not_equal -> Not_equal
  | Less -> Less
  | Less_equal -> Less_equal
  | Greater -> Greater
  | Greater_equal -> Greater_equal
  | _ -> bug "an operator that is no comparison"

(* A comparison with no call: of two values of one built-in type, or in a
   specification of two integers by value, which are then [Integer]s. *)
let compare_values state operator (left : expression) (right : expression) : Core.kind =
  let left = built state left in
  let right = built state right in
  let left, right =
    if T.equal left.type_ right.type_ then (left, right)
    else (as_integer state left, as_integer state right)
  in
  Compare { comparison = comparison_of operator; left; right }

(* A comparison of values that are not built in: [equal], or [compare]
   and a test of the [Ordering] it gives. *)
let comparison state (value : expression) operator (left : expression) (right : expression) :
    Core.kind =
  let recorded = recorded state value.id in
  match recorded.callee with
  | Trait_method { self_type; _ } when built_in_value self_type ->
      compare_values state operator left right
  | _ -> (
      let call =
        make state ~origin:value.id recorded.result (Call (call_of state ~lends:None recorded))
      in
      let is variant : Core.kind =
        Matches
          {
            value = Value call;
            pattern =
              {
                id = next_id state;
                origin = value.id;
                type_ = recorded.result;
                kind = Variant { variant; fields = [] };
              };
          }
      in
      let not_ kind : Core.kind = Not (make state ~origin:value.id T.bool kind) in
      match operator with
      | Equal -> call.kind
      | Not_equal -> Not call
      | Less -> is "Less"
      | Less_equal -> not_ (is "Greater")
      | Greater -> is "Greater"
      | Greater_equal -> not_ (is "Less")
      | _ -> bug "an operator that is no comparison")

(* Whether a condition can be checked when the program runs: nothing in it
   is only for specifications. That is no quantifier, no [Integer], no value
   that only a specification has, and no function for specifications only. *)
let runs state (condition : Core.expression) =
  let runs = ref true in
  let specification_only (called : Core.callee) =
    match called with
    | Function { path; _ } -> (
        match function_signature state path with
        | Some (Ok signature) -> signature.specification_only
        | _ -> false)
    | Trait_method { trait; name; receiver; _ } ->
        List.exists
          (fun (method_ : T.trait_method) ->
            method_.method_receiver = receiver && method_.method_signature.specification_only)
          (Members.trait_methods state.database trait.trait name)
    | Capability_method _ | Intrinsic _ | Through _ -> false
  in
  Core_walk.expression
    {
      Core_walk.nothing with
      expression =
        (fun (node : Core.expression) ->
          if node.type_ = T.Integer then runs := false;
          match node.kind with
          | Quantified _ | Result | Old _ | Yielded | Finished | Identical _ | Measure _
          | Convert { conversion = To_integer | From_integer; _ } ->
              runs := false
          | Call { callee; _ } -> if specification_only callee then runs := false
          | _ -> ());
    }
    condition;
  !runs

(* A compound assignment: what its target takes, in which [Updating] is
   what the target holds before. The operator's call was recorded under the
   statement, with the target as its first argument. *)
let update state (written : statement) (target : expression) (value : expression) operator :
    Core.statement_kind =
  let place = place_of (built state target) in
  let target_type = type_of state target in
  let updating = make state ~origin:written.id target_type Core.Updating in
  let given = built state value in
  let kind : Core.kind =
    match state.tables.calls.(written.id) with
    | Some ({ callee = Trait_method { trait; name; self_type; _ }; _ } as recorded) -> (
        match operation trait name self_type with
        | Some operation -> Operator { operation; arguments = [ updating; given ] }
        | None ->
            let mode index =
              match
                List.find_opt
                  (fun (argument : C.argument) -> argument.parameter = index)
                  recorded.arguments
              with
              | Some argument -> argument.mode
              | None -> T.Read
            in
            Call
              {
                callee = callee recorded.callee;
                arguments =
                  [
                    Passed { mode = mode 0; value = Value updating };
                    Passed { mode = mode 1; value = operand (mode 1) given };
                  ];
                lends = None;
                uses = recorded.uses;
              })
    | Some _ -> bug "a compound assignment calls what is not an operator"
    | None -> Operator { operation = operation_of operator; arguments = [ updating; given ] }
  in
  Update { target = place; value = make state ~origin:written.id target_type kind }

(* The cursor a call of a yielding method makes. *)
let cursor (call : C.call) : T.ty =
  match call.callee with
  | Function { path; type_arguments } -> T.Cursor { method_ = path; arguments = type_arguments }
  | Trait_method { trait; name; receiver; type_arguments; _ } ->
      T.Cursor
        { method_ = Method { owner = trait.trait; name; receiver }; arguments = type_arguments }
  | _ -> bug "a loop goes over a call of what is not a method"

(* What a [for] loop goes over. *)
let drive state (written : statement) (iterable : expression) : Core.drive =
  match (state.tables.loops.(written.id), iterable.kind) with
  | Some (Integer_range { inclusive; _ }), Range { start = Some start; stop = Some stop; _ } ->
      let start = built state start in
      Count { start; stop = built state stop; inclusive }
  | Some (Yielding { call; mode }), _ -> (
      match (State.called iterable, type_of state iterable) with
      (* The iterable is itself a call of a yielding method, which makes a
         cursor: the loop iterates over that call. *)
      | Some written_call, T.Cursor _ -> Each (built state written_call)
      | _ ->
          (* The iterable is a value, even if a call computes it: the loop
             calls the value's [each]. *)
          let receiver = built state iterable in
          Each
            (make state ~origin:iterable.id (cursor call)
               (Call
                  {
                    callee = callee call.callee;
                    arguments = [ Passed { mode; value = operand mode receiver } ];
                    lends = None;
                    uses = call.uses;
                  })))
  | Some (Pulled { cursor }), _ ->
      let next : Core.callee option =
        match cursor with
        | T.Cursor _ -> None
        | _ -> (
            let trait = trait_reference Impls.cursor_trait in
            match implements state cursor trait with
            | Some found ->
                Some
                  (Trait_method
                     {
                       trait;
                       name = "next";
                       receiver = Mut;
                       self_type = cursor;
                       type_arguments = [];
                       evidence = evidence (evidence_of found);
                     })
            | None -> bug "a loop pulls `%s`, which is no cursor" (T.show cursor))
      in
      Pull { cursor = place_of (built state iterable); next }
  | _ -> bug "a `for` loop has no record of what it goes over"

(* What a cost clause counts, with what its [calls] names resolved. *)
let resource state (written : Syntax.resource) : Core.resource =
  let capability (path : path_type) =
    match State.target state path.path.last with
    | Some (Definition (Capability, capability)) -> capability
    | _ -> bug "`calls` names what is not a capability"
  in
  match written with
  | Time -> Time
  | Allocations -> Allocations
  | Allocated_bytes -> Allocated_bytes
  | Calls (Call_parameter name) -> (
      match State.target state name with
      | Some (Local id) -> Calls (Through (Bound id))
      | _ -> bug "`calls(%s)` names no parameter" name.text)
  | Calls (Call_capability path) -> Calls (Capability (capability path))
  | Calls (Call_method (path, method_)) -> Calls (Capability_method (capability path, method_.text))

let cost state ~origin ({ amortized; resource = written; bound } : Syntax.cost) : Core.cost =
  {
    origin;
    amortized;
    resource = resource state written;
    bound =
      (match bound with
      | Finite -> Finite
      | Big_o value -> Order_of (built state value)
      | At_most value -> At_most (built state value)
      | Exactly value -> Exactly (built state value));
  }

let loop_clause state (clause : loop_clause) : Core.loop_clause =
  match clause.kind with
  | Invariant value -> Invariant (built state value)
  | Loop_decreases measures -> Decreases (List.map (built state) measures)
  | Loop_cost written -> Cost (cost state ~origin:clause.id written)

(* [?]: the value when there is one, and otherwise the function returns
   what there is in its place. Which variant holds the value is the first
   the type declares. *)
let try_ state (value : expression) (inner : expression) ~(output : T.ty) : Core.kind =
  let found = built state inner in
  let variants (type_ : T.ty) =
    match type_ with
    | T.Named { path; arguments } -> (
        match Members.variants state.database path arguments with
        | Some [ success; failure ] -> (success, failure)
        | _ -> bug "`?` on `%s`" (T.show type_))
    | _ -> bug "`?` on `%s`" (T.show type_)
  in
  let success, failure = variants found.type_ in
  let _, returned = variants output in
  let make = make state ~origin:value.id in
  let bind (variant : T.variant) : Core.pattern * (string * Core.expression) list =
    let fields =
      List.map
        (fun (field : T.field) -> (field, made_local state))
        (Option.value ~default:[] variant.fields)
    in
    ( {
        id = next_id state;
        origin = value.id;
        type_ = found.type_;
        kind =
          Variant
            {
              variant = variant.variant_name;
              fields =
                List.map
                  (fun ((field : T.field), local) : (string * Core.pattern) ->
                    ( field.field_name,
                      {
                        id = next_id state;
                        origin = value.id;
                        type_ = field.field_type;
                        kind = Bind { local; name = field.field_name; mutable_ = false; mode = Own };
                      } ))
                  fields;
            };
      },
      List.map
        (fun ((field : T.field), local) ->
          (field.field_name, make field.field_type (Core.Use (Local local))))
        fields )
  in
  let success_pattern, given = bind success in
  let failure_pattern, failed = bind failure in
  let arm patterns body : Core.arm = { patterns; guard = None; body; origin = value.id } in
  Match
    {
      scrutinees = [ Value found ];
      arms =
        [
          arm [ success_pattern ]
            {
              statements = [];
              value = (match given with [ (_, given) ] -> Some given | _ -> None);
              ends = true;
            };
          arm [ failure_pattern ]
            {
              statements = [];
              value =
                Some
                  (make T.Never
                     (Return
                        (Some
                           (make output
                              (Construct
                                 {
                                   variant = Some returned.variant_name;
                                   fields =
                                     List.map2
                                       (fun (field : T.field) (_, given) ->
                                         (field.field_name, Some given))
                                       (Option.value ~default:[] returned.fields)
                                       failed;
                                 })))));
              ends = false;
            };
        ];
      guards_cover = false;
    }

(* How a collection literal of a type is built. *)
let collection (type_ : T.ty) : Core.collection =
  match type_ with
  | T.Named { path; _ } when Intrinsic.builtin_of_path path = Some Array -> Array
  | T.Named { path; arguments } when Path.equal path set_path || Path.equal path map_path ->
      let method_ name receiver : Core.callee =
        Function { path = Method { owner = path; name; receiver }; type_arguments = arguments }
      in
      Inserted { empty = method_ "empty" Static; insert = method_ "insert" Mut }
  | T.Named { path; _ }
    when Path.equal path sequence_path || Path.equal path finite_set_path
         || Path.equal path finite_map_path ->
      Modelled
  | _ -> bug "a collection literal of type `%s`" (T.show type_)

(* A collection literal: a list is built from its elements, and any other
   is a node that says how it is built. *)
let collection_literal state (value : expression) (elements : Core.expression list) : Core.kind =
  match type_of state value with
  | T.Named { path; arguments = [ T.Type element ] } when Path.equal path list_path ->
      list state ~origin:value.id element elements
  | type_ -> Collection { elements; built = collection type_ }
