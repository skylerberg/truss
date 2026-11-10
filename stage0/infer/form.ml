(* Builds core form nodes from the tables the type checker records
   ([Checked]). The checker's other modules call these functions when they
   register how the core node of a syntax node is built. *)

open Syntax
module T = Types
module C = Tables
module Impls = Interface.Impls
module Properties = Interface.Properties
open State

let build_expression_by_id state (id : id) : Core.expression =
  match state.form.expression_builders.(id) with
  | Some build -> build ()
  | None -> bug "a call's argument has no core node"

(* The operand for a parameter with the given mode. A [Read] or [Mut]
   parameter borrows a place, so it receives the place itself. In every
   other case the parameter receives a value. *)
let operand (mode : T.mode) (node : Core.expression) : Core.operand =
  match (mode, node.kind) with (Read | Mut), Use place -> Place place | _ -> Value node

let checked_call state (id : id) : C.call =
  match state.tables.calls.(id) with
  | Some call -> call
  | None -> bug "the checker recorded no call for a call node"

let evidence : C.evidence -> Core.evidence = function
  | Impl { impl; arguments } -> Impl { impl; arguments }
  | Bound -> Bound
  | Dynamic -> Dynamic
  | Built_in -> bug "a built-in method has no core evidence"

let callee (callee : C.callee) : Core.callee =
  match callee with
  | Function { path; type_arguments } -> Function { path; type_arguments }
  | Trait_method { trait; name; receiver; self_type; type_arguments; evidence = found } ->
      Trait_method { trait; name; receiver; self_type; type_arguments; evidence = evidence found }
  | Capability_method { capability; name } -> Capability_method { capability; name }
  | Intrinsic { operation; type_arguments } -> Intrinsic { operation; type_arguments }
  | Constructor _ | Function_value | Built_in_operator -> bug "this callee has no core callee"

(* One argument per parameter, in parameter order. A parameter with no
   argument is [Default]. *)
let arguments state (call : C.call) : Core.argument list =
  List.init
    (List.length call.arguments + List.length call.defaults_left_out)
    (fun index ->
      match
        List.find_opt (fun (argument : C.argument) -> argument.parameter = index) call.arguments
      with
      | Some argument ->
          Core.Passed
            {
              mode = argument.mode;
              value = operand argument.mode (build_expression_by_id state argument.expression);
            }
      | None -> Default)

(* [function_value] is the callee expression of an indirect call. *)
let core_call state ~lends ?function_value (call : C.call) : Core.call =
  {
    callee =
      (match (call.callee, function_value) with
      | Function_value, Some function_value -> Indirect (operand Read function_value)
      | direct, _ -> callee direct);
    arguments = arguments state call;
    lends;
    uses = call.uses;
  }

(* The operator traits, each with its method and the built-in operation
   that the method is for a built-in number type. *)
let arithmetic_traits : (string * string * Intrinsic.operation) list =
  [
    ("Add", "add", Add);
    ("Subtract", "subtract", Subtract);
    ("Multiply", "multiply", Multiply);
    ("Divide", "divide", Divide);
    ("Remainder", "remainder", Remainder);
    ("Negate", "negate", Negate);
  ]

let is_number type_ = T.is_integer_type type_ || T.is_float_type type_

(* Whether values of the type are compared with built-in equality. *)
let is_built_in_scalar type_ =
  is_number type_ || T.is_builtin Bool type_ || T.is_builtin Character type_

(* The built-in operation that a trait method call is, if the receiver is a
   built-in number: [left.add(right)] is [Add], the same as [left + right]. *)
let built_in_operation (trait : T.trait_reference) name self_type =
  if
    is_number self_type
    && List.for_all (fun argument -> argument = T.Type self_type) trait.trait_arguments
  then
    List.find_map
      (fun (trait_name, method_, operation) ->
        if method_ = name && Path.equal trait.trait (core trait_name) then Some operation else None)
      arithmetic_traits
  else None

(* The call's argument expressions, in parameter order. *)
let argument_expressions state (call : C.call) =
  List.map
    (fun (argument : C.argument) -> build_expression_by_id state argument.expression)
    (List.sort
       (fun (left : C.argument) (right : C.argument) -> compare left.parameter right.parameter)
       call.arguments)

(* The fields of a record type, or of one variant of a sum type, in
   declaration order. *)
let constructor_fields state type_ variant type_arguments =
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
  | None -> bug "`%s` is constructed but has no fields" (Path.show type_)

(* The core node for a call expression. Most calls become a [Call]. A call
   of a lending method becomes a [Use] of the [Lent] place. A constructor
   becomes a [Construct]. A call of a built-in method becomes a [Copy], a
   [Cursor_next], an [Operator], or a [Compare].

   [lends] overrides the mode the checker recorded for a lending call.
   [function_value] is the callee expression of an indirect call. *)
let kind_of_call ?lends ?function_value state (value : expression) : Core.kind =
  let recorded = checked_call state value.id in
  let lends = match lends with Some lends -> Some lends | None -> state.tables.lends.(value.id) in
  match recorded.callee with
  | Trait_method { trait; evidence = Built_in; _ }
    when Path.equal trait.trait Properties.copyable_trait -> (
      match recorded.arguments with
      | [ receiver ] -> Copy (operand Read (build_expression_by_id state receiver.expression))
      | _ -> bug "`copy` does not have exactly one argument")
  (* The [next] of a yielding method's cursor is the method's own code. The
     trait's other methods on such a cursor are calls like any other, of
     the bodies that the trait gives them. *)
  | Trait_method { name = "next"; evidence = Impl { impl; _ }; _ }
    when Option.is_some (Impls.cursor_of_impl impl) -> (
      match recorded.arguments with
      | [ receiver ] -> Cursor_next (place_of (build_expression_by_id state receiver.expression))
      | _ -> bug "`next` does not have exactly one argument")
  | Trait_method { trait; name; self_type; _ }
    when Option.is_some (built_in_operation trait name self_type) ->
      Operator
        {
          operation = Option.get (built_in_operation trait name self_type);
          arguments = argument_expressions state recorded;
        }
  | Trait_method { trait; name = "equal"; self_type; _ }
    when is_built_in_scalar self_type && Path.equal trait.trait (core "Equal") -> (
      match argument_expressions state recorded with
      | [ left; right ] -> Compare { comparison = Equal; left; right }
      | _ -> bug "`equal` does not have exactly two arguments")
  | Constructor { type_; variant; type_arguments } ->
      Construct
        {
          variant;
          fields =
            List.mapi
              (fun index (field : T.field) ->
                ( field.field_name,
                  Option.map
                    (fun (argument : C.argument) ->
                      operand argument.mode (build_expression_by_id state argument.expression))
                    (List.find_opt
                       (fun (argument : C.argument) -> argument.parameter = index)
                       recorded.arguments) ))
              (constructor_fields state type_ variant type_arguments);
        }
  | Built_in_operator -> bug "an operator is recorded as a call"
  | Function_value | Function _ | Trait_method _ | Capability_method _ | Intrinsic _ -> (
      let function_value = Option.map (build_expression state) function_value in
      let call = Core.Call (core_call state ~lends ?function_value recorded) in
      match lends with
      | Some _ -> Use (Lent (synthetic_expression state ~origin:value.id recorded.result call))
      | None -> call)

let register_call ?function_value state (value : expression) =
  register_expression state value (fun () -> kind_of_call ?function_value state value)

(* An index expression is a call of [Index.at], which lends. It lends
   mutably if the checker chose the [mut self] version of [at]. *)
let register_index state (value : expression) =
  register_expression state value (fun () ->
      match (checked_call state value.id).callee with
      | Trait_method { receiver = Mut; _ } -> kind_of_call ~lends:Mut state value
      | _ -> kind_of_call ~lends:Read state value)

(* The node for a numeric literal, with the value the checker computed for
   the literal's inferred type. *)
let numeric_literal state (id : id) : Core.kind =
  match state.tables.literals.(id) with
  | Some (Integer_value number) -> Integer number
  | Some (Float_value number) -> Float number
  | None -> bug "a literal has no value"

let type_of state (value : expression) =
  match state.tables.types.(value.id) with
  | Some type_ -> type_
  | None -> bug "`%s` has a core node but no recorded type" (source state value.span)

(* A named function or method used as a value, with its inferred type
   arguments. *)
let function_value state (value : expression) : Core.kind =
  match state.tables.meanings.(value.id) with
  | Some (Global { path; type_arguments }) -> Function_value { path; type_arguments }
  | _ -> bug "`%s` is not recorded as a function" (source state value.span)

(* A variant constructor used as a value. A variant without fields is the
   constructed value. A variant with fields is a lambda that takes the
   fields and constructs the variant. *)
let variant_value state (value : expression) type_path variant : Core.kind =
  match type_of state value with
  | T.Function { output = Returns (T.Named { arguments; _ } as variant_type); _ } ->
      let fields =
        List.map
          (fun (field : T.field) -> (field, fresh_synthetic_local state))
          (constructor_fields state type_path (Some variant) arguments)
      in
      Lambda
        {
          parameters =
            List.map
              (fun ((field : T.field), local) : Core.pattern ->
                {
                  id = fresh_node_id state;
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
                  (synthetic_expression state ~origin:value.id variant_type
                     (Construct
                        {
                          variant = Some variant;
                          fields =
                            List.map
                              (fun ((field : T.field), local) ->
                                ( field.field_name,
                                  Some
                                    (Core.Value
                                       (synthetic_expression state ~origin:value.id field.field_type
                                          (Core.Use
                                             (Local
                                                {
                                                  local;
                                                  type_ = field.field_type;
                                                  origin = value.id;
                                                })))) ))
                              fields;
                        }));
              diverges = false;
            };
          result = variant_type;
        }
  | _ -> Construct { variant = Some variant; fields = [] }

let local_type state (id : id) =
  match state.tables.local_types.(id) with
  | Some type_ -> type_
  | None -> bug "a local has no recorded type"

(* The place of a parameter or a pattern binding, by the id of the name
   that declares it. [origin] is the expression that names it. *)
let named_local state ~origin (id : id) : Core.place =
  Local { local = Named id; type_ = local_type state id; origin }

(* A use of a parameter or a pattern binding. A local whose type is a hole
   is never bound, so a use of it is a [Todo]. *)
let local_use state ~origin (id : id) : Core.kind =
  if was_hole state (fun tables -> tables.local_types) id then Todo
  else Use (named_local state ~origin id)

let self_type state (env : env) =
  match env.self with
  | Some type_ -> final state type_
  | None -> bug "`self` is used outside a method"

(* The place of [self]. *)
let self_local state (env : env) ~origin : Core.place =
  Local { local = Self; type_ = self_type state env; origin }

(* The place of a constant's static data. *)
let constant_place state ~origin (path : Path.t) : Core.place =
  match Query.demand state.database Environment.constant_type path with
  | Some type_ -> Constant { path; type_; origin }
  | None -> bug "the constant `%s` has no type" (Path.show path)

(* A range expression used as a value: a [Construct] of the [Range]
   record. *)
let range_record state (value : expression) start stop ~inclusive : Core.kind =
  match (start, stop, type_of state value) with
  | Some start, Some stop, T.Named { path; arguments } ->
      let start = build_expression state start in
      let stop = build_expression state stop in
      let inclusive = synthetic_expression state ~origin:value.id T.bool (Core.Boolean inclusive) in
      Construct
        {
          variant = None;
          fields =
            List.map2
              (fun (field : T.field) given -> (field.field_name, Some (Core.Value given)))
              (constructor_fields state path None arguments)
              [ start; stop; inclusive ];
        }
  | _ -> bug "a range without both bounds is valid only inside a slice"

(* The capabilities that a type implements, each with its [impl] and the
   [impl]'s interface. An [impl] is declared in the package of its type or
   of its capability. The search covers the type's package, the current
   package, and the standard library. *)
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

(* A [provide] block. Each implementation is a place or a value, with the
   capabilities that its type implements. *)
let provide state (implementations : expression list) (body : block) : Core.kind =
  let implementations =
    List.map
      (fun (implementation : expression) : Core.implementation ->
        let mode : T.mode = match implementation.kind with Mode (Mut, _) -> Mut | _ -> Read in
        let node = build_expression state implementation in
        {
          origin = implementation.id;
          mode;
          value = operand mode node;
          type_ = node.type_;
          provides = List.map fst (capability_impls state node.type_);
        })
      implementations
  in
  Provide { implementations; body = build_block state body }

(* Strings *)

let text_path name : Path.t = standard [ "text" ] name

let builder_method name receiver : Core.callee =
  Function
    { path = Method { owner = text_path "TextBuilder"; name; receiver }; type_arguments = [] }

let checked_template state (literal : string_literal) =
  match state.tables.templates.(literal.id) with
  | Some template -> template
  | None -> bug "the checker recorded no template for a string literal"

(* An untagged string literal: a [String] if it has no interpolation, and
   an [Interpolated] if it has. *)
let untagged_string state (literal : string_literal) : Core.kind =
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
                 let value = operand Read (build_expression state part) in
                 match conversion with
                 | Some call ->
                     Core.Displayed { value; display = callee call.callee } :: piece after
                 | None -> bug "an interpolated value has no `display`")
               rest (checked_template state literal).part_conversions)
      in
      Interpolated
        {
          pieces;
          builder_new = builder_method "new" Static;
          builder_write = builder_method "write" Mut;
          builder_finish = builder_method "finish" Own;
        }

(* A list literal, desugared to a block: allocate storage with capacity for
   the elements, push each element, and convert the storage to a list with
   [List.from_storage]. *)
let list_literal state ~origin (element : T.ty) (elements : Core.expression list) : Core.kind =
  let make = synthetic_expression state ~origin in
  let statement kind : Core.statement = { id = fresh_node_id state; origin; kind } in
  let storage_type =
    T.Named { path = Intrinsic.builtin_path Storage; arguments = [ T.Type element ] }
  in
  let storage = fresh_synthetic_local state in
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
  let capacity = make (T.builtin USize) (Integer (Z.of_int (List.length elements))) in
  let let_storage =
    statement
      (Let
         {
           pattern =
             {
               id = fresh_node_id state;
               origin;
               type_ = storage_type;
               kind = Bind { local = storage; name = "storage"; mutable_ = true; mode = Own };
             };
           value =
             Value
               (intrinsic Storage_with_capacity storage_type
                  [ Passed { mode = Read; value = Value capacity } ]);
           else_ = None;
         })
  in
  let pushes =
    List.map
      (fun element ->
        statement
          (Evaluate
             (intrinsic Storage_push T.unit
                [
                  Passed
                    {
                      mode = Mut;
                      value = Place (Local { local = storage; type_ = storage_type; origin });
                    };
                  Passed { mode = Own; value = Value element };
                ])))
      elements
  in
  Block
    {
      statements = let_storage :: pushes;
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
                      Passed
                        {
                          mode = Own;
                          value =
                            Value
                              (make storage_type
                                 (Use (Local { local = storage; type_ = storage_type; origin })));
                        };
                    ];
                  lends = None;
                  uses = [];
                }));
      diverges = false;
    }

(* A tagged string, desugared to a call of the tag type's [from_template]
   with a [Template] record. The record holds the literal text segments and
   the interpolated values, each converted to the tag's [Part] type. *)
let tagged_string state (value : expression) (literal : string_literal) ~(part : T.ty) : Core.kind =
  let recorded = checked_template state literal in
  let from_template =
    match recorded.from_template with
    | Some call -> call
    | None -> bug "a tagged string has no `from_template`"
  in
  let make = synthetic_expression state ~origin:value.id in
  let record path arguments given =
    Core.Construct
      {
        variant = None;
        fields =
          List.map2
            (fun (field : T.field) given -> (field.field_name, Some (Core.Value given)))
            (constructor_fields state path None arguments)
            given;
      }
  in
  let list element elements =
    make (T.named list_path [ element ]) (list_literal state ~origin:value.id element elements)
  in
  let literal_type = T.named (text_path "Literal") [] in
  let texts =
    List.map
      (fun (written : Syntax.text) ->
        make literal_type
          (record (text_path "Literal") []
             [ make (T.named string_slice_path []) (String written.value) ]))
      (literal.first :: List.map snd literal.rest)
  in
  let parts =
    List.map2
      (fun ((written : expression), _) (conversion : C.call option) ->
        match conversion with
        | Some call ->
            synthetic_expression state ~origin:written.id call.result
              (Call (core_call state ~lends:None call))
        | None -> build_expression state written)
      literal.rest recorded.part_conversions
  in
  let texts = list literal_type texts in
  let template =
    make
      (T.named (text_path "Template") [ part ])
      (record (text_path "Template") [ T.Type part ] [ texts; list part parts ])
  in
  Template
    {
      literals =
        List.map
          (fun (written : Syntax.text) -> written.value)
          (literal.first :: List.map snd literal.rest);
      call =
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
  | None -> bug "a pattern has no recorded type"

(* A pattern that compares the scrutinee with a value: a [Literal] for a
   type with built-in equality, and an [Equal_to] that calls the type's
   [Equal.equal] for any other type. *)
let equal_to_pattern state ~origin type_ (value : Core.kind) : Core.pattern_kind =
  let value = synthetic_expression state ~origin type_ value in
  if is_built_in_scalar type_ then Literal value
  else
    let equal = trait_reference (core "Equal") in
    match implements state type_ equal with
    | Some found ->
        Equal_to
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
    | None ->
        bug "a pattern compares values of `%s`, which does not implement `Equal`" (T.show type_)

(* A constant used as a pattern, or as a bound of a range pattern. *)
let pattern_constant state (id : id) : Core.kind =
  match state.tables.patterns.(id) with
  | Some (Constant_pattern path) -> Use (constant_place state ~origin:id path)
  | _ -> bug "a pattern names a constant that was not recorded"

(* A literal used as a pattern, or as a bound of a range pattern. *)
let pattern_literal state (id : id) (written : Syntax.literal) : Core.kind =
  match (written, state.tables.literals.(id)) with
  | _, Some (Integer_value number) -> Integer number
  | Literal_true, _ -> Boolean true
  | Literal_false, _ -> Boolean false
  | Literal_string text, _ -> String text.first.value
  | Literal_integer _, _ -> bug "an integer pattern has no value"

(* The fields a pattern matches, in declaration order. *)
let pattern_fields state (fields : T.field list) (matched : (string * pattern) list) =
  List.filter_map
    (fun (field : T.field) ->
      Option.map
        (fun written -> (field.field_name, build_pattern state written))
        (List.assoc_opt field.field_name matched))
    fields

(* Operators *)

(* Converts a built-in integer to [Integer]. An expression of any other
   type is returned unchanged. *)
let to_integer state (node : Core.expression) : Core.expression =
  if node.type_ = T.Integer || not (T.is_integer_type node.type_) then node
  else
    synthetic_expression state ~origin:node.origin T.Integer
      (Convert { conversion = To_integer; value = node })

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
      bug "this operator is not an arithmetic operation"

(* An arithmetic operator on built-in types. If the result type is
   [Integer], which happens only in a specification, built-in integer
   operands are converted to [Integer]. *)
let operator state (value : expression) operation (operands : expression list) : Core.kind =
  let arguments = List.map (build_expression state) operands in
  Operator
    {
      operation;
      arguments =
        (if type_of state value = T.Integer then List.map (to_integer state) arguments
         else arguments);
    }

let comparison_of : binary -> Core.comparison = function
  | Equal -> Equal
  | Not_equal -> Not_equal
  | Less -> Less
  | Less_equal -> Less_equal
  | Greater -> Greater
  | Greater_equal -> Greater_equal
  | _ -> bug "this operator is not a comparison"

(* A comparison of two values of the same built-in type. In a
   specification the operands can be integers of different types; both are
   then converted to [Integer]. *)
let built_in_comparison state operator (left : expression) (right : expression) : Core.kind =
  let left = build_expression state left in
  let right = build_expression state right in
  let left, right =
    if T.equal left.type_ right.type_ then (left, right)
    else (to_integer state left, to_integer state right)
  in
  Compare { comparison = comparison_of operator; left; right }

(* A comparison that the checker resolved to a trait method. [==] is a
   call of [equal], and [!=] is its negation. An ordering operator is a
   call of [compare] followed by a test of the resulting [Ordering]:
   [left < right] is [compare(left, right) is Less]. *)
let comparison state (value : expression) operator (left : expression) (right : expression) :
    Core.kind =
  let recorded = checked_call state value.id in
  match recorded.callee with
  | Trait_method { self_type; _ } when is_built_in_scalar self_type ->
      built_in_comparison state operator left right
  | _ -> (
      let call =
        synthetic_expression state ~origin:value.id recorded.result
          (Call (core_call state ~lends:None recorded))
      in
      let is variant : Core.kind =
        Matches
          {
            value = Value call;
            pattern =
              {
                id = fresh_node_id state;
                origin = value.id;
                type_ = recorded.result;
                kind = Variant { variant; fields = [] };
              };
          }
      in
      let not_ kind : Core.kind = Not (synthetic_expression state ~origin:value.id T.bool kind) in
      match operator with
      | Equal -> call.kind
      | Not_equal -> Not call
      | Less -> is "Less"
      | Less_equal -> not_ (is "Greater")
      | Greater -> is "Greater"
      | Greater_equal -> not_ (is "Less")
      | _ -> bug "this operator is not a comparison")

(* Whether a condition can be evaluated at run time. It cannot if it
   contains a quantifier, a value of type [Integer], a specification-only
   expression such as [old] or [result], or a call of a specification-only
   function. *)
let is_executable state (condition : Core.expression) =
  let executable = ref true in
  let specification_only (callee : Core.callee) =
    match callee with
    | Function { path; _ } -> (
        match function_signature state path with
        | Some (Ok signature) -> signature.specification_only
        | _ -> false)
    | Trait_method { trait; name; receiver; _ } ->
        List.exists
          (fun (method_ : T.trait_method) ->
            method_.method_receiver = receiver && method_.method_signature.specification_only)
          (Members.trait_methods state.database trait.trait name)
    | Capability_method _ | Intrinsic _ | Indirect _ -> false
  in
  Core_walk.expression
    {
      Core_walk.ignore_all with
      expression =
        (fun (node : Core.expression) ->
          if node.type_ = T.Integer then executable := false;
          match node.kind with
          | Quantified _ | Result | Old _ | Yielded | Finished | Identical _
          | Specification_function _ | Method_time _
          | Convert { conversion = To_integer | From_integer; _ } ->
              executable := false
          | Call { callee; _ } -> if specification_only callee then executable := false
          | _ -> ());
    }
    condition;
  !executable

(* A compound assignment. Its [value] computes the new value from
   [Current_target] (the target's value before the assignment) and the
   right-hand side. If the operator is a trait method, the checker recorded
   the call under the statement's id. *)
let compound_assign state (written : statement) (target : expression) (value : expression) operator
    : Core.statement_kind =
  let place = place_of (build_expression state target) in
  let target_type = type_of state target in
  let current = synthetic_expression state ~origin:written.id target_type Core.Current_target in
  let right = build_expression state value in
  let kind : Core.kind =
    match state.tables.calls.(written.id) with
    | Some ({ callee = Trait_method { trait; name; self_type; _ }; _ } as recorded) -> (
        match built_in_operation trait name self_type with
        | Some operation -> Operator { operation; arguments = [ current; right ] }
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
                    Passed { mode = mode 0; value = Value current };
                    Passed { mode = mode 1; value = operand (mode 1) right };
                  ];
                lends = None;
                uses = recorded.uses;
              })
    | Some _ -> bug "a compound assignment's call is not a trait method call"
    | None -> Operator { operation = operation_of operator; arguments = [ current; right ] }
  in
  Compound_assign
    { target = place; value = synthetic_expression state ~origin:written.id target_type kind }

(* The cursor type that a call of a yielding method returns. *)
let cursor_type (call : C.call) : T.ty =
  match call.callee with
  | Function { path; type_arguments } -> T.Cursor { method_ = path; arguments = type_arguments }
  | Trait_method { trait; name; receiver; type_arguments; _ } ->
      T.Cursor
        { method_ = Method { owner = trait.trait; name; receiver }; arguments = type_arguments }
  | _ -> bug "a loop iterates over a call that cannot yield"

(* What a [for] loop iterates over. *)
(* The call of a value's [each] that a loop over the value makes. *)
let each_of state (call : C.call) (mode : T.mode) (iterable : expression) : Core.expression =
  let receiver = build_expression state iterable in
  synthetic_expression state ~origin:iterable.id (cursor_type call)
    (Call
       {
         callee = callee call.callee;
         arguments = [ Passed { mode; value = operand mode receiver } ];
         lends = None;
         uses = call.uses;
       })

let iteration state (written : statement) (iterable : expression) : Core.iteration =
  match (state.tables.loops.(written.id), iterable.kind) with
  | Some (Integer_range { inclusive; _ }), Range { start = Some start; stop = Some stop; _ } ->
      let start = build_expression state start in
      Integer_range { start; stop = build_expression state stop; inclusive }
  | Some (Yielding { call; mode }), _ -> (
      match (State.called iterable, type_of state iterable) with
      (* The iterable is itself a call of a yielding method, which makes a
         cursor: the loop iterates over that call. *)
      | Some written_call, T.Cursor _ -> Yielding_call (build_expression state written_call)
      | _ ->
          (* The iterable is a value, even if a call computes it: the loop
             calls the value's [each]. *)
          Yielding_call (each_of state call mode iterable))
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
            | None ->
                bug "a loop iterates over `%s`, which does not implement `Cursor`" (T.show cursor))
      in
      Cursor { cursor = place_of (build_expression state iterable); next }
  | _ -> bug "the checker recorded no iteration for a `for` loop"

(* The resource a cost clause counts, with the names in [calls(...)]
   resolved. *)
let resource state (written : Syntax.resource) : Core.resource =
  let capability (path : path_type) =
    match State.target state path.path.last with
    | Some (Definition (Capability, capability)) -> capability
    | _ -> bug "`calls` names something that is not a capability"
  in
  match written with
  | Time -> Time
  | Allocations -> Allocations
  | Allocated_bytes -> Allocated_bytes
  | Calls (Call_parameter name) -> (
      match State.target state name with
      | Some (Local id) -> Calls (Function_parameter (Named id))
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
      | Big_o value -> Order_of (build_expression state value)
      | At_most value -> At_most (build_expression state value)
      | Exactly value -> Exactly (build_expression state value));
  }

let loop_clause state (clause : loop_clause) : Core.loop_clause =
  match clause.kind with
  | Invariant value -> Invariant (build_expression state value)
  | Loop_decreases measures -> Decreases (List.map (build_expression state) measures)
  | Loop_cost written -> Cost (cost state ~origin:clause.id written)

(* An early exit. It is wrapped in a [Leaving] node if it terminates tasks. *)
let early_exit (tasks : Core.task list) state ~origin (exit : Core.kind) : Core.kind =
  match tasks with
  | [] -> exit
  | _ -> Leaving { tasks; exit = synthetic_expression state ~origin T.Never exit }

(* [inner?], desugared to a match. The first variant of the operand's type
   is the success variant: its arm evaluates to the variant's field. The
   second is the failure variant: its arm returns the failure variant of
   the function's result type, with the same fields. *)
let try_ state (value : expression) (inner : expression) ~(output : T.ty) ~(leaves : Core.task list)
    : Core.kind =
  let scrutinee = build_expression state inner in
  let variants (type_ : T.ty) =
    match type_ with
    | T.Named { path; arguments } -> (
        match Members.variants state.database path arguments with
        | Some [ success; failure ] -> (success, failure)
        | _ -> bug "`?` on `%s`" (T.show type_))
    | _ -> bug "`?` on `%s`" (T.show type_)
  in
  let success, failure = variants scrutinee.type_ in
  let _, returned_failure = variants output in
  let make = synthetic_expression state ~origin:value.id in
  (* A pattern that binds every field of [variant] to a synthetic local,
     and an expression that reads each of those locals. *)
  let bind_fields (variant : T.variant) : Core.pattern * (string * Core.expression) list =
    let fields =
      List.map
        (fun (field : T.field) -> (field, fresh_synthetic_local state))
        (Option.value ~default:[] variant.fields)
    in
    ( {
        id = fresh_node_id state;
        origin = value.id;
        type_ = scrutinee.type_;
        kind =
          Variant
            {
              variant = variant.variant_name;
              fields =
                List.map
                  (fun ((field : T.field), local) : (string * Core.pattern) ->
                    ( field.field_name,
                      {
                        id = fresh_node_id state;
                        origin = value.id;
                        type_ = field.field_type;
                        kind = Bind { local; name = field.field_name; mutable_ = false; mode = Own };
                      } ))
                  fields;
            };
      },
      List.map
        (fun ((field : T.field), local) ->
          ( field.field_name,
            make field.field_type
              (Core.Use (Local { local; type_ = field.field_type; origin = value.id })) ))
        fields )
  in
  let success_pattern, success_fields = bind_fields success in
  let failure_pattern, failure_fields = bind_fields failure in
  let arm patterns body : Core.arm = { patterns; guard = None; body; origin = value.id } in
  Match
    {
      scrutinees = [ Value scrutinee ];
      arms =
        [
          arm [ success_pattern ]
            {
              statements = [];
              value = (match success_fields with [ (_, field) ] -> Some field | _ -> None);
              diverges = false;
            };
          arm [ failure_pattern ]
            {
              statements = [];
              value =
                Some
                  (make T.Never
                     (early_exit leaves state ~origin:value.id
                        (Return
                           (Some
                              (make output
                                 (Construct
                                    {
                                      variant = Some returned_failure.variant_name;
                                      fields =
                                        List.map2
                                          (fun (field : T.field) (_, field_value) ->
                                            (field.field_name, Some (Core.Value field_value)))
                                          (Option.value ~default:[] returned_failure.fields)
                                          failure_fields;
                                    }))))));
              diverges = true;
            };
        ];
      guards_exhaustive = false;
    }

(* A slice expression, [base[start..stop]]. The node holds the call of the
   base type's [slice_range] that creates the view, with the bounds
   computed: a missing start is [0], a missing stop is the length of the
   base, and an inclusive stop is [stop + 1]. *)
let slice state (value : expression) (base : Core.place) ~start ~stop ~inclusive : Core.kind =
  let origin = value.id in
  let make = synthetic_expression state ~origin in
  let usize = T.builtin USize in
  let path, type_arguments =
    match Core_walk.place_type base with
    | T.Named { path; arguments } -> (path, arguments)
    | type_ -> bug "a slice of `%s`" (T.show type_)
  in
  let call name (arguments : Core.argument list) result =
    make result
      (Call
         {
           callee =
             Function { path = Method { owner = path; name; receiver = Read }; type_arguments };
           arguments;
           lends = None;
           uses = [];
         })
  in
  let receiver : Core.argument = Passed { mode = Read; value = Place base } in
  let start = match start with Some start -> start | None -> make usize (Integer Z.zero) in
  let stop =
    match stop with
    | Some stop when inclusive ->
        make usize (Operator { operation = Add; arguments = [ stop; make usize (Integer Z.one) ] })
    | Some stop -> stop
    | None -> call "length" [ receiver ] usize
  in
  Slice
    {
      base;
      call =
        call "slice_range"
          [
            receiver;
            Passed { mode = Read; value = Value start };
            Passed { mode = Read; value = Value stop };
          ]
          (type_of state value);
    }

(* A set or a map literal, desugared to a block: create the collection
   with capacity for the entries, insert each entry, and evaluate to the
   collection. [entries] holds the arguments of each insertion. A literal
   with no entries is the call that creates the collection. *)
let inserted_literal state ~origin (type_ : T.ty) ~name ~insert
    (entries : Core.expression list list) : Core.kind =
  let path, type_arguments =
    match type_ with
    | T.Named { path; arguments } -> (path, arguments)
    | _ -> bug "a set or map literal of type `%s`" (T.show type_)
  in
  let make = synthetic_expression state ~origin in
  let statement kind : Core.statement = { id = fresh_node_id state; origin; kind } in
  let call name receiver arguments result =
    make result
      (Call
         {
           callee = Function { path = Method { owner = path; name; receiver }; type_arguments };
           arguments;
           lends = None;
           uses = [];
         })
  in
  let capacity = make (T.builtin USize) (Integer (Z.of_int (List.length entries))) in
  let created =
    call "with_capacity" Static [ Passed { mode = Read; value = Value capacity } ] type_
  in
  match entries with
  | [] -> created.kind
  | _ ->
      let local = fresh_synthetic_local state in
      let collection : Core.place = Local { local; type_; origin } in
      let bind =
        statement
          (Let
             {
               pattern =
                 {
                   id = fresh_node_id state;
                   origin;
                   type_;
                   kind = Bind { local; name; mutable_ = true; mode = Own };
                 };
               value = Value created;
               else_ = None;
             })
      in
      let inserts =
        List.map
          (fun entry ->
            statement
              (Evaluate
                 (call insert Mut
                    (Passed { mode = Mut; value = Place collection }
                    :: List.map
                         (fun argument : Core.argument ->
                           Passed { mode = Own; value = Value argument })
                         entry)
                    T.unit)))
          entries
      in
      Block
        {
          statements = bind :: inserts;
          value = Some (make type_ (Use collection));
          diverges = false;
        }

(* A list, set, or array literal, or a specification's sequence or set.
   A list or a set literal is desugared to calls. *)
let collection_literal state (value : expression) (elements : Core.expression list) : Core.kind =
  match type_of state value with
  | T.Named { path; arguments = [ T.Type element ] } when Path.equal path list_path ->
      list_literal state ~origin:value.id element elements
  | T.Named { path; _ } as type_ when Path.equal path set_path ->
      inserted_literal state ~origin:value.id type_ ~name:"set" ~insert:"insert"
        (List.map (fun element -> [ element ]) elements)
  | T.Named { path; _ } when Intrinsic.builtin_of_path path = Some Array ->
      Collection_literal { elements; construction = Array }
  | T.Named { path; _ } when Path.equal path sequence_path || Path.equal path finite_set_path ->
      Collection_literal { elements; construction = Specification_only }
  | type_ -> bug "a collection literal of type `%s`" (T.show type_)

(* A map literal. A [Map] literal is desugared to calls of [insert_absent],
   which requires that the key is not in the map yet, so the prover checks
   that the keys of the literal are distinct. *)
let map_literal state (value : expression) (entries : (Core.expression * Core.expression) list) :
    Core.kind =
  match type_of state value with
  | T.Named { path; _ } as type_ when Path.equal path map_path ->
      inserted_literal state ~origin:value.id type_ ~name:"map" ~insert:"insert_absent"
        (List.map (fun (key, entry) -> [ key; entry ]) entries)
  | T.Named { path; _ } when Path.equal path finite_map_path -> Map_literal { entries }
  | type_ -> bug "a map literal of type `%s`" (T.show type_)
