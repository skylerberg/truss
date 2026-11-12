(* The tables that the type checker fills while it checks a definition. The
   core form is built from them. All are dense arrays keyed by the syntax
   tree's node ids. Three of them are published, for tools that work on the
   syntax tree. *)

type local = Syntax.id

(* How a trait's [impl] was found, for a call of a trait method. *)
type evidence =
  | Impl of { impl : Path.t; arguments : Types.substitution }  (** A written or derived [impl]. *)
  | Bound
      (** A bound in scope, on a generic parameter or on an associated type of one, resolved when
          the code is instantiated. *)
  | Dynamic  (** Through an [any] value's table. *)
  | Built_in  (** [Copyable] and [Plain], which the compiler implements. *)

type callee =
  | Function of { path : Path.t; type_arguments : Types.argument list }
      (** A named function or a type's own method, with its generic arguments, the type head's
          first. *)
  | Trait_method of {
      trait : Types.trait_reference;
      name : string;
      receiver : Path.receiver;
      self_type : Types.ty;
      type_arguments : Types.argument list;  (** The method's own generic arguments. *)
      evidence : evidence;
    }
  | Capability_method of { capability : Path.t; name : string }
  | Constructor of { type_ : Path.t; variant : string option; type_arguments : Types.argument list }
  | Indirect  (** A call through a function value, by position. *)
  | Intrinsic of { operation : Intrinsic.operation; type_arguments : Types.argument list }
  | Built_in_operator  (** [&&], [||], [!], and the bitwise operators, on built-in types. *)

type argument = {
  expression : Syntax.id;
  mark : Core.mark option;
  parameter_index : int;  (** Counting a method's receiver as 0 and the rest after it. *)
  mode : Types.mode;
}

type call = {
  callee : callee;
  arguments : argument list;  (** In the order written. *)
  omitted_defaults : string list;  (** The parameters with defaults that were not passed. *)
  uses : Types.capability list;  (** The callee's [uses], with capability parameters substituted. *)
  callee_result : Types.ty;
      (** For an operator that tests the result of its call, as [<] tests the [Ordering] of
          [compare], this is not the operator's own type. *)
}

(* What a name, member, or bracket expression resolves to, once types are
   known. *)
type resolution =
  | Local_value of local
  | Global of { path : Path.t; type_arguments : Types.argument list }
      (** A function as a value, or a constant. *)
  | Field_access of { type_ : Types.ty; field : string }
  | Variant_value of { type_ : Types.ty; variant : string }
      (** A variant with no fields, or one used as a function. *)
  | Type_name of Types.ty  (** A type before a [.], such as [Shape] in [Shape.Circle]. *)
  | Value_parameter of Types.parameter  (** A [USize] generic parameter. *)
  | Specification_value  (** [result], [old], or a specification function. *)

let show_resolution = function
  | Local_value local -> Printf.sprintf "local %d" local
  | Global { path; _ } -> Path.show path
  | Field_access { field; _ } -> "field " ^ field
  | Variant_value { variant; _ } -> "variant " ^ variant
  | Type_name type_ -> "type " ^ Types.show type_
  | Value_parameter parameter -> "generic " ^ parameter.name
  | Specification_value -> "specification"

type literal =
  | Integer_value of Z.t
  | Float_value of float
      (** Already rounded to the literal's type. A [Float32] is rounded to 32 bits. *)

(* The iteration of a [for] loop. *)
type loop =
  | Integer_range of { element : Types.ty; inclusive : bool }
      (** A counted loop over built-in integers. *)
  | Yielding of { call : call; mode : Types.mode }
      (** A call of a [yields] method: [each], or a call that is written out. *)
  | Pulled of { cursor : Types.ty }  (** A cursor, pulled until it is exhausted. *)

type pattern =
  | Variant_pattern of { type_ : Types.ty; variant : string }
  | Record_pattern of { type_ : Types.ty }
  | Constant_pattern of Path.t
  | Literal_pattern of literal
  | Other_pattern

type template = {
  from_template : call option;  (** The tag's [from_template]. [None] for a plain string. *)
  part_conversions : call option list;
      (** For each interpolated value: its [From] conversion to the tag's [Part], or for a plain
          string, its [Display]. *)
  interpolated : bool;
}

(* What tools read of the tables. *)
type published = {
  types : Types.ty option array;
  local_types : Types.ty option array;
  resolutions : resolution option array;
  callees : Path.t option array;
      (** By the id of each call of a named function or a type's own method: the callee's path. *)
}

type t = {
  types : Types.ty option array;  (** The type of each expression, by its id. Published. *)
  local_types : Types.ty option array;
      (** The type of each binding, by the id of its name. Published. *)
  resolutions : resolution option array;
      (** By the id of each [Name], [Member], or [Bracket] expression. Published. *)
  calls : call option array;
      (** By the id of each call: a [Call], an operator, an index, and a compound assignment. *)
  literals : literal option array;
      (** By the id of each literal expression, literal pattern, and literal bound of a range
          pattern. *)
  patterns : pattern option array;  (** By the id of each pattern. *)
  scrutinee_types : Types.ty option array;  (** The type of each pattern's scrutinee, by its id. *)
  loops : loop option array;  (** By the id of each [for] statement. *)
  templates : template option array;  (** By the id of each string literal. *)
  lend_modes : Types.mode option array;
      (** By the id of each call of a lending method: the mode in which the part is lent, read-only
          or [mut]. The loan lasts until the caller's statement ends. *)
}

(* Empty tables for a definition with [size] nodes. *)
let create size =
  {
    types = Array.make size None;
    local_types = Array.make size None;
    resolutions = Array.make size None;
    calls = Array.make size None;
    literals = Array.make size None;
    patterns = Array.make size None;
    scrutinee_types = Array.make size None;
    loops = Array.make size None;
    templates = Array.make size None;
    lend_modes = Array.make size None;
  }

(* Tables with the same entries, in new arrays. *)
let copy tables =
  {
    types = Array.copy tables.types;
    local_types = Array.copy tables.local_types;
    resolutions = Array.copy tables.resolutions;
    calls = Array.copy tables.calls;
    literals = Array.copy tables.literals;
    patterns = Array.copy tables.patterns;
    scrutinee_types = Array.copy tables.scrutinee_types;
    loops = Array.copy tables.loops;
    templates = Array.copy tables.templates;
    lend_modes = Array.copy tables.lend_modes;
  }

let publish (tables : t) : published =
  {
    types = tables.types;
    local_types = tables.local_types;
    resolutions = tables.resolutions;
    callees =
      Array.map
        (function Some { callee = Function { path; _ }; _ } -> Some path | _ -> None)
        tables.calls;
  }
