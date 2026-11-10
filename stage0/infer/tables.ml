(* The tables that the type checker fills while it checks a definition. The
   core form is built from them. All are dense arrays keyed by the syntax
   tree's node ids.

   Four of the tables are published as [Checked.t], for tools that work on
   the syntax tree. The others are read only by [Form], which builds the
   core form. *)

include (
  Checked :
    module type of struct
      include Checked
    end
    with type t := Checked.t)

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

type t = {
  types : Types.ty option array;  (** The type of each expression, by its id. Published. *)
  local_types : Types.ty option array;
      (** The type of each binding, by the id of its name. Published. *)
  meanings : meaning option array;
      (** By the id of each [Name], [Member], or [Bracket] expression. Published. *)
  calls : call option array;
      (** By the id of each call: a [Call], an operator, an index, and a compound assignment.
          Published. *)
  literals : literal option array;
      (** By the id of each literal expression, literal pattern, and literal bound of a range
          pattern. *)
  patterns : pattern option array;  (** By the id of each pattern. *)
  pattern_types : Types.ty option array;  (** The type of each pattern's scrutinee, by its id. *)
  loops : loop option array;  (** By the id of each [for] statement. *)
  templates : template option array;  (** By the id of each string literal. *)
  lends : Types.mode option array;
      (** By the id of each call of a lending method: the mode in which the part is lent, read-only
          or [mut]. The loan lasts until the caller's statement ends. *)
}

(* Empty tables for a definition with [size] nodes. *)
let create size =
  {
    types = Array.make size None;
    local_types = Array.make size None;
    meanings = Array.make size None;
    calls = Array.make size None;
    literals = Array.make size None;
    patterns = Array.make size None;
    pattern_types = Array.make size None;
    loops = Array.make size None;
    templates = Array.make size None;
    lends = Array.make size None;
  }

(* Tables with the same entries, in new arrays. *)
let copy tables =
  {
    types = Array.copy tables.types;
    local_types = Array.copy tables.local_types;
    meanings = Array.copy tables.meanings;
    calls = Array.copy tables.calls;
    literals = Array.copy tables.literals;
    patterns = Array.copy tables.patterns;
    pattern_types = Array.copy tables.pattern_types;
    loops = Array.copy tables.loops;
    templates = Array.copy tables.templates;
    lends = Array.copy tables.lends;
  }

(* The four tables that tools read. They share the arrays. *)
let published (tables : t) : Checked.t =
  {
    types = tables.types;
    local_types = tables.local_types;
    meanings = tables.meanings;
    calls = tables.calls;
  }
