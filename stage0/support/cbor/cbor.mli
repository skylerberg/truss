(** Deterministic CBOR (RFC 8949, section 4.2), the encoding exact keys are hashed over, such as a
    test's key.

    Each value has exactly one encoding: integers, lengths, and floats take their shortest form,
    every length is definite, and a map's entries are sorted by the bytes of their encoded keys. The
    same encoder must later be written in Truss and give the same bytes, so this module writes them
    directly rather than through a library. *)

type t =
  | Integer of Z.t
      (** Any integer. One beyond 64 bits is a bignum, tag 2 or 3, with no leading zero bytes. *)
  | Bytes of string
  | Text of string  (** Text, which the caller must give as valid UTF-8. *)
  | Array of t list
  | Map of (t * t) list  (** Encoded in sorted order, whatever order it is given in. *)
  | Tag of int * t
  | Bool of bool
  | Null
  | Float of float
      (** The shortest of 16, 32, or 64 bits that holds the value exactly. Every NaN is [0xf97e00].
      *)

val int : int -> t

val encode : t -> string
(** Raises [Invalid_argument] if a map has two entries whose keys encode the same, since a map with
    a repeated key has no deterministic form, or if a tag is negative. *)
