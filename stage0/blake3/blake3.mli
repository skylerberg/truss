(** BLAKE3, the hash behind every fingerprint, every key, and the name of every value in the store.

    Only the default hash mode with a 32-byte output is provided, since that is all the compiler
    uses. The algorithm follows the BLAKE3 specification and its reference implementation. *)

val hash : string -> string
(** The 32-byte digest of the input. *)

val to_hex : string -> string
(** Lowercase hexadecimal, two digits per byte. *)
