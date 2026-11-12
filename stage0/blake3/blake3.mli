(** BLAKE3, the hash behind every fingerprint, every key, and the name of every value in the store.

    Two of the specification's modes are provided, each with a 32-byte output. The algorithm follows
    the BLAKE3 specification and its reference implementation. *)

val hash : string -> string
(** The 32-byte digest of the input, in the default mode. It names bytes by their content: a value
    in the store, a file's text, an executable. *)

val derive_key : context:string -> string -> string
(** The 32-byte digest of the material in the derive-key mode, under [context]. A key that is made
    of fields, such as a store result's kind and input, is this digest of the fields' deterministic
    CBOR encoding.

    The mode's flags keep its outputs apart from every [hash] output and from the outputs of every
    other context, whatever the material, so two kinds of key cannot collide. [context] must be a
    constant that names the application, the date the key format was written, and the key's purpose,
    such as ["truss 2026-11-12 store result"]. A changed key format takes a new context, so keys of
    the old format stop matching instead of being misread.

    Applied to [context] alone, it hashes the context once and gives the function that derives every
    key of that kind. *)

val to_hex : string -> string
(** Lowercase hexadecimal, two digits per byte. *)
