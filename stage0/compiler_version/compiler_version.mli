val digest : string
(** The name of this compiler's code: a digest, in hex, of its source and of its build toolchain. It
    does not change with the standard library's text or with a test, so a result kept under it is
    still found after an edit to the library. *)
