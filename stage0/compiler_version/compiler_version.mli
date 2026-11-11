val digest : string
(** What names this compiler's code: a digest, in hex, of its source and of what it is built with.
    It does not change with the standard library's text or with a test, so a result kept under it is
    still found after an edit to the library. *)
