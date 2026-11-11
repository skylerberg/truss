(** The parser's entry point.

    A file's tokens are split into pieces, its [use] lines and its definitions, and each piece is
    parsed on its own, from its own slice of the tokens. Its tree depends only on its own tokens,
    its spans are relative to its first token, and so are its diagnostics, so that a piece that only
    moved parses to exactly the same result, which can be cached and reused. *)

type piece = Split.piece = { first : int; stop : int }
(** A piece of a file: the indexes of its first token and one past its last. *)

val split : Token.t array -> piece list
(** The pieces of a file, in order. *)

val is_use : Token.t array -> piece -> bool

type relative_diagnostics
(** A piece's diagnostics, relative to its base, so that a piece that only moved has the same ones.
    They cannot be shown until {!placed} puts them in the file's offsets. *)

type 'value parsed = { value : 'value Syntax.item; diagnostics : relative_diagnostics }

val placed : _ parsed -> Diagnostic.t list
(** A piece's diagnostics, moved by its base to their place in the file. *)

val definition :
  Source.t -> Token.t array -> piece -> Syntax.definition parsed * Syntax.definition parsed list
(** A definition, with the checks that need its whole tree, and the methods written inside it when
    it is a trait, an [impl], or a capability. Each method is a definition of its own, parsed from
    its own tokens, with its own positions and node ids. *)

val use_line : Source.t -> Token.t array -> piece -> Syntax.path option parsed
(** A [use] line, and its path if it parsed. Whether it comes before every definition depends on the
    rest of the file, so {!parse} checks it. *)

val parse : Source.t -> Token.t array -> Syntax.file * Diagnostic.t list
(** A whole file, with its diagnostics in the file's offsets, in order of position. *)

val spelled_words : string list
(** The names the parser recognizes by their spelling, in [cost] clauses. *)

(** {1 The documents' examples}

    Examples in the documents mix definitions, signatures without bodies, and statements. Only the
    tests of the documents and the tools that use the examples parse them, with these. Their
    diagnostics are in the file's offsets. *)

type example = Example_definition | Example_signature

val example_definition : Source.t -> Token.t array -> piece -> example * Diagnostic.t list
(** A definition, or a function's signature without a body. *)

val example_statement : Source.t -> Token.t array -> piece -> Diagnostic.t list
(** A statement, as a line of a block. *)
