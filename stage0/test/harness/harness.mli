(** Running the tests of one test executable. When the executable exits, it prints the result, and
    exits with status 1 if any test failed. *)

val test : string -> (unit -> unit) -> unit
(** Runs a test now. An exception it raises is a failure, and so is a result that an engine the test
    made holds and a new engine with the same inputs computes differently. *)

val always : string -> (unit -> unit) -> unit
(** Runs a test whatever [TRUSS_TEST] names, for a step that every test of the executable needs,
    such as building the program they run in. *)

val wanted : string -> bool
(** Whether a test of this name runs: every test does, or with [TRUSS_TEST] set, the tests whose
    names contain it. *)

val fail : ('a, unit, string, unit) format4 -> 'a
(** Reports a failure of the test that is running. *)

val expect_not_recomputed :
  Engine.t ->
  first:(unit -> unit) ->
  again:(unit -> unit) ->
  ('key, 'value) Query.query ->
  'key list ->
  unit
(** Fails the test unless [first] computes the query's result for each key and [again] computes none
    of them. A key that [first] does not compute fails, so the check cannot pass on a result nothing
    computes. *)

val scratch : string -> string
(** A new empty directory whose name starts with [name]. Each is inside one directory of this
    process, which is removed when the process exits. *)

val write_files : string -> (string * string) list -> unit
(** Writes files under a directory, each a path under it and its text, making directories as needed.
*)

val git : string -> string list -> unit
(** Runs git in a directory, with a test author, and fails the test if git fails. *)

val expect_string : expected:string -> string -> unit
(** Fails the running test unless the strings are equal. *)

val expect_strings : expected:string list -> string list -> unit
(** Fails the running test unless the lists are equal. *)

val markdown_documents : unit -> string list
(** The names of the Markdown documents at the root of the repository, in order. *)

val workspace_path : string -> string
(** The path of a file of the repository, given from the workspace root, such as ["SYNTAX.md"],
    whatever directory the executable runs in. *)
