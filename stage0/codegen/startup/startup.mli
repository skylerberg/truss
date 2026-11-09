(* The C that every program links with: the runtime's few functions, and
   the generated [main]. See CODEGEN.md, "Program startup and failure".

   The runtime is one fixed file per target, compiled once and cached, so
   unlike generated code it includes the system's headers: its declarations
   of signals and alternate stacks differ between systems, and parsing the
   headers costs nothing on an edit. *)

val runtime : Memory_layout.target -> string

(* A C [main] that installs the stack-overflow handler, calls the C
   function [entry], which takes nothing and returns an [Int32], and exits
   with the status it returns. *)
val main_calling : string -> string
