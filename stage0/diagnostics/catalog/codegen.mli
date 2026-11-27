type location = { file : Path.file; line : int; column : int }
type evaluated = Constant of Path.t | Assertion of { definition : Path.t; condition : int }
type construct = Lending_capability_method of { capability : Path.t; method_ : string }
type todo_type = { type_ : Path.t; location : location }
type ending = Panicked | Assertion_failed | Incomplete | Timed_out | Crashed

type stop =
  | Depends_on_itself of Path.t
  | Ended of { ending : ending; message : string }
  | Unbuildable of failure

and failure =
  | Unsupported of { construct : construct; location : location option }
  | Todo_types of todo_type list
  | Todo_types_reached_by_main of todo_type list
  | Evaluation_stopped of { evaluated : evaluated; stop : stop }
  | Test_program_ended of { status : int; errors : string }
  | C_compiler_failed of string
  | Unreadable_test_report of string
