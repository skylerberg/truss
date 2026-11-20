val find_refused_class : State.state -> sides:(Types.ty * Types.ty) list -> int option

val report_decided_in_specification :
  State.state -> Source.Definition_span.t -> int -> Diagnostic.reported

val list_class_pairs : State.state -> Types.ty * Types.ty -> (int * Types.ty) list

val add_mismatch_diagnostic :
  State.state ->
  ?fixes:Source.Definition_span.t Diagnostic.fix list ->
  Diagnostic.Code.types ->
  Source.Definition_span.t ->
  sides:(Types.ty * Types.ty) list ->
  string ->
  Diagnostic.reported

val add_operand_mismatch :
  State.state ->
  at:Source.Definition_span.t ->
  left:Source.Definition_span.t * Types.ty ->
  right:Source.Definition_span.t * Types.ty ->
  Diagnostic.reported

val report_mismatch :
  State.state -> Source.Definition_span.t -> expected:Types.ty -> actual:Types.ty -> unit

val report_requirement :
  State.state ->
  State.goal ->
  ?associated:string * Types.ty * Types.ty ->
  unmet:string ->
  Types.ty ->
  Diagnostic.reported

val report_failure :
  State.state ->
  State.goal ->
  ?associated:string * Types.ty * Types.ty ->
  Types.ty ->
  Diagnostic.reported
