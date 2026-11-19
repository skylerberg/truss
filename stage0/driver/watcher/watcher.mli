type t
type changes = Changed of string list | Rescan | Removed

val start : is_skipped_name:(string -> bool) -> cookie_directory:string -> string -> t
val extract_descriptor : t -> Unix.file_descr
val read_changes : t -> changes
val read_pending_changes : t -> changes
val stop : t -> unit

module For_testing : sig
  val is_delivered_before_synchronizing : unit -> bool
end
