val version : string
val is_xid_start : Uchar.t -> bool
val is_xid_continue : Uchar.t -> bool
val is_forbidden : Uchar.t -> bool
val is_bidi_control : Uchar.t -> bool
val is_control : Uchar.t -> bool
val find_forbidden_name : Uchar.t -> string option
