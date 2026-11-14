val ended : Mir.t -> Mir.t
(** A MIR in which each value that a cursor loop pulls ends: a {!Mir.Dead} of the loop's part where
    an iteration ends, and on each way out of the loop's body. The MIR builder leaves these ends
    out, since only code generation drops the value. *)
