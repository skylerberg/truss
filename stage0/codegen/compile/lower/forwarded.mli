type t = { setup : (Mir.local * Types.ty * Mir.call) list; call : Mir.call }
(** The call that a call of a lending method stands for, where the method only forwards. [setup] is
    each intrinsic call that the method makes first, in order, with the caller's local that takes
    its result and the local's type: [Array.at] makes the array's view before it indexes it. *)

val call :
  substitution:Types.substitution -> fresh:(unit -> Mir.local) -> Mir.t -> Mir.call -> t option
(** The calls that a call of a lending method stands for, where the method only forwards: its body
    is one lending call, of which it lends the part whole, after intrinsic calls that compute the
    lending call's arguments. [call ~substitution ~fresh mir outer] is those calls with the
    arguments of [outer] in place of the method's parameters, and the types of the method's
    instance, which [substitution] gives. A caller can then make the calls itself: an index of a
    [List] is its element's place, with no call of [List.at]. [fresh] gives a local of the caller's
    for each result of [setup].

    [None] where the method does more, or where an argument cannot stand for its parameter: the
    method owns it, leaves it out, or reads a part of a value by value. *)
