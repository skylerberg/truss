type encoding = Utf_8 | Utf_16

val serve :
  input:In_channel.t ->
  output:Out_channel.t ->
  check:(root:string -> encoding -> (string * string) list -> string option) ->
  int

val check_buffers : string list -> int
val check_arguments : root:string -> encoding -> (string * string) list -> string list

module For_testing : sig
  val position : encoding -> Source.t -> int -> int * int
  val offset : encoding -> Source.t -> line:int -> column:int -> int

  type server

  val create :
    write:(Json.t -> unit) ->
    check:(root:string -> encoding -> (string * string) list -> string option) ->
    server

  val handle : server -> Json.t -> unit
  val refresh : server -> unit
end
