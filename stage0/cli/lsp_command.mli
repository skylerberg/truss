type encoding = Utf_8 | Utf_16

val position : encoding -> String.t -> int -> int * int
val offset : encoding -> String.t -> line:int -> column:int -> int
val check : root:string -> encoding -> (string * string) list -> Json.t

type server = {
  write : Json.t -> unit;
  check : root:string -> encoding -> (string * string) list -> string option;
  mutable root : string;
  mutable encoding : encoding;
  mutable buffers : (string * string) list;
  mutable shut_down : bool;
  mutable published : string list;
}

val refresh : server -> unit

type step = Continue | Recheck | Stop of int

val handle : server -> Json.t -> step

val create :
  write:(Json.t -> unit) ->
  check:(root:string -> encoding -> (string * string) list -> string option) ->
  server

val serve :
  input:In_channel.t ->
  output:Out_channel.t ->
  check:(root:string -> encoding -> (string * string) list -> string option) ->
  int

val check_buffers : string list -> int
val check_arguments : root:string -> encoding -> (string * string) list -> string list
