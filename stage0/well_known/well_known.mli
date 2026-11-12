(** The definitions of the standard library that the compiler names by path. A definition that the
    library renames or moves is renamed or moved here. *)

type t =
  | Equal
  | Ordered
  | Ordering
  | Hash
  | Copyable
  | Plain
  | Storable
  | Display
  | Default
  | Index
  | Index_assign
  | Cursor
  | Model
  | From
  | Add
  | Subtract
  | Multiply
  | Divide
  | Remainder
  | Negate
  | Range
  | Exit_code
  | Option
  | Result
  | List
  | Slice
  | String
  | String_slice
  | Text_builder
  | Literal
  | Template
  | From_template
  | Set
  | Map
  | Sequence
  | Finite_set
  | Finite_map
  | Panic
  | Tasks
  | Serialize
  | Deserialize
  | Serializer
  | Deserializer
  | Deserialize_required
      (** The function a derived [deserialize] reads a field without a default with. *)
  | Deserialize_optional
      (** The function a derived [deserialize] reads a field with a default with. *)
  | Unknown_variant
      (** The error a derived [deserialize] returns for a variant name it does not know. *)
  | Write_fully  (** The function that writes a program's output. *)
  | Text_copied_from  (** The function that makes a [String] from a C string. *)
  | Run_tests  (** The entry point of a test executable. *)

val all : t list
val path : t -> Path.t
val of_path : Path.t -> t option

val is : t -> Path.t -> bool
(** Whether a path is that of the definition: [is Equal path]. *)

val specification : Path.module_
(** [standard::specification], whose types exist only in specifications. *)

val system_module : string -> Path.module_
(** A module of [standard::system], which holds the system implementation of each capability. *)

val in_system : Path.module_ -> bool
(** Whether a module is [standard::system] or one of its modules. *)
