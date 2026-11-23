module Path_table = Hashtbl.Make (Path)

type t = Types.signature option Path_table.t

let create () : t = Path_table.create 16

let read (signatures : t) (interface : Interface.Lookups.t) path =
  match Path_table.find_opt signatures path with
  | Some signature -> signature
  | None ->
      let signature = Interface.Impls.read_signature interface path in
      Path_table.replace signatures path signature;
      signature

let read_of_method signatures interface ~owner (method_ : Types.trait_method) =
  let path =
    Path.Method { owner; name = method_.method_name; receiver = method_.method_receiver }
  in
  match read signatures interface path with
  | Some signature -> signature
  | None ->
      Compiler_bug.raise_bug ~stage:"Infer" "the method `%s` has no signature" (Path.show path)
