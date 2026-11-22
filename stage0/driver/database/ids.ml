let encode value = Marshal.to_string value [ No_sharing ]
let of_package (package : Path.package) = Store.identify (Path.show_package package)
let of_module (module_ : Path.module_) = Store.identify (encode module_)
let of_file (file : Path.file) = Store.identify (encode file)
let of_key (key : Resolve.Names.key) = Store.identify (encode key)
let of_path (path : Path.t) = Store.identify (encode path)

let of_dependency (package : Path.package) (dependency : Path.package) =
  Store.identify (encode (package, dependency))

let of_item (item : Lowered.Item.t) = Store.identify (encode item)
