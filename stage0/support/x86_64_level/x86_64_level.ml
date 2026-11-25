type t = V1 | V2 | V3 | V4

let default = V3
let all = [ V1; V2; V3; V4 ]
let show = function V1 -> "v1" | V2 -> "v2" | V3 -> "v3" | V4 -> "v4"
let parse text = List.find_opt (fun level -> show level = text) all
