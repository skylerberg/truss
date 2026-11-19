type t = Read | Mut | Own

let show_prefix = function Read -> "" | Mut -> "mut " | Own -> "own "
