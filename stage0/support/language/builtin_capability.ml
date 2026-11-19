type t = Panic | Run_forever | System

let all = [ Panic; Run_forever; System ]
let show = function Panic -> "Panic" | Run_forever -> "RunForever" | System -> "System"
