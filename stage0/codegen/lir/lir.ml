(* The lowered IR. See lir.mli. Its parts:

   - [Ir]: the types, the queries over them, and the canonical form
   - [Encoding]: the canonical encoding and the hash
   - [Printing]: the text form *)

include Ir
include Encoding
include Printing
