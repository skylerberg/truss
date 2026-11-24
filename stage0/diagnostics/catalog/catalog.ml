type 'node range = 'node Description.range = { covering : 'node list }

type 'node siblings = 'node Description.siblings =
  | Next of 'node range
  | Previous of 'node range
  | Alone of { clause : 'node; is_only_clause : bool }

type 'node location = 'node Description.location =
  | At of 'node
  | Over of 'node range
  | Before of 'node
  | After of 'node

type 'node piece = 'node Description.piece =
  | Text of string
  | Quote of 'node
  | Quote_over of 'node range
  | Substituted of {
      clause : 'node;
      replacements : ('node * string) list;
      type_names : (string * string) list;
    }

type 'node boundary = 'node Description.boundary = Start of 'node | Stop of 'node

type 'node edit = 'node Description.edit =
  | Replace of 'node * 'node piece list
  | Insert_before of 'node * 'node piece list
  | Insert_after of 'node * 'node piece list
  | Delete of 'node boundary * 'node boundary
  | Remove_entry of { entry : 'node range; siblings : 'node siblings }
  | Remove_lines of 'node range
  | Add_lines_after of 'node * 'node piece list list
  | Add_line_before of 'node * 'node piece list

type 'node fix = 'node Description.fix = { title : 'node piece list; edits : 'node edit list }

type 'node t = 'node Description.t = {
  code : Diagnostic.Code.t;
  severity : Diagnostic.severity;
  location : 'node location;
  message : 'node piece list;
  notes : ('node location * 'node piece list) list;
  fixes : 'node fix list;
}

type node = Nodes.node =
  | Node of Core.origin
  | Definition
  | In_definition of Path.key * Core.origin

type description = node t

let find_example_name = Build.find_example_name
let make_reported (_ : _ t) = Diagnostic.reported_elsewhere

module Usage = Usage
module Package = Package
module Typing = Typing
module Resolve = Resolve
module Patterns = Patterns
module Capabilities = Capabilities
module Ownership = Ownership
module Inference = Inference
module Prover = Prover
