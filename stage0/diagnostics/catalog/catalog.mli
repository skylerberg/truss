type 'node range = 'node Description.range = { covering : 'node list }

type 'node siblings = 'node Description.siblings =
  | Next of 'node range
  | Previous of 'node range
  | Alone of { clause : 'node; is_only_clause : bool }

type 'node location = 'node Description.location = private
  | At of 'node
  | Over of 'node range
  | Before of 'node
  | After of 'node

type 'node piece = 'node Description.piece = private
  | Text of string
  | Quote of 'node
  | Quote_over of 'node range
  | Substituted of {
      clause : 'node;
      replacements : ('node * string) list;
      type_names : (string * string) list;
    }

type 'node boundary = 'node Description.boundary = private Start of 'node | Stop of 'node

type 'node edit = 'node Description.edit = private
  | Replace of 'node * 'node piece list
  | Insert_before of 'node * 'node piece list
  | Insert_after of 'node * 'node piece list
  | Delete of 'node boundary * 'node boundary
  | Remove_entry of { entry : 'node range; siblings : 'node siblings }
  | Remove_lines of 'node range
  | Add_lines_after of 'node * 'node piece list list
  | Add_line_before of 'node * 'node piece list

type 'node fix = 'node Description.fix = private {
  title : 'node piece list;
  edits : 'node edit list;
}

type 'node t = 'node Description.t = private {
  code : Diagnostic.Code.t;
  severity : Diagnostic.severity;
  location : 'node location;
  message : 'node piece list;
  notes : ('node location * 'node piece list) list;
  fixes : 'node fix list;
}

type node = Nodes.node = private
  | Node of Core.origin
  | Definition
  | In_definition of Path.key * Core.origin

type description = node t

val make_reported : _ t -> Diagnostic.reported
val read_entry_siblings : Core.origin range list -> int -> Core.origin siblings

module Usage = Usage
module Usage_description = Usage_description
module Package = Package
module Package_description = Package_description
module Typing = Typing
module Typing_description = Typing_description
module Resolve = Resolve
module Resolve_description = Resolve_description
module Patterns = Patterns
module Patterns_description = Patterns_description
module Capabilities = Capabilities
module Capabilities_description = Capabilities_description
module Ownership = Ownership
module Ownership_description = Ownership_description
module Inference = Inference
module Inference_description = Inference_description
module Prover = Prover
module Prover_description = Prover_description
