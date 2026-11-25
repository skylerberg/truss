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

let read_entry_siblings (entries : Core.origin range list) index : Core.origin siblings =
  match (index, entries) with
  | 0, _ :: next :: _ -> Next next
  | 0, ([] | [ _ ]) ->
      Compiler_bug.raise_bug ~stage:"Catalog" "the siblings of the only entry of a list"
  | _, _ -> Previous (List.nth entries (index - 1))

let cover_names names =
  { covering = List.map (fun (name : Syntax.name) : Core.origin -> Written name.id) names }

let cover_path (path : Syntax.path) = cover_names (path.modules @ [ path.last ])

type diagnostic =
  | Usage of Usage.t
  | Package of Package.t
  | Typing of Typing.t
  | Resolve of Resolve.t
  | Patterns of Patterns.t
  | Capabilities of Capabilities.t
  | Ownership of Ownership.t
  | Inference of Inference.t
  | Prover of Prover.t

let describe : diagnostic -> description = function
  | Usage diagnostic -> Usage_description.describe diagnostic
  | Package diagnostic -> Package_description.describe diagnostic
  | Typing diagnostic -> Typing_description.describe diagnostic
  | Resolve diagnostic -> Resolve_description.describe diagnostic
  | Patterns diagnostic -> Patterns_description.describe diagnostic
  | Capabilities diagnostic -> Capabilities_description.describe diagnostic
  | Ownership diagnostic -> Ownership_description.describe diagnostic
  | Inference diagnostic -> Inference_description.describe diagnostic
  | Prover diagnostic -> Prover_description.describe diagnostic

type reported = Diagnostic.reported

let make_reported (_ : diagnostic) = Diagnostic.reported_elsewhere
let reported_elsewhere = Diagnostic.reported_elsewhere

module Code = Code
module Codegen = Codegen
module Codegen_description = Codegen_description
module Model_value = Model_value
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
