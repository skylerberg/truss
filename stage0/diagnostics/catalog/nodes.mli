type node = Node of Core.origin | Definition | In_definition of Path.key * Core.origin
type description = node Description.t
