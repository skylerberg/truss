type 'node range = { covering : 'node list }
type 'node location = At of 'node | Over of 'node range | Before of 'node | After of 'node

type 'node piece =
  | Text of string
  | Quote of 'node
  | Quote_over of 'node range
  | Substituted of {
      clause : 'node;
      replacements : ('node * string) list;
      type_names : (string * string) list;
    }

type 'node boundary = Start of 'node | Stop of 'node

type 'node siblings =
  | Next of 'node range
  | Previous of 'node range
  | Alone of { clause : 'node; is_only_clause : bool }

type 'node edit =
  | Replace of 'node * 'node piece list
  | Insert_before of 'node * 'node piece list
  | Insert_after of 'node * 'node piece list
  | Delete of 'node boundary * 'node boundary
  | Remove_entry of { entry : 'node range; siblings : 'node siblings }
  | Remove_lines of 'node range
  | Add_lines_after of 'node * 'node piece list list
  | Add_line_before of 'node * 'node piece list

type 'node fix = { title : 'node piece list; edits : 'node edit list }

type 'node t = {
  code : Diagnostic.Code.t;
  severity : Diagnostic.severity;
  location : 'node location;
  message : 'node piece list;
  notes : ('node location * 'node piece list) list;
  fixes : 'node fix list;
}

type quoted = { definition_text : string; start : int; stop : int }

type ('node, 'span) source = {
  text : string Lazy.t;
  locate : 'node -> int * int;
  read_quoted : 'node -> quoted;
  make_span : int -> int -> 'span;
}

val render_with : ('node, 'span) source -> 'node t -> 'span Diagnostic.diagnostic
val render_file : text:string -> Source.span t -> Diagnostic.t
val render_spans : Source.span t -> Diagnostic.t
val describe_hidden : count:int -> severity:Diagnostic.severity -> int -> Source.span t
val select_shown : Diagnostic.t list -> Diagnostic.t list

module For_testing : sig
  val limit : int
end
