open Description
open Nodes

let node origin = Node origin
let cover ({ covering } : Core.origin range) = { covering = List.map node covering }
let at origin = At (node origin)
let over range = Over (cover range)
let quote origin = Quote (node origin)
let quote_over range = Quote_over (cover range)
let after origin = After (node origin)
let replace origin pieces = Replace (node origin, pieces)
let insert_before origin pieces = Insert_before (node origin, pieces)
let insert_after origin pieces = Insert_after (node origin, pieces)

let map_boundary : Core.origin boundary -> node boundary = function
  | Start origin -> Start (node origin)
  | Stop origin -> Stop (node origin)

let delete start stop = Delete (map_boundary start, map_boundary stop)

let remove_entry entry (siblings : Core.origin siblings) =
  Remove_entry
    {
      entry = cover entry;
      siblings =
        (match siblings with
        | Next range -> Next (cover range)
        | Previous range -> Previous (cover range)
        | Alone { clause; is_only_clause } -> Alone { clause = node clause; is_only_clause });
    }

let remove_lines range = Remove_lines (cover range)
let add_lines_after origin lines = Add_lines_after (node origin, lines)

let list_spelling_fixes origin ~written candidates =
  match Diagnostic.find_closest written candidates with
  | Some candidate ->
      [
        {
          title = [ Text (Printf.sprintf "Write `%s`." candidate) ];
          edits = [ replace origin [ Text candidate ] ];
        };
      ]
  | None -> []

let write_hidden path (visibility : Language.Visibility.t) =
  Printf.sprintf "`%s` is %s, so it cannot be used here." (Path.show path)
    (match visibility with
    | Private -> "private to its module"
    | Internal -> "internal to its package"
    | Public | Public_opaque ->
        Compiler_bug.raise_bug ~stage:"Catalog" "%s is public, so it is not hidden" (Path.show path))

let describe_call (origin : Core.origin) =
  match origin with
  | Written _ -> [ Text "this call" ]
  | Desugared { desugaring; _ } -> (
      match desugaring with
      | For_loop -> [ Text "the call that this `for` loop makes" ]
      | Quantifier -> [ Text "the call that this quantifier makes" ]
      | Derived -> [ Text "the call that the derived `"; quote origin; Text "` makes" ]
      | Rewrite | Try -> [ Text "the call that `"; quote origin; Text "` makes" ])

let show_field_path parameter fields = String.concat "." (parameter :: fields)

let show_function_name : Path.t -> string = function
  | Top { name; _ } | Method { name; _ } -> name
  | path -> Path.show path

let example_names =
  [
    "amount";
    "argument";
    "arguments";
    "arm";
    "at";
    "binding";
    "body";
    "call";
    "clause";
    "condition";
    "cost_function_name";
    "decided_at";
    "default";
    "edit";
    "entry";
    "first";
    "form";
    "header";
    "inner";
    "join";
    "key";
    "label";
    "later";
    "literals";
    "local";
    "measures";
    "name";
    "next";
    "operand";
    "origin";
    "other";
    "pattern";
    "patterns";
    "place";
    "promise";
    "receiver";
    "second";
    "statement";
    "subject";
    "tried";
    "type_";
    "uses";
    "value";
  ]

let example name =
  match List.find_index (String.equal name) example_names with
  | Some index -> Core.Written (index + 1)
  | None -> Compiler_bug.raise_bug ~stage:"Catalog" "the example node `%s` has no name" name

let find_example_name : Core.origin -> string option = function
  | Written id | Desugared { construct = id; _ } -> List.nth_opt example_names (id - 1)

let example_module : Path.module_ =
  { package = { owner = None; name = "app" }; modules = [ "main" ] }

let example_package = example_module.package
let example_path = Path.Top { module_ = example_module; name = "helper" }
let example_key : Path.key = { module_ = example_module; path = example_path; ordinal = 0 }
let example_type = Types.make_builtin Int64

let example_trait =
  Types.make_trait_reference ~arguments:[] (Path.make_standard_path [ "core" ] "Ordered")

let example_capability = Types.Built_in Panic

let example_condition : Types.condition =
  [
    { subject = Types.Parameter { owner = example_path; name = "Element" }; bound = example_trait };
  ]
