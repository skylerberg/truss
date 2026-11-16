open State

let variable ?(numbers = []) label = Symbol.Variable { label; numbers }

exception Unsupported of Source.Definition_span.t * string
exception Foreign_unsupported of string

let unsupported span format =
  Printf.ksprintf (fun message -> raise (Unsupported (span, message))) format

let bug format = Compiler_bug.bug ~stage:"Prover" format

let is_in_recursion_group context path =
  List.exists (Path.equal path) (context.lookups.recursion_group context.current)

let clauses (requires : Mir.requirement list) =
  List.map (fun (requirement : Mir.requirement) -> requirement.clause) requires

let declare context (declaration : Logic.declaration) =
  match declaration with
  | Constant (name, _) | Function (name, _, _) ->
      if not (Hashtbl.mem context.declared name) then begin
        Hashtbl.replace context.declared name ();
        context.declarations <- declaration :: context.declarations
      end
  | Datatype _ -> invalid_arg "Translate.declare: a datatype is declared by its sort"

let add_fact context fact = context.facts <- fact :: context.facts

let value_symbol context frame name sort =
  match List.rev frame.binders with
  | [] ->
      declare context (Logic.Constant (name, sort));
      Logic.Symbol name
  | outermost_first ->
      declare context
        (Logic.Function (name, List.map (fun (_, sort, _) -> sort) outermost_first, sort));
      Logic.Apply (name, List.map (fun (bound, _, _) -> Logic.Symbol bound) outermost_first)

let fresh_name context label =
  context.fresh <- context.fresh + 1;
  variable label ~numbers:[ context.fresh ]

let fresh context frame label sort =
  let name = fresh_name context label in
  Hashtbl.replace context.fresh_order name context.fresh;
  value_symbol context frame name sort

let mentions_fresh_after context mark term =
  let is_fresh_after name =
    match Hashtbl.find_opt context.fresh_order name with
    | Some order -> order > mark
    | None -> false
  in
  let rec walk = function
    | Logic.Symbol name -> is_fresh_after name
    | Logic.Integer _ | Logic.Boolean _ | Logic.Bits _ -> false
    | Logic.Apply (name, arguments) -> is_fresh_after name || List.exists walk arguments
    | Logic.Operation (_, arguments) -> List.exists walk arguments
    | Logic.Is (_, argument) -> walk argument
    | Logic.Forall (_, _, body) | Logic.Exists (_, body) -> walk body
  in
  walk term

let closed_over_binders frame term =
  let names = List.map (fun (name, _, _) -> name) frame.binders in
  if Logic.mentions (List.filter (fun name -> not (List.mem name names)) frame.bound) term then None
  else if not (Logic.mentions names term) then Some term
  else
    let outermost_first = List.rev frame.binders in
    Some
      (Logic.forall
         ( List.map (fun (name, sort, _) -> (name, sort)) outermost_first,
           Logic.( ==> )
             (Logic.conjunction (List.map (fun (_, _, premise) -> premise) outermost_first))
             term ))

let in_scope context frame term =
  let named = List.filter (fun name -> Logic.mentions [ name ] term) frame.bound in
  if List.for_all (fun name -> List.mem_assoc name context.scopes) named then
    match List.find_opt (fun (name, _) -> List.mem name named) context.scopes with
    | Some (_, facts) -> facts := term :: !facts
    | None -> ()

let scope_facts context names =
  List.concat_map
    (fun (name, facts) -> if List.mem name names then List.rev !facts else [])
    context.scopes

let with_quantifier_facts ?(binders = []) context term =
  let stated bound fact =
    List.for_all
      (fun name -> List.mem name bound || not (Logic.mentions [ name ] fact))
      context.quantifier_symbols
  in
  let rec walk positive bound term =
    let facts symbols =
      let bound = List.map fst symbols @ bound in
      ( bound,
        List.filter (stated bound)
          (Option.value ~default:[] (Hashtbl.find_opt context.quantifier_facts term)) )
    in
    match term with
    | Logic.Forall (symbols, trigger, body) when positive ->
        let bound, facts = facts symbols in
        let body = walk positive bound body in
        Logic.Forall
          ( symbols,
            trigger,
            match facts with [] -> body | facts -> Logic.( ==> ) (Logic.conjunction facts) body )
    | Logic.Exists (symbols, body) when not positive ->
        let bound, facts = facts symbols in
        let body = walk positive bound body in
        Logic.Exists
          ( symbols,
            match facts with [] -> body | facts -> Logic.( &&& ) (Logic.conjunction facts) body )
    | Logic.Operation ((("and" | "or") as operator), parts) ->
        Logic.Operation (operator, List.map (walk positive bound) parts)
    | Logic.Operation ("=>", [ premise; conclusion ]) ->
        Logic.Operation ("=>", [ walk (not positive) bound premise; walk positive bound conclusion ])
    | Logic.Operation ("not", [ inner ]) ->
        Logic.Operation ("not", [ walk (not positive) bound inner ])
    | term -> term
  in
  walk true binders term

let fact context frame term =
  if not (Logic.mentions frame.bound term) then add_fact context term
  else in_scope context frame term

let assume context frame term =
  match term with
  | Logic.Boolean true -> ()
  | _ ->
      let guarded = Logic.( ==> ) frame.condition term in
      if not (Logic.mentions frame.bound term || Logic.mentions frame.bound frame.condition) then
        add_fact context guarded
      else in_scope context frame guarded

let span_of (source : source) origin =
  let spans = Lazy.force source.spans in
  if origin >= 0 && origin < Array.length spans then spans.(origin)
  else Source.Definition_span.make 0 0

let add_requires context frame required =
  let text = Lazy.force frame.source.text in
  let brace =
    match Option.map context.lookups.interface.names.definition frame.source.key with
    | Some { kind = Function { body; _ }; _ } ->
        let start = (span_of frame.source body.id).start in
        if start < String.length text then Some start else None
    | _ -> None
  in
  let edit at before =
    Some { at; replacement = (Text (before ^ "  requires ") :: required) @ [ Text "\n" ] }
  in
  let edit =
    match brace with
    | Some at when at > 0 && text.[at - 1] = '\n' -> edit (Source.Definition_span.zero_width at) ""
    | Some at when at > 0 && text.[at - 1] = ' ' ->
        edit (Source.Definition_span.make (at - 1) at) "\n"
    | _ -> None
  in
  match edit with
  | Some edit ->
      [ { title = (Text "Add `requires " :: required) @ [ Text "`" ]; edits = [ edit ] } ]
  | None -> []

let parameter_name context symbol =
  if List.mem symbol context.entry then
    match List.assoc_opt symbol context.values with Some name -> Some name | None -> Some "self"
  else None

let all_printed printed =
  if List.mem None printed then None else Some (List.filter_map Fun.id printed)

let truss_of_value context term =
  let parenthesized level inner text = if inner < level then "(" ^ text ^ ")" else text in
  let rec arithmetic level = function
    | Logic.Operation ((("+" | "*") as operator), (_ :: _ :: _ as parts)) ->
        let inner = if operator = "+" then 1 else 2 in
        Option.map
          (fun printed -> parenthesized level inner (String.concat (" " ^ operator ^ " ") printed))
          (all_printed (List.map (arithmetic inner) parts))
    | Logic.Operation ("-", [ left; right ]) ->
        Option.map
          (fun printed -> parenthesized level 1 (String.concat " - " printed))
          (all_printed [ arithmetic 1 left; arithmetic 2 right ])
    | Logic.Operation ("-", [ inner ]) ->
        Option.map (fun printed -> parenthesized level 3 ("-" ^ printed)) (arithmetic 3 inner)
    | Logic.Integer value when Z.sign value < 0 && level > 0 -> Some ("(" ^ Z.to_string value ^ ")")
    | Logic.Apply (Symbol.Field { field; variant = None; _ }, [ receiver ]) ->
        Option.map (fun receiver -> receiver ^ "." ^ field) (arithmetic 4 receiver)
    | Logic.Symbol symbol -> parameter_name context symbol
    | Logic.Integer value -> Some (Z.to_string value)
    | Logic.Boolean value -> Some (if value then "true" else "false")
    | _ -> None
  in
  arithmetic 0 term

let truss_of_goal context term =
  let value = truss_of_value context in
  let rec print = function
    | Logic.Operation ((("<" | "<=" | ">" | ">=" | "=") as operator), [ left; right ]) -> (
        match (value left, value right) with
        | Some left, Some right ->
            Some (Printf.sprintf "%s %s %s" left (if operator = "=" then "==" else operator) right)
        | _ -> None)
    | Logic.Operation ("and", parts) -> joined " && " parts
    | Logic.Operation ("or", parts) -> joined " || " parts
    | Logic.Operation ("not", [ inner ]) -> Option.map (Printf.sprintf "!(%s)") (print inner)
    | Logic.Operation ("=>", [ premise; conclusion ]) -> (
        match (print premise, print conclusion) with
        | Some premise, Some conclusion -> Some (Printf.sprintf "(%s) ==> (%s)" premise conclusion)
        | _ -> None)
    | term -> value term
  and joined separator parts =
    Option.map
      (fun printed -> "(" ^ String.concat separator printed ^ ")")
      (all_printed (List.map print parts))
  in
  let printed =
    match term with
    | Logic.Operation ("and", parts) ->
        Option.map (String.concat " && ") (all_printed (List.map print parts))
    | Logic.Operation ("or", parts) ->
        Option.map (String.concat " || ") (all_printed (List.map print parts))
    | term -> print term
  in
  if List.exists (fun symbol -> List.mem symbol context.entry) (Logic.free_constants term) then
    printed
  else None

let rec oblige ?template_clause ?cited ?(fixes = []) context frame code span message goal =
  match
    obligation_at ?template_clause context frame code span message
      (with_quantifier_facts
         ~binders:(List.map (fun (name, _, _) -> name) frame.binders)
         context goal)
  with
  | Some obligation ->
      let fixes =
        match fixes with
        | [] when frame.source.key = Some context.home && frame.makes_obligations -> (
            let goal =
              match frame.condition with
              | Logic.Boolean true -> goal
              | condition -> Logic.( ==> ) condition goal
            in
            match truss_of_goal context goal with
            | Some required -> add_requires context frame [ Text required ]
            | None -> [])
        | fixes -> fixes
      in
      context.obligations <- { obligation with cited; fixes } :: context.obligations;
      assume context frame goal
  | None -> ()

and obligation_at ?template_clause context frame code span message goal =
  if not frame.makes_obligations then None
  else if not (Logic.mentions frame.bound goal || Logic.mentions frame.bound frame.condition) then
    Some (make_obligation ?template_clause context frame code span message goal)
  else
    let names = List.map (fun (name, _, _) -> name) frame.binders in
    let goal =
      match scope_facts context names with
      | [] -> goal
      | facts -> Logic.( ==> ) (Logic.conjunction facts) goal
    in
    match closed_over_binders frame (Logic.( ==> ) frame.condition goal) with
    | Some closed ->
        Some
          (make_obligation ?template_clause context
             { frame with condition = Logic.Boolean true }
             code span message closed)
    | None -> None

and make_obligation ?template_clause context frame code span message goal =
  let query =
    Logic.prune
      {
        declarations = List.rev context.declarations;
        facts = List.rev context.facts;
        goal = Logic.( ==> ) frame.condition goal;
      }
  in
  {
    code;
    span;
    message;
    cited = None;
    fixes = [];
    query;
    values = context.values;
    decisions = List.rev context.decisions;
    locals =
      Locals.fold
        (fun local term shown ->
          match (term, Hashtbl.find_opt context.local_names local) with
          | Logic.Symbol symbol, Some name
            when not (List.mem_assoc symbol context.values || List.mem_assoc symbol shown) ->
              (symbol, name) :: shown
          | _ -> shown)
        frame.locals
        (match frame.result with
        | Some (Logic.Symbol symbol) when not (List.mem_assoc symbol context.values) ->
            [ (symbol, "result") ]
        | _ -> []);
    template_clause;
  }

let quote source origin =
  match source.key with Some key -> Quote (key, origin) | None -> Text "this expression"

let quoted text (span : Source.Definition_span.t) =
  if span.stop = span.start then "this expression" else Source.Definition_span.quote text span

let text_of source origin = quoted (Lazy.force source.text) (span_of source origin)
let builtin ty = Types.find_builtin ty

let bounds (ty : Types.ty) =
  if Types.is_builtin Character ty then Some (Z.zero, Z.of_int 0x10FFFF)
  else Types.find_integer_range ty

let is_numeric (ty : Types.ty) = match ty with Types.Integer -> true | _ -> bounds ty <> None

let float_format (ty : Types.ty) =
  match builtin ty with Some Float32 -> Some (8, 24) | Some Float64 -> Some (11, 53) | _ -> None

let is_bool ty = Types.is_builtin Bool ty
let constructor_name (ty : Types.ty) variant = Symbol.Constructor { type_ = ty; variant }
let selector_name ty variant field = Symbol.Field { type_ = ty; variant; field }
let is_standard_equal = Well_known.is Equal
let equal_trait = Well_known.path Equal

let visible_type context (ty : Types.ty) =
  match ty with
  | Named { path; arguments } when builtin ty = None -> (
      match Interface.Definition.read_interface context.lookups.interface path with
      | Some (Interface.Environment.Type_interface interface)
        when (not interface.opaque) || Path.package path = Path.package context.current ->
          let substitution =
            Option.value ~default:[] (Types.make_substitution interface.type_generics arguments)
          in
          Some (interface, substitution)
      | _ -> None)
  | _ -> None

let constructors context ty =
  match visible_type context ty with
  | Some (interface, substitution) -> (
      let fields (list : Types.field list) =
        List.sort compare
          (List.map
             (fun (field : Types.field) ->
               (field.field_name, Types.substitute substitution field.field_type))
             list)
      in
      match interface.shape with
      | Record list -> Some [ (None, fields list) ]
      | Sum variants ->
          Some
            (List.sort compare
               (List.map
                  (fun (variant : Types.variant) ->
                    ( Some variant.variant_name,
                      match variant.fields with Some list -> fields list | None -> [] ))
                  variants))
      | Todo_type | Builtin_type _ -> None)
  | None -> None

let rec sort_of context (ty : Types.ty) : Logic.sort =
  if is_numeric ty then Int
  else if is_bool ty then Bool
  else
    match (ty, float_format ty) with
    | _, Some (exponent, significand) -> Float (exponent, significand)
    | _ when Types.equal ty Types.unit ->
        if not (Hashtbl.mem context.datatypes ty) then begin
          Hashtbl.replace context.datatypes ty ();
          context.declarations <- Logic.Datatype (ty, [ (Symbol.Unit, []) ]) :: context.declarations
        end;
        Type_sort ty
    | Function function_type, _ -> Function_sort (List.length function_type.inputs)
    | _ -> begin
        (if not (Hashtbl.mem context.datatypes ty) then
           match constructors context ty with
           | Some shape ->
               Hashtbl.replace context.datatypes ty ();
               let declaration =
                 Logic.Datatype
                   ( ty,
                     List.map
                       (fun (variant, fields) ->
                         ( constructor_name ty variant,
                           List.map
                             (fun (field, field_type) ->
                               (selector_name ty variant field, sort_of context field_type))
                             fields ))
                       shape )
               in
               context.declarations <- declaration :: context.declarations
           | None -> ());
        Type_sort ty
      end

let rec structural context ?(seen = []) (ty : Types.ty) =
  if is_numeric ty || is_bool ty || Types.is_builtin Character ty || Types.equal ty Types.unit then
    true
  else if List.exists (Types.equal ty) seen then true
  else
    match (visible_type context ty, constructors context ty) with
    | Some (interface, _), Some shape ->
        List.exists is_standard_equal interface.derives
        && List.for_all
             (fun (_, fields) ->
               List.for_all
                 (fun (_, field_type) -> structural context ~seen:(ty :: seen) field_type)
                 fields)
             shape
    | _ -> false

let in_range ty term =
  match bounds ty with
  | Some (low, high) ->
      let in_bounds =
        Logic.(Operation ("<=", [ Integer low; term ]) &&& Operation ("<=", [ term; Integer high ]))
      in
      if Types.is_builtin Character ty then
        Logic.(
          in_bounds
          &&& not_
                (Operation ("<=", [ int 0xD800; term ]) &&& Operation ("<=", [ term; int 0xDFFF ])))
      else in_bounds
  | None -> Logic.Boolean true

let once context stated make =
  if not (Hashtbl.mem context.stated stated) then begin
    Hashtbl.replace context.stated stated ();
    make ()
  end

let arrive context frame prefix ty =
  let value = fresh context frame prefix (sort_of context ty) in
  assume context frame (in_range ty value);
  value

let bind frame local ty term =
  {
    frame with
    locals = Locals.add local term frame.locals;
    types = Locals.add local ty frame.types;
  }

let substituted context frame ty =
  (Interface.Impls.normalize context.lookups.interface ~bounds:Interface.Impls.no_bounds)
    (Types.substitute frame.substitution ty)

let local_type context frame local =
  Option.map (substituted context frame) (Locals.find_opt local frame.types)

let mentions_potential term =
  let rec walk = function
    | Logic.Apply ((Symbol.Potential _ | Symbol.Slack _), _) -> true
    | Logic.Forall (_, _, body) | Logic.Exists (_, body) -> walk body
    | term -> List.exists walk (Logic.arguments term)
  in
  walk term

let restrict frame condition = { frame with condition = Logic.( &&& ) frame.condition condition }

let known_on_paths (paths : (Logic.term * frame) list) =
  let known pick ~is_same ~differing =
    let keys =
      List.fold_left
        (fun keys ((_, frame) : Logic.term * frame) ->
          Locals.fold (fun key _ keys -> Locals.add key () keys) (pick frame) keys)
        Locals.empty paths
    in
    Locals.mapi
      (fun key () ->
        let each =
          List.map (fun (condition, frame) -> (condition, Locals.find_opt key (pick frame))) paths
        in
        match each with
        | (_, Some one) :: rest
          when List.for_all
                 (fun (_, other) ->
                   match other with Some other -> is_same one other | None -> false)
                 rest ->
            one
        | _ -> differing each)
      keys
  in
  let under condition = List.map (fun (on, known) -> (Logic.( &&& ) condition on, known)) in
  let each_under each =
    List.concat_map
      (fun (condition, known) -> under condition (Option.value ~default:[] known))
      each
  in
  let aliases = known (fun frame -> frame.aliases) ~is_same:( = ) ~differing:each_under in
  let slices =
    known
      (fun frame -> frame.slices)
      ~is_same:( = )
      ~differing:(fun each ->
        if
          List.exists
            (function _, (None | Some Unknown_slice) -> true | _, Some (Slices _) -> false)
            each
        then Unknown_slice
        else
          Slices
            (List.concat_map
               (function
                 | condition, Some (Slices slices) -> under condition slices
                 | _, (Some Unknown_slice | None) -> [])
               each))
  in
  let lends = known (fun frame -> frame.lends) ~is_same:( == ) ~differing:each_under in
  (aliases, slices, lends)

let path_condition context (frame : frame) condition =
  match condition with
  | Logic.Boolean _ | Logic.Symbol _ -> condition
  | _ when (not frame.makes_obligations) || Logic.mentions frame.bound condition -> condition
  | _ ->
      let path = fresh context frame "path" Logic.Bool in
      fact context frame (Logic.equal path condition);
      path

let merge context ?value_type ~condition (paths : (Logic.term * frame * Logic.term option) list) =
  let first = match paths with (_, first, _) :: _ -> first | [] -> bug "no paths meet" in
  let is_expression = not first.makes_obligations in
  let aliases, slices, lends =
    known_on_paths (List.map (fun (on, frame, _) -> (on, frame)) paths)
  in
  let merged = { first with condition; aliases; slices; lends } in
  let chosen values =
    match List.rev values with
    | (_, _, last) :: earlier ->
        List.fold_left (fun otherwise (on, _, term) -> Logic.ite on term otherwise) last earlier
    | [] -> bug "a value that no path gives"
  in
  let define prefix sort (values : (Logic.term * frame * Logic.term) list) =
    match values with
    | (_, _, term) :: rest
      when List.for_all (fun (_, _, other) -> other == term || other = term) rest ->
        term
    | _
      when List.for_all
             (fun (_, _, term) -> match term with Logic.Boolean _ -> true | _ -> false)
             values ->
        Logic.disjunction
          (List.filter_map
             (fun (on, _, term) -> if term = Logic.Boolean true then Some on else None)
             values)
    | _
      when is_expression
           || List.exists
                (fun (on, (frame : frame), term) ->
                  Logic.mentions first.bound on
                  || Logic.mentions first.bound frame.condition
                  || Logic.mentions first.bound term)
                values ->
        chosen values
    | _ ->
        let symbol = fresh context first prefix sort in
        List.iter
          (fun (_, (frame : frame), term) ->
            fact context first (Logic.( ==> ) frame.condition (Logic.equal symbol term)))
          values;
        symbol
  in
  let held pick =
    let values =
      List.filter_map
        (fun (on, frame, _) -> Option.map (fun term -> (on, frame, term)) (pick frame))
        paths
    in
    if List.length values = List.length paths then Some values else None
  in
  let keys =
    List.fold_left
      (fun keys (_, (frame : frame), _) ->
        Locals.fold (fun key _ keys -> Locals.add key () keys) frame.locals keys)
      Locals.empty paths
  in
  let locals =
    Locals.mapi
      (fun id () ->
        match held (fun frame -> Locals.find_opt id frame.locals) with
        | Some values ->
            let sort =
              match local_type context first id with
              | Some ty -> sort_of context ty
              | None -> (
                  match values with (_, _, Logic.Boolean _) :: _ -> Logic.Bool | _ -> Logic.Int)
            in
            define "joined" sort values
        | None -> (
            match
              List.find_map (fun (_, (frame : frame), _) -> Locals.find_opt id frame.locals) paths
            with
            | Some term -> term
            | None -> bug "a local that no path binds"))
      keys
  in
  let types =
    List.fold_left
      (fun types (_, (frame : frame), _) -> Locals.union (fun _ ty _ -> Some ty) types frame.types)
      Locals.empty paths
  in
  let self =
    match (first.self_type, held (fun frame -> frame.self)) with
    | Some ty, Some values -> Some (define "self" (sort_of context ty) values)
    | _ -> first.self
  in
  let in_joined (frame : frame) amount =
    let renamed =
      Locals.fold
        (fun id joined renamed ->
          match Locals.find_opt id frame.locals with
          | Some own when own != joined && own <> joined -> (own, joined) :: renamed
          | _ -> renamed)
        locals []
    in
    let renamed =
      match (frame.self, self) with
      | Some own, Some joined when own <> joined -> (own, joined) :: renamed
      | _ -> renamed
    in
    List.fold_left (fun amount (from, into) -> Logic.replace ~from ~into amount) amount renamed
  in
  let spent =
    List.map
      (fun (key, term) ->
        let values =
          List.map
            (fun (on, (frame : frame), _) ->
              ( on,
                in_joined frame
                  (match List.assoc_opt key frame.spent with
                  | Some spent_term -> spent_term
                  | None -> term) ))
            paths
        in
        match values with
        | (_, first_value) :: rest
          when List.for_all (fun (_, other) -> other == first_value || other = first_value) rest ->
            (key, first_value)
        | _ ->
            let choice =
              match List.rev values with
              | (_, last) :: earlier ->
                  List.fold_left
                    (fun otherwise (on, value) -> Logic.ite on value otherwise)
                    last earlier
              | [] -> term
            in
            if Logic.mentions first.bound choice || mentions_potential choice then (key, choice)
            else
              let symbol = fresh context first "spent" Logic.Int in
              fact context first (Logic.equal symbol choice);
              (key, symbol))
      first.spent
  in
  let value =
    let values =
      List.filter_map
        (fun (on, frame, value) -> Option.map (fun term -> (on, frame, term)) value)
        paths
    in
    if values = [] || List.length values <> List.length paths then None
    else
      match value_type with
      | Some ty -> Some (define "value" (sort_of context ty) values)
      | None -> Some (chosen values)
  in
  let yielded_so_far =
    match (context.yielded_part, held (fun frame -> frame.yielded_so_far)) with
    | Some part, Some values ->
        Some
          (define "parts"
             (sort_of context
                (Types.Named { path = Well_known.path Sequence; arguments = [ Types.Type part ] }))
             values)
    | _ -> first.yielded_so_far
  in
  ({ merged with locals; types; spent; self; yielded_so_far }, value)

let join context ?value_type frames =
  match frames with
  | [] -> None
  | [ (frame, value) ] -> Some (frame, value)
  | (first, _) :: _ ->
      let condition =
        path_condition context first
          (Logic.disjunction (List.map (fun ((frame : frame), _) -> frame.condition) frames))
      in
      Some
        (merge context ?value_type ~condition
           (List.map (fun ((frame : frame), value) -> (frame.condition, frame, value)) frames))

let join_frames context frames =
  Option.map fst (join context (List.map (fun frame -> (frame, None)) frames))
