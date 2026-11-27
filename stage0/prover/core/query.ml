type t = {
  mutable declarations : Logic.declaration list;
  declared : Logic.sort list Tables.Symbol_table.t;
  definitions : unit Tables.Symbol_table.t;
  stated : unit Tables.Stated_table.t;
  defined_terms : Logic.term Tables.Term_table.t;
  specified_terms : unit Tables.Term_table.t;
  mutable facts : Fact_list.t;
  mutable scopes : (Logic.symbol * Logic.term list ref) list;
  quantifier_facts : Logic.term list Tables.Term_table.t;
  written_quantifiers : unit Tables.Term_table.t;
  mutable quantifier_symbols : Logic.symbol list;
  mutable obligations : Obligation.t list;
  withheld : Path.t Tables.Symbol_table.t;
  mutable fresh : int;
  fresh_order : int Tables.Symbol_table.t;
  mutable holes : (Resolve.Names.key * Obligation.location) list;
  private_state : Private_state.t;
}

let create () =
  {
    declarations = [];
    declared = Tables.Symbol_table.create 64;
    definitions = Tables.Symbol_table.create 8;
    stated = Tables.Stated_table.create 64;
    defined_terms = Tables.Term_table.create 16;
    specified_terms = Tables.Term_table.create 16;
    facts = Fact_list.empty;
    scopes = [];
    quantifier_facts = Tables.Term_table.create 16;
    written_quantifiers = Tables.Term_table.create 4;
    quantifier_symbols = [];
    obligations = [];
    withheld = Tables.Symbol_table.create 4;
    fresh = 0;
    fresh_order = Tables.Symbol_table.create 64;
    holes = [];
    private_state = Private_state.create ();
  }

let read_state query key = Private_state.read query.private_state key
let make_variable ?(numbers = []) label = Logic.Symbol.Variable { label; numbers }

let declare query (declaration : Logic.declaration) =
  let declare_symbol name arguments =
    if not (Tables.Symbol_table.mem query.declared name) then begin
      Tables.Symbol_table.replace query.declared name arguments;
      query.declarations <- declaration :: query.declarations
    end
  in
  match declaration with
  | Constant (name, _) -> declare_symbol name []
  | Function (name, arguments, _) -> declare_symbol name arguments
  | Definition { symbol; _ } ->
      if not (Tables.Symbol_table.mem query.definitions symbol) then begin
        Tables.Symbol_table.replace query.definitions symbol ();
        query.declarations <- declaration :: query.declarations
      end
  | Datatype _ -> invalid_arg "Query.declare: a datatype is derived from its sort"

let find_argument_sorts query symbol = Tables.Symbol_table.find_opt query.declared symbol
let is_defined query symbol = Tables.Symbol_table.mem query.definitions symbol
let add_fact query fact = query.facts <- Fact_list.add fact query.facts
let assume query ~under fact = add_fact query (Logic.( ==> ) under fact)

type reason =
  | Defines of Logic.term
  | Specifies of Logic.term
  | Lemma
  | Proven_by of Path.t
  | Hypothesis
  | Generalizes_an_execution

let add_theorem query ~because theorem =
  match because with
  | Defines subject -> (
      if Tables.Term_table.mem query.specified_terms subject then
        Compiler_bug.raise_bug ~stage:"Prover"
          "`%s` is defined by `%s` after a fact about it was stated, which may contradict it"
          (Logic.show_term subject) (Logic.show_term theorem);
      match Tables.Term_table.find_opt query.defined_terms subject with
      | Some earlier ->
          if earlier <> theorem then
            Compiler_bug.raise_bug ~stage:"Prover" "`%s` is defined by `%s` and again by `%s`"
              (Logic.show_term subject) (Logic.show_term earlier) (Logic.show_term theorem)
      | None ->
          Tables.Term_table.replace query.defined_terms subject theorem;
          add_fact query theorem)
  | Specifies subject ->
      if not (Tables.Term_table.mem query.defined_terms subject) then begin
        Tables.Term_table.replace query.specified_terms subject ();
        add_fact query theorem
      end
  | Lemma | Proven_by _ | Hypothesis | Generalizes_an_execution -> add_fact query theorem

let define query defined value =
  add_theorem query ~because:(Defines defined) (Logic.equal defined value)

type mark = { declaration_count : int; fact_count : int; fresh_count : int }

let mark query =
  {
    declaration_count = List.length query.declarations;
    fact_count = Fact_list.count query.facts;
    fresh_count = query.fresh;
  }

let list_declarations_since query mark =
  List.take (List.length query.declarations - mark.declaration_count) query.declarations

let list_facts_since query mark = Fact_list.list_newest_since query.facts ~count:mark.fact_count
let holds query ~under goal = Fact_list.holds query.facts ~under goal

let run_dropping_facts query ~drop run =
  let before = query.facts in
  let result = run () in
  query.facts <-
    List.fold_left
      (fun facts fact -> if drop fact then facts else Fact_list.add fact facts)
      before
      (List.rev (Fact_list.list_newest_since query.facts ~count:(Fact_list.count before)));
  result

let run_once query stated make =
  if not (Tables.Stated_table.mem query.stated stated) then begin
    Tables.Stated_table.replace query.stated stated ();
    make ()
  end

let run_without_facts query run =
  let facts = query.facts
  and stated = Tables.Stated_table.copy query.stated
  and defined_terms = Tables.Term_table.copy query.defined_terms
  and specified_terms = Tables.Term_table.copy query.specified_terms in
  query.facts <- Fact_list.empty;
  Fun.protect
    ~finally:(fun () ->
      query.facts <- facts;
      Tables.Stated_table.reset query.stated;
      Tables.Stated_table.iter (Tables.Stated_table.replace query.stated) stated;
      Tables.Term_table.reset query.defined_terms;
      Tables.Term_table.iter (Tables.Term_table.replace query.defined_terms) defined_terms;
      Tables.Term_table.reset query.specified_terms;
      Tables.Term_table.iter (Tables.Term_table.replace query.specified_terms) specified_terms)
    run

let run_in_scope query symbols run =
  let facts = ref [] in
  let enclosing = query.scopes in
  query.scopes <- List.map (fun symbol -> (symbol, facts)) symbols @ enclosing;
  let result = Fun.protect ~finally:(fun () -> query.scopes <- enclosing) run in
  (result, !facts)

let add_scoped_fact query ~bound term =
  let named = List.filter (fun name -> Logic.mentions [ name ] term) bound in
  if List.for_all (fun name -> List.mem_assoc name query.scopes) named then
    match List.find_opt (fun (name, _) -> List.mem name named) query.scopes with
    | Some (_, facts) -> facts := term :: !facts
    | None -> ()

let list_scope_facts query names =
  List.concat_map
    (fun (name, facts) -> if List.mem name names then List.rev !facts else [])
    query.scopes

let run_under_binder query symbol run =
  query.quantifier_symbols <- symbol :: query.quantifier_symbols;
  let result, facts = run_in_scope query [ symbol ] run in
  let attach_facts term =
    if facts <> [] then Tables.Term_table.replace query.quantifier_facts term (List.rev facts);
    term
  in
  (result, attach_facts)

let note_written_quantifier query term = Tables.Term_table.replace query.written_quantifiers term ()

let add_quantifier_facts query ~binders term =
  let is_stated bound fact =
    List.for_all
      (fun name -> List.mem name bound || not (Logic.mentions [ name ] fact))
      query.quantifier_symbols
  in
  let rec walk positive bound term =
    let collect_facts symbols =
      let bound = List.map fst symbols @ bound in
      ( bound,
        List.filter (is_stated bound)
          (Option.value ~default:[] (Tables.Term_table.find_opt query.quantifier_facts term)) )
    in
    match term with
    | Logic.Forall (symbols, trigger, body) when positive ->
        let bound, facts = collect_facts symbols in
        let body = walk positive bound body in
        Logic.Forall
          ( symbols,
            trigger,
            match facts with [] -> body | facts -> Logic.( ==> ) (Logic.conjunction facts) body )
    | Logic.Exists (symbols, body) when not positive ->
        let bound, facts = collect_facts symbols in
        let body = walk positive bound body in
        Logic.Exists
          ( symbols,
            match facts with [] -> body | facts -> Logic.( &&& ) (Logic.conjunction facts) body )
    | Logic.Operation (((And | Or) as operator), parts) ->
        Logic.Operation (operator, List.map (walk positive bound) parts)
    | Logic.Operation (Implies, [ premise; conclusion ]) ->
        Logic.Operation
          (Implies, [ walk (not positive) bound premise; walk positive bound conclusion ])
    | Logic.Operation (Ite, [ condition; then_; else_ ]) ->
        Logic.Operation (Ite, [ condition; walk positive bound then_; walk positive bound else_ ])
    | Logic.Operation (Not, [ inner ]) -> Logic.Operation (Not, [ walk (not positive) bound inner ])
    | term -> term
  in
  walk true binders term

let take_fresh_number query =
  query.fresh <- query.fresh + 1;
  query.fresh

let make_fresh_name query label = make_variable label ~numbers:[ take_fresh_number query ]

let make_ordered_fresh_name query label =
  let name = make_fresh_name query label in
  Tables.Symbol_table.replace query.fresh_order name query.fresh;
  name

let is_made_between query since until name =
  Option.map
    (fun order -> order > since.fresh_count && order <= until.fresh_count)
    (Tables.Symbol_table.find_opt query.fresh_order name)

let mentions_fresh_since query since term =
  let is_fresh_after name = is_made_between query since (mark query) name = Some true in
  let rec walk = function
    | Logic.Symbol name -> is_fresh_after name
    | Logic.Integer _ | Logic.Boolean _ | Logic.Bits _ -> false
    | Logic.Apply (name, arguments) -> is_fresh_after name || List.exists walk arguments
    | Logic.Operation (_, arguments) -> List.exists walk arguments
    | Logic.Is (_, argument) -> walk argument
    | Logic.Forall (_, _, body) | Logic.Exists (_, body) -> walk body
  in
  walk term

let make_obligation query ~find_signature ~list_axioms ~list_constructors ~condition location
    obligation goal : Obligation.t =
  let pruned =
    Logic.declare_derived ~find_signature ~list_constructors
      (Logic.prune ~find_signature ~list_axioms
         {
           declarations = List.rev query.declarations;
           facts = Fact_list.list_oldest_first query.facts;
           goal = Logic.( ==> ) condition goal;
         })
  in
  {
    obligation;
    instance = { builtins = []; condition = [] };
    location;
    cited = None;
    fixes = [];
    query = pruned;
    has_untriggered_written_fact =
      Logic.has_untriggered_fact pruned
        ~is_counted:(Tables.Term_table.mem query.written_quantifiers);
    withheld =
      List.sort_uniq Path.compare
        (List.filter_map
           (function
             | Logic.Function (symbol, _, _) -> Tables.Symbol_table.find_opt query.withheld symbol
             | Constant _ | Definition _ | Datatype _ -> None)
           pruned.declarations);
    refutation =
      (match goal with
      | Logic.Boolean false -> None
      | _ -> Some (Logic.( ==> ) condition (Logic.not_ goal)));
  }

let add_obligation query obligation = query.obligations <- obligation :: query.obligations
let note_withheld query symbol callee = Tables.Symbol_table.replace query.withheld symbol callee
let list_obligations query = List.rev query.obligations
let add_hole query hole = if not (List.mem hole query.holes) then query.holes <- hole :: query.holes
let list_holes query = List.rev query.holes
