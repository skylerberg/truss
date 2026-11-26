type t = {
  mutable declarations : Logic.declaration list;
  declared : Logic.sort list Tables.Symbol_table.t;
  definitions : unit Tables.Symbol_table.t;
  datatypes : unit Tables.Type_table.t;
  stated : unit Tables.Stated_table.t;
  mutable facts : Fact_list.t;
  mutable scopes : (Logic.symbol * Logic.term list ref) list;
  quantifier_facts : Logic.term list Tables.Term_table.t;
  written_quantifiers : unit Tables.Term_table.t;
  mutable quantifier_symbols : Logic.symbol list;
  mutable obligations : Obligation.t list;
  mutable fresh : int;
  fresh_order : int Tables.Symbol_table.t;
}

let create () =
  {
    declarations = [];
    declared = Tables.Symbol_table.create 64;
    definitions = Tables.Symbol_table.create 8;
    datatypes = Tables.Type_table.create 16;
    stated = Tables.Stated_table.create 64;
    facts = Fact_list.empty;
    scopes = [];
    quantifier_facts = Tables.Term_table.create 16;
    written_quantifiers = Tables.Term_table.create 4;
    quantifier_symbols = [];
    obligations = [];
    fresh = 0;
    fresh_order = Tables.Symbol_table.create 64;
  }

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
  | Datatype _ -> invalid_arg "Query.declare: a datatype is declared by its sort"

let has_datatype query ty = Tables.Type_table.mem query.datatypes ty

let declare_datatype query ty list_constructors =
  Tables.Type_table.replace query.datatypes ty ();
  let constructors = list_constructors () in
  query.declarations <- Logic.Datatype (ty, constructors) :: query.declarations

let find_argument_sorts query symbol = Tables.Symbol_table.find_opt query.declared symbol
let is_declared query symbol = Tables.Symbol_table.mem query.declared symbol
let list_defined_symbols query = List.of_seq (Tables.Symbol_table.to_seq_keys query.definitions)
let count_declarations query = List.length query.declarations

let list_declarations_since query ~count =
  List.take (List.length query.declarations - count) query.declarations

let add_fact query fact = query.facts <- Fact_list.add fact query.facts
let count_facts query = Fact_list.count query.facts
let list_facts_since query ~count = Fact_list.list_newest_since query.facts ~count
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
  let facts = query.facts and stated = Tables.Stated_table.copy query.stated in
  query.facts <- Fact_list.empty;
  Fun.protect
    ~finally:(fun () ->
      query.facts <- facts;
      Tables.Stated_table.reset query.stated;
      Tables.Stated_table.iter (Tables.Stated_table.replace query.stated) stated)
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

let add_quantifier_symbol query symbol =
  query.quantifier_symbols <- symbol :: query.quantifier_symbols

let attach_quantifier_facts query term facts =
  Tables.Term_table.replace query.quantifier_facts term facts

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

let count_fresh query = query.fresh
let make_fresh_name query label = make_variable label ~numbers:[ take_fresh_number query ]

let make_ordered_fresh_name query label =
  let name = make_fresh_name query label in
  Tables.Symbol_table.replace query.fresh_order name query.fresh;
  name

let find_fresh_order query name = Tables.Symbol_table.find_opt query.fresh_order name

let mentions_fresh_after query mark term =
  let is_fresh_after name =
    match find_fresh_order query name with Some order -> order > mark | None -> false
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

let make_obligation query ~condition location obligation goal : Obligation.t =
  let pruned =
    Logic.prune
      {
        declarations = List.rev query.declarations;
        facts = Fact_list.list_oldest_first query.facts;
        goal = Logic.( ==> ) condition goal;
      }
  in
  {
    obligation;
    instance = [];
    location;
    cited = None;
    fixes = [];
    query = pruned;
    has_untriggered_written_fact =
      Logic.has_untriggered_fact pruned
        ~is_counted:(Tables.Term_table.mem query.written_quantifiers);
    is_rejection = goal = Logic.Boolean false;
  }

let add_obligation query obligation = query.obligations <- obligation :: query.obligations
let list_obligations query = List.rev query.obligations
