> 🧔 This part of this doc was written by a human. LLMs are not allowed to edit it.

# Truss Implementation

The stage0 compiler is written in OCaml and is compiled to a static binary. When
the Truss compiler builds a program it emits C code as its backend. Truss
programs do not link to a separate runtime, they use libc. Truss packages
compile to a single binary or library.

## Modular Design

Each part of Truss should be modular. This will help make the compiler easier to
develop as well as make it easier to bootstrap the compiler in parts.

> 🤖 LLMs are allowed to edit the doc below this point

## Notes for stage0

### Building

- **Dependencies** are declared in `dune-project`, which generates
  `truss.opam`. Install them with
  `opam install . --deps-only --with-test --with-dev-setup`. On macOS, Zarith
  also needs GMP and `pkgconf` from Homebrew. The `sqlite3` bindings link the
  system's SQLite library, which macOS ships and which Debian and Ubuntu
  package as `libsqlite3-dev`.
- **The code database is a SQLite file,** `.truss/database.sqlite` in a
  project's root. [CODE_DATABASE.md](CODE_DATABASE.md) describes its tables
  and stages. `sqlite3 .truss/database.sqlite` reads it while a background
  process has it open: `SELECT name FROM definition WHERE kind = 0` lists
  the functions, `SELECT code, message FROM diagnostic` lists every
  diagnostic, `SELECT code, shows FROM verdict WHERE proven = 0` lists the
  obligations that the last check did not prove, and
  `SELECT stage, COUNT(*) FROM stale GROUP BY stage` counts the units that
  wait for each stage.
- **Z3 5.3.3** runs the prover's queries, and the prover refuses any other
  version, since another could answer differently. Install it with
  `brew install z3` on macOS, or from the release's archive, and put it on
  the path or name it in `TRUSS_Z3`. CI downloads that release and checks
  its hash.
- **`stage0/tools/prover_queries`** prints the solver's input for each
  obligation that starts at a position, written as a diagnostic writes it:
  `dune exec ./stage0/tools/prover_queries/prover_queries.exe --
  standard/numbers/floats/floats.truss:6:13`. A file of a package is named
  by its path. The output is one script for `z3 -in`, which prints each
  obligation's answer, Z3's reason for an unknown answer, and the steps Z3
  used.
- **The Unicode tables are generated** from the Unicode character database
  files that `stage0/tools/unicode/sources.txt` lists with their hashes:
  the compiler's into `stage0/support/unicode/unicode_tables.ml`, and the standard
  library's into `standard/text/unicode_data/unicode_data.truss`. To move to a new
  version of Unicode, change that list and run
  `stage0/tools/unicode/regenerate.sh`.
- **`dune build`** builds everything, and **`dune fmt`** formats the code
  with the ocamlformat version that `.ocamlformat` pins.
- **`stage0/tools/docs/build.sh`** builds the odoc documentation of every
  library, a page of the library dependency graph, and a page of the
  dependencies between areas into `_build/docs`. On the page of each
  library, `stage0/tools/docs/library_uses` lists the names that the
  library's `.cmt` and `.cmti` files reference in other libraries and the
  names that other libraries reference in it, each linked to its entry in
  odoc's index. After each definition, it lists the modules of any library
  or executable that reference the definition, leaving out the references
  by which a library re-exports its own modules. A page hides the libraries
  and modules of stage0/test and stage0/tools until the reader checks Show
  test and tools. The script needs odoc and
  dune-deps from opam and Graphviz
  and jq from Homebrew, which `dune-project` does not list because CI never
  builds the documentation.
- **CI** (`.github/workflows/ci.yml`) builds, checks formatting, checks that
  `truss.opam` matches `dune-project`, rejects comments, runs every test
  suite, and proves the standard library, on every pull request and every
  push to `main`. It must stay fast: it installs nothing in an ordinary run,
  restores dune's cache and compiled objects from `main`, and gives the
  longest suites runners of their own.

### Libraries

- **A library is a contract with more than one consumer, or a unit that
  must not see its consumer's dependencies.**
- **Each library belongs to one area of stage0,** a directory under
  `stage0`. The dependencies between areas form no cycle.
- **A unit of several modules inside a library is a subdirectory.** The
  library's `dune` file sets `(include_subdirs qualified)`, the
  subdirectory's module of its own name is its interface, and its other
  modules are hidden from the rest of the library, as `lexer/scanner` is.

### The lexer

- **The scanner reads Truss, and the habits read other languages.** The
  scanner's core scans the grammar of [SPECIFICATION.md](SPECIFICATION.md).
  Each form of another language, such as a `//` comment, `===`, `f"..."`,
  or `0755`, belongs to a module of `Habits`, which the scanner asks first
  wherever such a form can start. A habit reports the form and lexes it as
  the Truss token it stands for. A change to Truss's grammar edits the core,
  and a new form of another language edits only the habits.

### The parser

- **The parser reads tokens, never the source text.** A fix that would move
  code edits around it instead, so the fix never respells the code:
  `x as Int64` becomes `Int64.from_integer(x)` by inserting
  `Int64.from_integer(` and replacing ` as Int64` with `)`.
- **The tree holds no positions.** A node holds an id, and its item's span
  table holds the node's span at that index. A definition that only moved
  parses to an equal tree, so a change to positions alone re-runs only the
  parts that report positions, and no stage strips spans to compare two
  trees.

### Stages

- **Every stage after the type checker reads the MIR.** Ownership, the
  prover, and code generation read no core expression.
- **No stage rebuilds what an earlier stage had,** since a rebuilt fact can
  disagree with the original. The builder lowers each expression once and
  records each fact where it has it, and no stage finds a loop in the
  control-flow graph. A stage that needs a value in another state runs the
  MIR's statements in that state.
- **The values of a type have one definition.** `Types.list_value_ranges`
  gives the ranges of an integer type and of `Character`, whose two ranges
  leave out the surrogates. The pattern checker splits them, the prover
  derives a value's range, the count of a range's values and the value at
  an offset from them, and the code generator's range loop skips the gap
  between them.
- **A body's final expression returns in each branch.** The builder lowers
  the final `if`, `match` or block of a body in tail position: each branch
  returns its own value where it has one, and its end where it has none,
  and no value joins. An obligation checked at a return is then checked on
  the path of one branch, where it is located and can be refuted, and a
  value moved on one branch needs no drop flag.

### The prover

- **The cost modules hold the rules of cost checking.** A cost is ghost
  state of the one symbolic execution, so the modules that execute the MIR
  call the cost modules at each statement, and a new cost rule edits a cost
  module. The state of cost checking is one record, `context.cost`, and CI
  rejects a use of it outside the cost modules.

  | Module | Holds |
  |---|---|
  | `Costs` | The counters, the terms of an amount, and the join of the amounts spent on two paths |
  | `Counters` | The counters of a body: their assignment from cost clauses, and spending |
  | `Cost_promises` | The cost clauses of a function as obligations at its return |
  | `Potentials` | The potential that a value holds |
  | `Amounts` | The amount that a call or an operation spends |
  | `Loop_costs` | The cost rules of a loop |

- **A worst-case bound is proven at both ends of the exchange rate between
  a callee's bound and its potential.** A callee's `O(f)` is checked against
  `2^17 * f + 2^16` of the callee's units and charged to its caller as
  `f + 1`, so one unit of a callee's bound stands for up to 2^17 of the
  callee's steps, and one unit of potential for one. The work of a callee
  with an amortized bound is therefore its bound less its potential change
  divided by 2^17. An account is affine in that rate, so it is within a
  bound at that rate where it is within the bound at rate 0 and at rate 1.
  `Counters.make_potential_credit` builds `credit(change)`, which is
  `change` or zero by one Boolean that no fact constrains, so each cost
  obligation is proven for both rates. `Loop_costs` credits the potential
  that a loop gained by the same term in a plain account.

  An amortized account has the same exchange rate, for each type that
  holds potential. The potential of a type is worth as many steps as the
  largest unit of a function that takes credit for releasing it, so a
  function whose callee's amortized bound covers a change in that type's
  potential cannot also take that credit at one unit each.
  `Counters.spend_operation` blocks the types that such a callee reaches,
  and `Counters.count_held_potential` counts a decrease in a blocked class
  as zero. A callee that blocks a class which the body already took credit
  for raises `Counters.Blocks_credited_potential`, and
  `Translate.run_blocking` translates the definition again with the class
  blocked from the start, so no term in a query depends on a later call.

  | Rate | Account of a callee with an amortized bound | Rejects |
  |---|---|---|
  | 1 | Its bound less its potential change | A bound that ignores potential that the callee spent |
  | 0 | Its bound | A bound whose steps are paid for by potential that the callee saved |
- **A supposed execution is read under a condition that nothing asserts.**
  A fact of a frame is assumed wherever the frame's condition holds, so a
  fact about code that may not run must not enter a frame that does. The
  prover reads three executions that it only supposes: a lambda's body,
  where the lambda is made, both when it is checked and when it is explored
  for a definition; a call of a function passed for a parameter,
  where its contract is compared with the parameter's; and the return of a
  definition, where a cost clause that names `result` is checked to be
  defined. `Facts.suppose` makes the frame for each: it restricts the frame
  by a new Boolean, so every fact and obligation of the supposed execution
  has that Boolean as a premise, and the query stays satisfiable where the
  execution is impossible. Three false proofs came from a supposed execution
  in a frame that runs: the `ensures` of a function that never returns,
  which no result meets, denied the `requires` it was assumed under; the
  invariant of a supposed result of type `Room[capacity]` gave the body a
  fact about `capacity`; and a call in a lambda's body, explored where the
  lambda was made, gave the code around the lambda the callee's `ensures`
  about a captured value.
- **The facts of a partial term are assumed under its precondition.** Three
  terms denote a value only where a condition holds: an application of a
  function value, under the `requires` of its contract; an element at an
  index, under the bounds; and a call's result, under the callee's
  `requires`. A frame that makes obligations proves the condition before it
  reads the term, and an obligation that is made is assumed, so the term's
  facts are stated in that frame as they are. A frame that makes none reads
  a clause of another definition and proves nothing, so it takes the
  condition as a premise: `Facts.restrict_unless_proven` gives the frame.
  That premise is all that keeps the claim "this term is a value of its
  type" from holding of arguments that the clause's own definition never
  showed well defined. A callee whose `ensures` names `read(0)` under a
  premise that its `requires` rules out is such a clause.
- **A contract is resolved once, and its three readers differ only in what
  they prove and what they assume.** The rules are those of modular
  verification with pre- and postconditions. A definition is proven against
  its contract once, and every use relies on that proof alone, so a use may
  assume a clause only under the premises that the proof assumed.
  `Contracts.list_promises` is the one statement of those premises: it lists
  each clause set's `ensures` with the clause set whose `requires` they were
  proven under.

  | Reader | Proves | Assumes |
  |---|---|---|
  | The definition's check, `Translate` | Each `ensures` at every return, under its premise | The `requires` |
  | A call, `Calls` | The `requires`, and the Panic condition where the caller may not panic | Each `ensures` under its premise, in the frame of the call |
  | The axiom of a logic function, `Contract_axioms` | Nothing | Each `ensures`, for every argument in the function's domain |

  A logic function is total in the logic and unspecified outside its domain.
  Its domain is a condition under which the definition returns: valid
  arguments, the premise of the clause, the Panic condition, and, for a
  callee in the recursion group of the definition being proven, arguments
  below the entry measure, which is the induction hypothesis. A call that
  returned gives its `ensures` without the Panic condition, since
  `uses Panic unless C` says that `C` rules a panic out, not that a return
  implies `C`.

  A definition that may abort returns for no argument that the prover
  knows of, so it has no axiom, and a call of it in a specification or a
  proof assumes neither its `ensures` nor that its result is valid. It may
  abort where its code that runs, or a callee's, holds a call of
  `intrinsic.crash` or of an intrinsic that allocates. That is the fact
  `may_abort` of the call graph, which the code database computes for a
  definition from its own code and its callees' facts, and once for the
  members of a recursion group. A proof block, a loop's clauses, a theorem
  and a specification-only function never run: each is read in a ghost
  frame, where a call is a specification's, so none of them holds an abort
  site or a callee, and a specification-only definition never aborts. A
  method called through a trait bound and a function value have
  no code to read, so each may abort unless the trait or the function's
  type states `cost allocations == 0`, which every `impl` and every
  function passed then proves. A scalar result keeps its range, since a
  value in range exists for every argument.

  A definition's own code also calls code that it cannot read: a method
  through a bound of its generics, and a function value. Its proof assumed
  the contract of each such call that returned, so its own contract is an
  axiom only where those calls return. Such a call is an abort site unless
  the trait's method, or the function's type, states
  `cost allocations == 0`. A function value has no weaker condition: its
  call leaves the relation of the value in the frame, which the definition's
  own `ensures` can state of its result with `visit.ensures(...)`, and that
  relation holds only of a call that returned.
  A trait's method on a type whose `impl` is known is a callee like any
  other: the method that the `impl` writes, derives or inherits has its own
  fact. So the fact of a definition depends on no code that a caller
  supplies, and a call is judged by the callee's fact alone.

  A storage of capacity zero allocates nothing, so the call that builds one,
  which an empty list literal makes, is no abort site.

  So `cost allocations == 0` stands for "returns" on a trait's method and on
  a function's type. Three obligations make that hold of code
  that could reach `intrinsic.crash`, which allocates nothing. A method
  whose trait states the clause for it, and a function that states
  it and is named as a value, are rejected where their `may_abort` holds.
  The method is one that an `impl` writes, or the body that the trait gives:
  that body is judged by the fact of the node it is proven as, which is the
  trait's method, or the method that an `impl` inherits where the body is
  proven for that `impl`. A
  lambda whose type states it is rejected where its body, or a lambda made
  in its body, holds an abort site or calls a function that may abort. So
  every function value of such a type was made from code that returns.

  `Query.note_withheld` records each call whose contract a specification
  did not learn, by the symbol of its function. An obligation keeps the
  callees among them that its pruned query declares, and a failed one names
  them, so the diagnostic says why a fact that the code seems to state is
  missing.
- **The semantics of a storage operation is a contract written in Truss.**
  `standard.intrinsic_contracts` declares a function with the name and the
  signature of the intrinsic and a `todo` body, as `standard.specification`
  declares `Sequence`. `Intrinsic.has_contract` lists these operations.
  `Callee.resolve_target` resolves a call of one to its declaration, so the
  rules of a call prove its `requires` and assume its `ensures` and its
  costs, and `Mir.Call_edges` gives the call an edge to the declaration. The
  contract is trusted: no proof compares it with the generated code. The
  declaration of an operation that may abort, which `Intrinsic.may_abort`
  lists, is an abort site. So its contract is no axiom and holds only of a
  call that returned, and it needs no `requires` that the capacity is
  within `core.maximum_length`.

  | Operations | Semantics |
  |---|---|
  | `storage_empty`, `storage_with_capacity`, `storage_set_capacity`, `storage_from_array`, `array_from_storage`, `storage_shorten`, `storage_push`, `storage_pop`, `storage_insert`, `storage_remove`, `storage_swap`, `find_byte` | A contract in `standard.intrinsic_contracts` |
  | `storage_length`, `storage_capacity`, `storage_model`, `array_model` | Terms of the logic, which the contracts are written in |
  | Scalar operations | Terms of the logic, in `Operations` |
  | Every other buffer operation, and the runtime operations | `Intrinsics` |
- **One module states the contract of a logic function as an axiom.**
  `Contract_axioms` builds the axiom for a call and for a function used as a
  value, with every premise its proof had: arguments in range that meet
  their invariants, the `requires`, and, for a callee in the recursion group
  of the definition being proven, arguments below the entry measure. Its
  state is one record, `context.axioms`, and CI rejects a use of it outside
  `Contract_axioms`.
- **`Termination` holds the rules that show a body to end.** It compares a
  recursive call with the entry of the definition being proven: the call
  obliges the comparison, and the axiom of a callee in the recursion group
  takes it as a premise, so the two never differ. It also holds the measure
  of a loop. Its state is one record, `context.termination`.
- **`Cycles` reads the recursion group and the proof group, and rejects a
  proof that assumes a fact whose own proof assumes it back.** Every fact
  that a proof takes from another definition is an edge of the proof graph,
  which `Mir.Call_edges` lists: a callee's contract, a type's invariant, and
  the laws of an `impl`. `Laws` assumes no law of an `impl` in the proof
  group of the definition being proven.
- **`Callbacks` holds the rules of a function value.** A function value has
  two terms in the logic: its application, where its type uses no capability
  and has no `mut` input, and the relation that holds of the arguments and
  the result of each of its calls, which `visit.ensures(...)` reads.
  `Callbacks` knows the contract of two function values: a named function,
  whose definition `Callee` resolves at the type arguments written, and a
  function-typed parameter. It keys each contract by the value's term, so
  the contract follows the value into a local and out of it, and nothing
  reads the form of the expression that an argument was written as. The
  contract of a parameter belongs to the frame that binds the parameter,
  `frame.callbacks`: the first frame of the definition being proven, and
  the frame that `Contracts.make_entry_frame` builds to read a clause of
  another definition, where the key is the argument. So a clause that
  applies its function parameter finds that parameter's `requires` wherever
  the clause is read: at a call, in a callee's axiom, in a relation. Every
  other function value promises nothing. Each use of a function value reads
  that contract in one function:

  | Use | Function | Rule |
  |---|---|---|
  | Named as a value | `read_named_function` | States its relation once per query, and its definition where the function does not abort |
  | Passed for a parameter | `check_passed` | The parameter's `requires` imply its `requires`, and its `ensures` imply the parameter's |
  | Called | `check_called`, `assume_returned` | The call proves its `requires` and assumes its `ensures` |
  | Read where no function type states a `requires` | `check_read`, `check_passed` | Its `requires` hold for every argument |

  The definition of a named function is its contract as an axiom, and the
  relation holds only of a call that returned. So a function that may abort
  has a relation and no definition: its application is a term that nothing
  specifies, as its call in a specification is. `Callee.may_abort` decides
  that for a call and for a function named as a value, and
  `State.known_function` carries the answer with the contract. A lambda
  follows the same rule. Its definition and the facts of its application
  are those of its body where the body returns, so where the body may abort
  `Lambdas.read_lambda` states only the relation of the body, which a call
  that returned makes hold. The body was checked for the arguments of the
  lambda's domain: valid inputs that meet the `requires` of the parameter
  that the lambda is passed for. The definition is a term, so it holds of
  every argument, and the fact that the application is a value of its
  result type is stated under the domain: `fn(x) { x - 1 }` passed for a
  parameter that requires `x > 0` is `-1` at zero, and is a `UInt64` above
  it.

  `Lambdas.make_passed_values` checks each argument of a call against its
  parameter's contract: it runs a lambda's body against the contract, which
  it reads through `Callbacks.read_requires` and `Callbacks.read_ensures`,
  and gives every other value to `check_passed`. The state of `Callbacks`
  is one record, `context.callbacks`.
- **One function builds the frame that reads a callee's clause.**
  `Contracts.make_entry_frame` binds a clause's parameters to the arguments,
  and `Contracts.make_exit_frame` to the values at return, with the entry
  values as `old`. A call, a callback, a contract axiom and the clauses a
  method takes from its trait all read through them.
- **Each rule of the prover has one owner module, and each record of its
  state one owner.** `Reader`, `Calls`, `Loops` and `Lambdas` execute the
  MIR and call an owner at each statement, so a new rule edits its owner.
  An owner's state is an abstract type or a record of `State.context` that
  `for_prover_state.sh` lets only the owner use.

  | Module | Holds |
  |---|---|
  | `Query` | The query under construction |
  | `Facts` | The facts of a frame, the source of a clause, and the constructs that the prover cannot read |
  | `Encoding` | A type in the logic: its sort, its range, its constructors and fields, and the types of a frame's locals |
  | `Fixes` | The fixes that a diagnostic offers |
  | `Obligations` | The obligations of a run, and which of them it makes |
  | `Joins` | The join of the paths that meet |
  | `Cycles` | The recursion group and the proof group |
  | `Termination` | Measures, and the comparison of a recursive call |
  | `Contract_axioms` | The contract of a logic function as an axiom |
  | `Validity` | The invariant of a value, and each check of it |
  | `Callee` | The callee of a call: the definition that it runs, its contract, its substitutions and the key of its logic symbol |
  | `Callbacks` | A function value: its terms, its contract, and each use of it |
  | `Lending` | The contract of a lending method: where each clause holds, and the part as the caller left it |
  | `Laws` | The laws of a trait |

- **What holds for the length of a nested read is a field of the frame that
  the read receives.** A reader that needs such a fact takes it from its
  frame, and the frame that the caller keeps never had it, so nothing is
  set and restored and a reader cannot see the setting of another read.

  | Field of `State.frame` | Holds while |
  |---|---|
  | `is_ghost` | A specification, a proof block or an evaluated assertion is read |
  | `panics`, `can_declare_panic` | The code being read may panic, and may be given `uses Panic` as a fix |
  | `obligation_condition` | A clause that holds under a condition is read, so that an obligation made while reading it is one of that condition |
  | `requires_being_read` | One `requires` clause of the definition is read, so that a fix is placed before it |
  | `callees_whose_requires_are_read` | The `requires` of a callee are read, so that a call to the same callee inside them reads none |
  | `instantiating` | The contract of a callee is read at an instantiation, so that a nested reading at a larger instantiation stops |
  | `provided` | The body of a `provide` block is read |
  | `is_reading_callback` | An operand is read as a function to call or to pass, where a function parameter does not escape |
  | `validating` | The invariant of a type is read, so that a value of the same type inside it is not unfolded again |
  | `callbacks` | The parameters of a definition or of a clause are bound |

- **`Query` holds the query under construction.** Its declarations, facts,
  fresh names, scopes and posed obligations are fields of an abstract type,
  `context.query`, so no other module writes them: a module marks the facts
  with `Query.count_facts` and reads the ones added since, and a module that
  reads code under a binder takes the facts of that scope from
  `Query.run_in_scope`.
- **A term is built without the query.** The sort of a type is
  `Encoding.sort_of`, a function of the type. A symbol whose structure
  fixes its signature, such as `Capacity` of a type or `Apply` of a list of
  sorts, has it in `Signatures.find_signature`, and no reader declares it.
  `Logic.prune` reads such a symbol as declared, and `Logic.declare_derived`
  completes the pruned query of an obligation: a declaration for each such
  symbol that a fact or the goal names, and a datatype, with the
  constructors that `Encoding.list_constructors` gives, for each sort that
  a declaration, a bound variable, a constructor or a field names. It
  rejects a written declaration of a derived symbol, so each symbol has one
  source of its signature. A symbol that names a definition or a fresh
  value is declared by the module that makes it.
- **`Validity` decides each check of an invariant.** Every moment that
  obliges one calls `Validity.check_valid`, which first asks its record of
  the values already shown valid, so a value is proven once. A write
  through a passed place returns the end of the write, and the call ends it
  after its postconditions: an element is checked there, and a step's
  `self` is a value not known to be valid until then. Its state is one
  record, `context.validity`.
- **A call's callee is resolved once.** `Callee.resolve` turns the target
  that the MIR writes into the definition that runs, its contract, the
  substitution of each of its clauses, and the type arguments that key its
  logic symbol: a trait's own arguments, the type of `self`, and the
  method's. The reader resolves it before it reads the arguments, and the
  contract call, the callback rules, the costs, the cursor loop and the
  check of a restated contract all read that value. A capability's method
  is a definition like any other, so a callback that it takes has its
  contract.
- **`Lending` decides where each clause of a lending method holds.**
  `Lending.holds_where_lent` separates the clauses on the lent part from
  the clauses that hold when the lend ends, and the method's proof and
  every caller read a clause in the state that it names. A method's proof
  records each part it lends in `context.lending`, and `Translate` checks
  the method's own clauses and its trait's at each lent part and at each
  exit. `Calls.call_contract` gives a `mut` lend two moments: it assumes
  the clauses on the lent part where the method lends, and returns the end
  of the lend, which takes the part as the caller left it, checks its
  invariant, and assumes the other clauses. `visited` and `final(result)`
  are separate MIR nodes, and each reads its own field of the frame.
- **An obligation carries its refutation.** `Obligation.refutation` is the
  negated goal under the obligation's path condition, and no refutation
  for a goal of `false`, which only an unreachable path proves. `Prover`
  asks it of every obligation that the solver did not prove, whether Z3
  answered `sat` or `unknown`: a false goal needs a model of the facts,
  and Z3 builds none once a fact is quantified, as a callee's contract
  axiom is. A proven refutation is the verdict `Refuted`. The request is
  one run of Z3 with a tenth of the step limit: a refutation that fails
  makes Z3 search for a model until its steps run out, so its limit is a
  cost of every obligation that stays undecided.
- **The solver keeps Z3 running.** `Solver` starts one `z3 -in` process for
  each domain that solves, gives each query to an idle process, and sends
  `(reset)` after the answer, so a query costs no launch. A process that was
  reset answers as a new process does, in the same number of steps. Z3
  linked into the compiler does not: its contexts share state within one
  process, so a query solved beside another takes a different number of
  steps, and the step limit then decides differently from one run to the
  next.

### Documents

Each document has one job, and a fact is stated in one of them:

- **[SPECIFICATION.md](SPECIFICATION.md) and [PACKAGES.md](PACKAGES.md)
  define Truss,** its grammar and the rules of the language and of
  packages, **and [DESIGN.md](DESIGN.md) says why.** They describe the
  language, whether or not stage0 builds all of it yet.
- **This document holds the rules for working on stage0.**

Stage0 and the standard library have no documents of their own. Stage0's
code and interfaces describe it, and the standard library's signatures and
contracts describe it.

A design document describes the design as it is. How it got there belongs in
version control, in commit messages and pull request descriptions. A
document has no sections that list changes, an earlier version's behavior,
or the review that settled a question; when the design changes, the document is
rewritten to describe the new design.

A document records no measurement. A time or a size is true of one commit,
and a document that states one gives every later change something to measure
again. A measurement belongs in the commit message or the pull request
it explains.

### Comments

Code has no comments. Nothing checks a comment against the code it
describes, so the comment drifts. A reason, an invariant, or a trap is
stated instead by a name, by code that cannot be gotten wrong, or by a test
named after the failure it prevents. A rule of the language belongs in
[SPECIFICATION.md](SPECIFICATION.md). CI rejects a comment in any tracked
file with `stage0/tools/comments`. The tool also rejects a file type that it
has no comment syntax for, so a new type of file cannot add comments
unchecked.

### Module names

Code names each module by its path, such as `Resolve.Names` or
`Emit_c.Ir_builder`, so a reader finds a definition without searching for the
module a short name stands for. Code has no `open`: a name from another
module is qualified, as in `Facts.find_visible_type`, and no `open` can
shadow a name in scope. Code has no module alias either. Many modules share a name,
such as the scanner's `Names` and `Resolve.Names`, so an alias's short name
does not say which module it is. A library's main module exposes a
submodule with `module Names = Names`; that line is the library's
interface, not an alias.

An expression may open a module for its infix operators: `Logic`, or
Cmdliner's `Arg` or `Term`, as in `Logic.(a &&& b)`. Warnings 44 and 45
reject such an open when it shadows a name in scope. CI rejects every other
open, and every alias, with `stage0/tools/qualified_names`.

### Testing

Every stage of stage0 is tested the same way:

- **A test states its claim.** Each test gives a small input and asserts
  exact facts about the result: the tokens, a diagnostic's code and
  position, the text after applying a fix. Its name names the behavior it
  covers.
- **Tests are fast and deterministic.** No randomness, no large inputs, and
  no test cases generated by combining options, so the suite can run on
  every change. A test that takes over half a second is a defect: the
  harness prints each one with its time.
- **No golden files.** A golden file compares a whole dump of output, so it
  breaks when anything in the dump changes, whether or not the behavior it
  meant to check did, and it never says which fact mattered.
- **A fix is tested by applying it.** A test that expects a fix applies it,
  checks again, and asserts that the diagnostic is gone with no new one in
  its place. `Support.expect_diagnostic` does this for every diagnostic a
  test expects: it fails when the diagnostic offers a fix that the test
  does not give as `~fixed` or in `~alternatives`, so no fix goes untested.
  A test states a fix as its edit of the input, such as
  `~fixed:("own items", "items.copy()")`: the text the fix replaces, which
  occurs once in the input, and the text it writes there. A test whose
  input keeps a second error on purpose names its code in
  `~left_after_fix`.
- **Fuzzing and benchmarks are tools, not tests.** They live in
  `stage0/tools/` and are run by hand. Each problem a fuzzer finds becomes a
  focused test of its own.
- **Tests share one checked standard library.** A test that needs the
  standard library creates its database over the standard library's package
  database, a SQLite file in the user's cache that every test's database
  attaches read-only. A test must not give a new database the library's
  sources: that parses and checks the whole library again, so every such
  test gets slower each time the library grows. A test whose probe module
  must be in the standard package, such as one that calls an intrinsic,
  extends a copy of that package database with
  `Database.For_testing.extend_package`, which checks only the probe. Only
  `standard_library_tests` walks the whole library: for each module, one
  test checks and proves it, and one checks the invariants of its core
  forms and its MIR.
- **A test whose only claim is that it passes is written in Truss.** Each
  file under `stage0/test/codegen/modules/` is a module of tests. A file of
  `modules/library/` tests one module of the standard library and is named
  after it. The other directories, such as `modules/feature/` and
  `modules/owning/`, test the code generated for a construct. `module_tests`
  divides the modules by name into the shares that `TRUSS_TEST_SHARE` names, builds
  the tests of every module in its share into one program, and runs it. The
  `runtest` alias runs two shares in parallel. A new test therefore adds
  its code to one build and starts no build of its own. A test of a panic
  goes in the module `library.panics`: each of its tests must panic with a
  message that contains the test's name. A test written in OCaml that
  compiles a program of its own is for what a passing test cannot show: a
  diagnostic, the generated code, a reported source location, or a whole
  program's output.
- **A test's Truss source is a fixture file, not an OCaml string.** The
  text a test checks lives in `fixtures/<suite>/<name>.truss` beside the
  suite, where it can be read, edited, and renamed as Truss.
  `embed_fixtures` compiles each directory of fixtures into the module
  `Fixtures`, so the test names one as
  `Fixtures.Prover.addition_that_can_overflow`, and a fixture that is
  missing fails to compile. Text that is not a whole module stays in OCaml:
  a template with a hole that the test fills, a line given to the lexer or
  the parser, and a snippet of one or two lines.
- **Checks against the documents are tests,** as long as each one states a
  single property, such as "SPECIFICATION.md's keyword list matches the lexer's".
  Each example in the documents is tested once by each suite that can:
  `parser_documents_tests` parses it and checks the grammar accepts it,
  `documents_tests` checks and proves it, and `program_tests` runs its
  tests when it has some.
- **One test can be run alone.** With `TRUSS_TEST` set, a test executable
  runs only the tests whose names contain it, for working on one:
  `TRUSS_TEST=standard.text _build/default/stage0/test/standard_library_tests.exe`.
  A test must not depend on what an earlier test did, since `TRUSS_TEST`
  and `TRUSS_TEST_SHARE` run it without the tests before it. The harness
  restores the environment after each test, so a test sets or unsets the
  variables it needs and does not restore them itself.
- **A test keeps its share.** `TRUSS_TEST_SHARE=index/count` runs the tests
  whose names hash to `index`, so adding or removing a test moves no other
  test to another share.
