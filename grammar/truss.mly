/* The grammar from GRAMMAR.md, written for Menhir so that it can be checked
   for conflicts with `menhir --explain truss.mly`. Semantic actions are
   empty; this file checks the grammar's shape, not what it builds.

   The lexer is assumed to:
   - apply the line-break rule, emitting a single NEWLINE where the token
     before a line break can end a statement and the token after it can begin
     one, and a NEWLINE before EOF when the last token can end a statement.
     So no NEWLINE ever comes right after an opening `{` or before a closing
     `}`, and items inside braces are separated by NEWLINEs, not ended by
     them;
   - return the cost words (amortized, time, allocations, allocated_bytes,
     calls, O, finite, and potential) as ordinary LOWER or UPPER names. The
     rules below accept any name in their positions; the real parser checks
     the spelling;
   - return a whole string literal, interpolations included, as one STRING
     or TAGGED token. */

%token UPPER LOWER UNDERSCORE INTEGER FLOAT STRING TAGGED NEWLINE EOF

%token ANY ASSERT BREAK CAPABILITY CONTINUE COST DECREASES DERIVES ECHO ELSE
%token ENSURES EXISTS FALSE FN FOR FORALL IF IMPL IN INDIRECT INTERNAL INVARIANT IS LAW LENDS
%token LET MATCH MUT OPAQUE OWN PARALLEL PROOF PROVIDE PUBLIC REQUIRES RETURN
%token SELF SELF_TYPE TEST THEOREM TODO TRAIT TRUE TYPE UNREACHABLE USE USES
%token VAR WHILE WITH YIELD YIELDS

%token LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE COMMA COLON COLONCOLON
%token DOT DOTDOT DOTDOTEQ ARROW FATARROW QUESTION BAR
%token EQ PLUSEQ MINUSEQ STAREQ SLASHEQ PERCENTEQ AMPEQ BAREQ CARETEQ SHLEQ SHREQ
%token PLUS MINUS STAR SLASH PERCENT EQEQ NEQ LT LE GT GE ANDAND OROR IMPLIES
%token BANG AMP CARET TILDE SHL SHR

%start <unit> file

%%

/* Helpers */

comma_list(X):
  | { () }
  | X { () }
  | X COMMA comma_list(X) { () }

comma_list1(X):
  | X { () }
  | X COMMA comma_list(X) { () }

newline_opt:
  | { () }
  | NEWLINE { () }

newline_separated(X):
  | { () }
  | newline_separated1(X) { () }

newline_separated1(X):
  | X { () }
  | X NEWLINE newline_separated1(X) { () }

/* Files and definitions */

file:
  | list(top_item) EOF { () }

top_item:
  | use_declaration NEWLINE { () }
  | definition NEWLINE { () }

use_declaration:
  | USE module_path { () }

module_path:
  | LOWER { () }
  | module_path COLONCOLON LOWER { () }

qualified_upper:
  | UPPER { () }
  | module_path COLONCOLON UPPER { () }

definition:
  | visibility_opt function_definition { () }
  | visibility_opt type_definition { () }
  | visibility_opt trait_definition { () }
  | impl_definition { () }
  | visibility_opt capability_definition { () }
  | visibility_opt constant { () }
  | test_definition { () }
  | visibility_opt theorem_definition { () }
  | law_proof { () }

visibility_opt:
  | { () }
  | PUBLIC { () }
  | PUBLIC OPAQUE { () }
  | INTERNAL { () }

/* Functions */

function_definition:
  | FN function_name generics_opt parameters result_opt list(clause)
    newline_opt block { () }

function_name:
  | LOWER { () }
  | type_head DOT LOWER { () }

type_head:
  | qualified_upper generics_opt { () }

parameters:
  | LPAREN comma_list(parameter) RPAREN { () }

parameter:
  | mode_opt SELF { () }
  | LOWER COLON mode_opt type_expression default_opt { () }

default_opt:
  | { () }
  | EQ expression { () }

mode_opt:
  | { () }
  | MUT { () }
  | OWN { () }

result_opt:
  | { () }
  | ARROW type_expression { () }
  | YIELDS mode_opt type_expression { () }
  | LENDS mode_opt type_expression { () }

signature:
  | FN LOWER generics_opt parameters result_opt list(clause) { () }

/* Clauses */

clause:
  | USES capability_list { () }
  | REQUIRES expression { () }
  | ENSURES expression { () }
  | DECREASES separated_nonempty_list(COMMA, expression) { () }
  | COST cost { () }

capability_list:
  | separated_nonempty_list(COMMA, path_type) { () }

/* A cost clause starts with one or two words: `time ...`, `calls(...) ...`,
   or `amortized time ...`. Whether a second word is a resource or `finite` is
   decided by the token after it, so the rules are factored to need only one
   token of lookahead. */
cost:
  | LOWER cost_after_word { () }

cost_after_word:
  | marked_bound { () }
  | LPAREN call_target RPAREN bound { () }
  | LOWER cost_after_second_word { () }

cost_after_second_word:
  | { () }
  | marked_bound { () }
  | LOWER { () }
  | LPAREN call_target RPAREN bound { () }

call_target:
  | LOWER { () }
  | path_type { () }
  | path_type DOT LOWER { () }

bound:
  | marked_bound { () }
  | LOWER { () }

marked_bound:
  | UPPER LPAREN expression RPAREN { () }
  | LE expression { () }
  | EQEQ expression { () }

/* Type definitions */

type_definition:
  | TYPE UPPER generics_opt type_body list(type_clause) { () }

type_body:
  | fields { () }
  | EQ variants { () }
  | EQ TODO { () }

fields:
  | LPAREN comma_list(field) RPAREN { () }

field:
  | LOWER COLON type_expression default_opt { () }

variants:
  | separated_nonempty_list(BAR, variant) { () }
  | BAR separated_nonempty_list(BAR, variant) { () }

variant:
  | UPPER { () }
  | UPPER fields { () }
  | INDIRECT UPPER { () }
  | INDIRECT UPPER fields { () }

type_clause:
  | INVARIANT expression { () }
  | DERIVES separated_nonempty_list(COMMA, path_type) { () }
  | COST LOWER expression { () }

/* Types */

type_expression:
  | path_type { () }
  | SELF_TYPE { () }
  | SELF_TYPE DOT UPPER { () }
  | UPPER DOT UPPER { () }
  | ANY path_type { () }
  | function_type { () }
  | LPAREN function_type nonempty_list(function_type_clause) RPAREN { () }

path_type:
  | qualified_upper { () }
  | qualified_upper type_arguments { () }

type_arguments:
  | LBRACKET comma_list1(type_argument) RBRACKET { () }

type_argument:
  | type_expression { () }
  | INTEGER { () }
  | LOWER { () }
  | UPPER EQ type_expression { () }

function_type:
  | FN LPAREN comma_list(function_type_parameter) RPAREN { () }
  | FN LPAREN comma_list(function_type_parameter) RPAREN ARROW type_expression { () }

function_type_parameter:
  | mode_opt type_expression { () }

function_type_clause:
  | USES capability_list { () }
  | COST cost { () }

generics_opt:
  | { () }
  | LBRACKET comma_list1(generic_parameter) RBRACKET { () }

generic_parameter:
  | UPPER { () }
  | UPPER COLON bound_list { () }
  | LOWER COLON type_expression { () }
  | CAPABILITY UPPER { () }

bound_list:
  | separated_nonempty_list(PLUS, path_type) { () }

/* Traits, implementations, and capabilities */

trait_definition:
  | TRAIT UPPER generics_opt supertraits_opt LBRACE trait_members RBRACE { () }

supertraits_opt:
  | { () }
  | COLON bound_list { () }

/* A method declared without a body and a method whose body starts on the
   next line both begin `signature NEWLINE`. The token after the NEWLINE
   decides: `{` starts the body, and anything else starts the next member. */
trait_members:
  | { () }
  | trait_members1 { () }

trait_members1:
  | trait_member { () }
  | trait_member NEWLINE trait_members1 { () }
  | signature { () }
  | signature NEWLINE trait_members1 { () }
  | signature NEWLINE block { () }
  | signature NEWLINE block NEWLINE trait_members1 { () }

trait_member:
  | signature block { () }
  | TYPE UPPER { () }
  | TYPE UPPER COLON bound_list { () }
  | LAW LOWER parameters list(law_requires) newline_opt block { () }

law_requires:
  | REQUIRES expression { () }

impl_definition:
  | IMPL path_type FOR type_head option(impl_uses) newline_opt
    LBRACE newline_separated(impl_item) RBRACE { () }

impl_uses:
  | USES capability_list { () }

impl_item:
  | signature newline_opt block { () }
  | TYPE UPPER EQ type_expression { () }

capability_definition:
  | CAPABILITY UPPER LBRACE newline_separated(signature) RBRACE { () }

/* Constants, tests, theorems, and proofs */

constant:
  | LET constant_name COLON type_expression EQ expression { () }

constant_name:
  | LOWER { () }
  | type_head DOT LOWER { () }

test_definition:
  | TEST STRING newline_opt block { () }
  | TEST STRING USES capability_list newline_opt block { () }

theorem_definition:
  | THEOREM LOWER generics_opt parameters list(clause) newline_opt block { () }

law_proof:
  | PROOF path_type DOT LOWER FOR type_expression newline_opt block { () }

/* Statements and blocks */

block:
  | LBRACE newline_separated(statement) RBRACE { () }

statement:
  | LET pattern annotation_opt EQ expression else_opt { () }
  | VAR pattern annotation_opt EQ expression else_opt { () }
  | expression { () }
  | expression assignment_operator expression { () }
  | FOR pattern IN expression list(loop_clause) newline_opt block { () }
  | WHILE expression list(loop_clause) newline_opt block { () }
  | PARALLEL block { () }
  | PARALLEL FOR pattern IN expression list(loop_clause) newline_opt block { () }
  | PROOF block { () }
  | ASSERT expression { () }
  | YIELD expression { () }

annotation_opt:
  | { () }
  | COLON type_expression { () }

else_opt:
  | { () }
  | ELSE block { () }

assignment_operator:
  | EQ { () } | PLUSEQ { () } | MINUSEQ { () } | STAREQ { () } | SLASHEQ { () }
  | PERCENTEQ { () } | AMPEQ { () } | BAREQ { () } | CARETEQ { () }
  | SHLEQ { () } | SHREQ { () }

loop_clause:
  | INVARIANT expression { () }
  | DECREASES separated_nonempty_list(COMMA, expression) { () }

/* Expressions */

expression:
  | ECHO expression { () }
  | RETURN { () }
  | RETURN expression { () }
  | implication { () }
  | bitwise { () }

/* A quantifier's body runs to the end of the expression, so a quantifier can
   only be the last operand of `&&`, `||`, or `==>`. Keeping `quantified`
   apart from `logical` stops anything from following a quantifier, so the
   body is never cut short. */
implication:
  | implication_operand { () }
  | logical IMPLIES implication_operand { () }

implication_operand:
  | logical { () }
  | quantified { () }

quantified:
  | quantifier { () }
  | comparison ANDAND quantifier { () }
  | and_chain ANDAND quantifier { () }
  | comparison OROR quantifier { () }
  | or_chain OROR quantifier { () }

quantifier:
  | FORALL binder FATARROW expression { () }
  | EXISTS binder FATARROW expression { () }

binder:
  | pattern IN expression { () }
  | LOWER COLON type_expression { () }

logical:
  | comparison { () }
  | and_chain { () }
  | or_chain { () }

and_chain:
  | comparison ANDAND comparison { () }
  | and_chain ANDAND comparison { () }

or_chain:
  | comparison OROR comparison { () }
  | or_chain OROR comparison { () }

comparison:
  | range { () }
  | range comparison_operator range { () }
  | range IS pattern { () }

comparison_operator:
  | EQEQ { () } | NEQ { () } | LT { () } | LE { () } | GT { () } | GE { () }

range:
  | additive { () }
  | additive DOTDOT additive { () }
  | additive DOTDOTEQ additive { () }

additive:
  | multiplicative { () }
  | additive PLUS multiplicative { () }
  | additive MINUS multiplicative { () }

multiplicative:
  | prefix { () }
  | multiplicative STAR prefix { () }
  | multiplicative SLASH prefix { () }
  | multiplicative PERCENT prefix { () }

bitwise:
  | and_bits { () }
  | or_bits { () }
  | xor_bits { () }
  | shift_bits { () }

and_bits:
  | prefix AMP prefix { () }
  | and_bits AMP prefix { () }

or_bits:
  | prefix BAR prefix { () }
  | or_bits BAR prefix { () }

xor_bits:
  | prefix CARET prefix { () }
  | xor_bits CARET prefix { () }

shift_bits:
  | prefix SHL prefix { () }
  | prefix SHR prefix { () }
  | shift_bits SHL prefix { () }
  | shift_bits SHR prefix { () }

prefix:
  | MINUS prefix { () }
  | BANG prefix { () }
  | TILDE prefix { () }
  | MUT postfix { () }
  | OWN postfix { () }
  | ANY postfix { () }
  | postfix { () }

postfix:
  | primary { () }
  | postfix DOT LOWER { () }
  | postfix DOT UPPER { () }
  | postfix LBRACKET brackets RBRACKET { () }
  | postfix LPAREN comma_list(argument) RPAREN { () }
  | postfix QUESTION { () }
  | postfix WITH LPAREN comma_list(update) RPAREN { () }

brackets:
  | comma_list1(bracket_item) { () }
  | DOTDOT { () }
  | DOTDOT additive { () }
  | DOTDOTEQ additive { () }
  | additive DOTDOT { () }

bracket_item:
  | expression { () }
  | UPPER EQ type_expression { () }

argument:
  | expression { () }
  | LOWER COLON expression { () }

update:
  | update_path { () }
  | update_path COLON expression { () }

update_path:
  | LOWER { () }
  | update_path DOT LOWER { () }

primary:
  | INTEGER { () } | FLOAT { () } | STRING { () } | tagged_string { () }
  | TRUE { () } | FALSE { () } | TODO { () } | UNREACHABLE { () }
  | BREAK { () } | CONTINUE { () } | SELF { () } | SELF_TYPE { () }
  | LOWER { () }
  | qualified_upper { () }
  | module_path COLONCOLON LOWER { () }
  | LPAREN expression RPAREN { () }
  | LBRACKET comma_list(expression) RBRACKET { () }
  | LBRACKET COLON RBRACKET { () }
  | LBRACKET map_entries RBRACKET { () }
  | lambda { () }
  | if_expression { () }
  | match_expression { () }
  | provide_expression { () }
  | block { () }

map_entries:
  | map_entry { () }
  | map_entry COMMA { () }
  | map_entry COMMA map_entries { () }

map_entry:
  | expression COLON expression { () }

lambda:
  | FN LPAREN comma_list(pattern) RPAREN block { () }

if_expression:
  | IF expression newline_opt block { () }
  | IF expression newline_opt block ELSE block { () }
  | IF expression newline_opt block ELSE if_expression { () }

match_expression:
  | MATCH separated_nonempty_list(COMMA, expression) newline_opt
    LBRACE newline_separated(arm) RBRACE { () }

arm:
  | separated_nonempty_list(COMMA, pattern) guard_opt FATARROW statement { () }

guard_opt:
  | { () }
  | IF expression { () }

provide_expression:
  | PROVIDE separated_nonempty_list(COMMA, expression) newline_opt block { () }

tagged_string:
  | TAGGED { () }
  | module_path COLONCOLON TAGGED { () }

/* Patterns */

pattern:
  | separated_nonempty_list(BAR, pattern_primary) { () }

pattern_primary:
  | UNDERSCORE { () }
  | range_end { () }
  | range_end DOTDOT range_end { () }
  | range_end DOTDOTEQ range_end { () }
  | qualified_upper { () }
  | qualified_upper pattern_fields { () }
  | pattern_fields { () }

range_end:
  | literal_pattern { () }
  | constant_reference { () }

/* A bare LOWER is a constant if one is in scope and otherwise a binding;
   name resolution decides, so the parser builds the same node for both. */
constant_reference:
  | LOWER { () }
  | module_path COLONCOLON LOWER { () }
  | qualified_upper DOT LOWER { () }

literal_pattern:
  | INTEGER { () }
  | MINUS INTEGER { () }
  | TRUE { () }
  | FALSE { () }
  | STRING { () }
  | tagged_string { () }

pattern_fields:
  | LPAREN comma_list(pattern_field) RPAREN { () }

pattern_field:
  | LOWER COLON pattern { () }
  | pattern { () }
  | DOTDOT { () }
