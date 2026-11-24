type root =
  | Self
  | Named of string
  | Unnamed of Core.origin
  | Temporary
  | Constant of Path.t
  | Environment

type step = Field of string | Indexed
type place = { root : root; steps : step list }
type verb = Be_used | Be_passed_mut | Be_assigned | Be_moved
type lender = Loop | Provide_block | Rest_of_statement | Earlier_operand | Alias of root

type loan = {
  at : Core.origin;
  place : place;
  is_mut : bool;
  lender : lender;
  through : place option;
  verb : verb;
}

type copy = { moved : Core.origin; own_keyword : (Core.origin * Core.origin) option }
type dangling_act = Is | Returns | Stores_in of root | Lends
type dangling_view = Captured_variables | Temporary_view | View_of of root
type scrutinee = { scrutinee : root; written : Core.origin; is_part : bool }

type t =
  | Conflicting_loan of loan
  | Mutated_while_lent of loan
  | Mutated_while_viewed of { at : Core.origin; place : place; verb : verb; holder : root }
  | Moved_out_of_lent of { at : Core.origin; copy : copy option }
  | Arguments_overlap of {
      at : Core.origin Description.range;
      exclusive : place;
      also : place;
      call : Core.origin;
      is_yielded : bool;
    }
  | View_argument_overlap of {
      at : Core.origin Description.range;
      passed : place;
      call : Core.origin;
    }
  | Temporary_dropped_while_viewed of { at : Core.origin; holder : string option }
  | Dropped_while_viewed of { at : Core.origin; owner : root; holder : string option }
  | Lent_part_bound of { at : Core.origin; copy : copy option }
  | Capturing_lambda_stored of { at : Core.origin }
  | Unowned_function_stored of { at : Core.origin; viewed : place }
  | Dangling_view of {
      at : Core.origin;
      act : dangling_act;
      viewed : dangling_view;
      is_constant : bool;
    }
  | Returned_view_of_implementation of { at : Core.origin }
  | Stored_view_in_implementation of { at : Core.origin; viewed : root }
  | Self_referential_store of { at : Core.origin; root : root }
  | Stored_view_of_borrowed of { at : Core.origin; parameter : root; holder : root }
  | Lent_owned_part of { at : Core.origin; part : root }
  | Lent_other_parameter of { at : Core.origin; root : root }
  | Branch_data_race of { at : Core.origin; schedule : Language.Loop_mode.t; place : place }
  | Iteration_data_race of { at : Core.origin; schedule : Language.Loop_mode.t }
  | Lent_element_race of {
      at : Core.origin;
      schedule : Language.Loop_mode.t;
      collection : Types.ty option;
    }
  | Pulled_view of { at : Core.origin; element : Types.ty }
  | Lent_mut_in_variant of { at : Core.origin Description.range; variant : string }
  | Needs_lent_mut of { at : Core.origin; place : place; copy : copy option }
  | Returned_view_of_scrutinee of {
      at : Core.origin;
      place : place;
      scrutinee : scrutinee;
      copy : copy option;
    }
  | Returned_unowned of {
      at : Core.origin;
      place : place;
      views_literal : bool;
      copy : copy option;
    }
  | Moved_element of { at : Core.origin; place : place; copy : copy option }
  | Moved_constant of { at : Core.origin; place : place; copy : copy option }
  | Moved_literal_view of { at : Core.origin; place : place; copy : copy option }
  | Moved_view_of_scrutinee of {
      at : Core.origin;
      place : place;
      scrutinee : scrutinee;
      copy : copy option;
    }
  | Moved_view of { at : Core.origin; place : place; copy : copy option }
  | Needs_own_keyword of { at : Core.origin; place : place; copy : copy option }
  | Use_after_move of { at : Core.origin; place : place; moved : Core.origin; copy : copy option }
  | Not_reinitialized_at_return of { at : Core.origin; moved : Core.origin; place : place }
  | Not_reinitialized_at_scope_end of { moved : Core.origin; place : place }
  | Not_reinitialized_in_branch of { moved : Core.origin; place : place }
  | Undeclared_change of {
      at : Core.origin;
      function_ : Path.t;
      parameter : string;
      fields : string list;
      last_entry : Core.origin option;
    }

val describe : t -> Nodes.description
val list_examples : Diagnostic.Code.ownership -> t list
