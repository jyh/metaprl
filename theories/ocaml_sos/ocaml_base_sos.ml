(*
 * Basic definition for the operational semantics of
 * ocaml.  We define states as maps form "addresses", which
 * are just strings, to values.
 *)

include Ocaml

open Nl_debug
open Printf

let _ =
   if !debug_load then
      eprintf "Loading Ocaml_base_sos%t" eflush

(*
 * Extract for equivalences.
 *)
declare it

(*
 * Term:
 * The address of a value.
 *)
declare address[@name:s]

(*
 * Type:
 * A function belongs to type functional{'t1; 't2} if it
 * belongs to fun{'t1; 't2} and for any argument in 't1,
 * the application of the function does not modify the state.
 *)
declare functional{'t1; 't2}

(*
 * Judgment:
 * Two expressions are equivalent if their evaluation from the same
 * state produces the same value and the same state.
 *)
declare equiv{'S; 'e1; 'e2; 't}
declare member{'S; 'e; 't}

primrw member_unfold :
   member{'S; 'e; 't} <--> equiv{'S; 'e; 'e; 't}

(*
 * Judgment:
 * Two expressions are functionally equivalent if they are equivalent
 * and they are both values.
 *)
declare value_equiv{'S; 'e1; 'e2; 't}
declare value_member{'S; 'e; 't}

primrw value_member_unfold :
   value_member{'S; 'e; 't} <--> value_equiv{'S; 'e; 'e; 't}

(*
 * Judgment:
 * Untyped value judgment.
 *)
declare is_value{'S; 'e}

(*
 * Judgment:
 * t is a valid type.
 *)
declare is_type{'t}

(*
 * Equivalence of names.
 *)
declare lid_equiv{'n1; 'n2}

(*
 * Equivalence of names.
 *)
declare name_equiv{'S; 'n1; 'n2}

(*
 * Form:
 * This is a program run.  It pairs an expression
 * with an initial state.
 *)
declare process{'S; 'e}

(*
 * Form:
 * This program is a value in state 'S;
 *)
declare "value"{'S; 'e}

(*
 * Combinator:
 * Evaluate a run to a value and separate the state from the value.
 *)
declare spread{'process; e, S. 'body['e; 'S]}
declare spread_value{'process; v, S. 'body['v; 'S]}
declare state{'S; 'e}
declare expr{'S; 'e}
declare expr_value{'S; 'e}

primrw state_unfold :
   state{'S; 'e} <--> spread{process{'S; 'e}; v, S2. 'S2}

primrw expr_unfold :
   expr{'S; 'e} <--> spread{process{'S; 'e}; v, S2. 'v}

primrw expr_value_unfold :
   expr_value{'S; 'e} <--> spread{process{'S; 'e}; v, S2. 'v}

(*
 * Operations on states.
 *)
declare lookup{'S; 'n}
declare replace{'S; 'n; 'v}
declare allocate{'S; 'v}

(************************************************************************
 * BASIC FACTS                                                          *
 ************************************************************************)

(*
 * Two equivalent values are equivalent.
 *)
prim value_equiv_is_equiv 'H :
   sequent { 'H >- value_equiv{'S; 'e1; 'e2; 't} } -->
   sequent { 'H >- equiv{'S; 'e1; 'e2; 't} } =
   it

(*
 * A functional function application to a value is a value.
 *)
prim functional_apply_value 'H 't1 :
   sequent { 'H >- value_equiv{'S; 'a1; 'a2; 't2} } -->
   sequent { 'H >- value_equiv{'S; 'f1; 'f2; functional{'t1; 't2}} } -->
   sequent { 'H >- value_equiv{'S; apply{'f1; 'a1}; apply{'f2; 'a2}; 't2} } =
   it

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
