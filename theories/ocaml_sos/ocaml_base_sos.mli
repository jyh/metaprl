(*
 * Basic definition for the operational semantics of
 * ocaml.  We define states as maps form "addresses", which
 * are just strings, to values.
 *)

include Ocaml

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

rewrite member_unfold :
   member{'S; 'e; 't} <--> equiv{'S; 'e; 'e; 't}

(*
 * Judgment:
 * Two expressions are functionally equivalent if they are equivalent
 * and they are both values.
 *)
declare value_equiv{'S; 'e1; 'e2; 't}
declare value_member{'S; 'e; 't}

rewrite value_member_unfold :
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
declare name_equiv{'S; 'n1; 'n2}

(*
 * Form:
 * "process" is a run of a program in a particular state
 * "value" is a process, but its evaluation does not modify the state
 * "state" projects the state component of a process
 * "expr" projects the program component
 * "expr_value" projects the program if it is a value
 *)
declare process{'S; 'e}
declare "value"{'S; 'e}
declare spread{'process; e, S. 'body['e; 'S]}
declare spread_value{'process; v, S. 'body['v; 'S]}
declare state{'S; 'e}
declare expr{'S; 'e}
declare expr_value{'S; 'e}

(*
 * Operations on states.
 *)
declare lookup{'S; 'n}
declare replace{'S; 'n; 'v}
declare allocate{'S; 'v}

rewrite state_unfold :
   state{'S; 'e} <--> spread{process{'S; 'e}; v, S2. 'S2}

rewrite expr_unfold :
   expr{'S; 'e} <--> spread{process{'S; 'e}; v, S2. 'v}

(************************************************************************
 * BASIC FACTS                                                          *
 ************************************************************************)

(*
 * Two equivalent values are equivalent.
 *)
axiom value_equiv_is_equiv 'H :
   sequent { 'H >- value_equiv{'S; 'e1; 'e2; 't} } -->
   sequent { 'H >- equiv{'S; 'e1; 'e2; 't} }

(*
 * A functional function application to a value is a value.
 *)
axiom functional_apply_value 'H 't1 :
   sequent { 'H >- value_equiv{'S; 'a1; 'a2; 't2} } -->
   sequent { 'H >- value_equiv{'S; 'f1; 'f2; functional{'t1; 't2}} } -->
   sequent { 'H >- value_equiv{'S; apply{'f1; 'a1}; apply{'f2; 'a2}; 't2} }

(*
 * $Log$
 * Revision 1.2  1998/06/01 13:56:52  jyh
 * Proving twice one is two.
 *
 * Revision 1.1  1998/04/29 14:49:43  jyh
 * Added ocaml_sos.
 *
 * Revision 1.1  1998/02/18 18:47:11  jyh
 * Initial ocaml semantics.
 *
 * Revision 1.1  1998/02/13 16:02:08  jyh
 * Partially implemented semantics for caml.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
