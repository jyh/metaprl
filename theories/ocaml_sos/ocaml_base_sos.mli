(*
 * Basic definition for the operational semantics of
 * ocaml.  We define states as maps form "addresses", which
 * are just strings, to values.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of Nuprl-Light, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 1998 Jason Hickey, Cornell University
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 * 
 * Author: Jason Hickey
 * jyh@cs.cornell.edu
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
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
