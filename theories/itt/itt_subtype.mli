(*
 * Subtype type.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
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
 *
 *)

extends Itt_equal
extends Itt_struct

open Basic_tactics

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare \subtype{'A; 'B}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_subtype

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext subtype(A; B)
 * by subtypeFormation
 * H >- Ui ext A
 * H >- Ui ext B
 *)
rule subtypeFormation :
   sequent { <H> >- univ[i:l] } -->
   sequent { <H> >- univ[i:l] } -->
   sequent { <H> >- univ[i:l] }

(*
 * H >- subtype(A1; B1) = subtype(A2; B2) in Ui
 * by subtypeEquality
 *
 * H >- A1 = A2 in Ui
 * H >- B1 = B2 in Ui
 *)
rule subtypeEquality :
   sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   sequent { <H> >- 'B1 = 'B2 in univ[i:l] } -->
   sequent { <H> >- \subtype{'A1; 'B1} = \subtype{'A2; 'B2} in univ[i:l] }

rule subtypeType :
   sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- "type"{'B} } -->
   sequent { <H> >- "type"{.'A subtype 'B} }

rule subtypeTypeRight 'B :
   sequent { <H> >- 'A subtype 'B } -->
   sequent { <H> >- "type"{'A} }

rule subtypeTypeLeft 'A :
   sequent { <H> >- 'A subtype 'B } -->
   sequent { <H> >- "type"{'B} }

(*
 * H >- subtype(A; B) ext it
 * by subtype_axiomFormation
 *
 * H >- A = A in Ui
 * H; x: A; y: A; x = y in A >- x = y in B
 *)
rule subtype_axiomFormation :
   sequent { <H> >- "type"{'A} } -->
   sequent { <H>; x: 'A >- 'x in 'B } -->
   sequent { <H> >- 'A subtype 'B }

(*
 * H >- it = it in subtype(A; B)
 * by subtype_axiomEquality
 *
 * H >- subtype(A; B)
 *)
rule subtype_axiomEquality :
   sequent { <H> >- 'A subtype 'B } -->
   sequent { <H> >- it in 'A subtype 'B }

(*
 * H, x: subtype(A; B); J[x] >- C[x]
 * by subtypeElimination
 *
 * H, x: subtype(A; B); J[it] >- C[it]
 *)
rule subtypeElimination 'H :
   sequent { <H>; 'A subtype 'B; <J[it]> >- 'C[it] } -->
   sequent { <H>; x: 'A subtype 'B; <J['x]> >- 'C['x] }

(*
 * H >- x = y in B
 * by subtypeElimination2 A
 *
 * H >- x = y in A
 * H >- subtype(A; B)
 *)
rule subtypeElimination2 'H 'a 'b :
   sequent { <H>; x: 'A subtype 'B; <J['x]> >- 'a='b in 'A } -->
   sequent { <H>; x: 'A subtype 'B; <J['x]>; 'a = 'b in 'B >- 'C['x] } -->
   sequent { <H>; x: 'A subtype 'B; <J['x]> >- 'C['x] }

(************************************************************************
 * RESOURCE                                                             *
 ************************************************************************)

(*
 * Define a resource to keep track of proofs of subtyping.
 * This resource provides tactics to prove subtyping goals.
 * These tactics take transitivity into account, and try
 * to construct an optimal subtype chain.
 *)

(*
 * This is what is supplied to the resource.
 *)
type sub_info_type = (term * term) list * tactic

type sub_resource_info =
   LRSubtype of sub_info_type
 | RLSubtype of sub_info_type
 | DSubtype of sub_info_type

(*
 * The resource itself.
 *)
resource (sub_resource_info, tactic) sub

topval subtypeT : term -> tactic

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val is_subtype_term : term -> bool
val dest_subtype : term -> term * term
val mk_subtype_term : term -> term -> term

topval type_subtype_leftT : term -> tactic
topval type_subtype_rightT : term -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
