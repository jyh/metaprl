(*
 * Quotient type.
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
 * Author: Jason Hickey <jyh@cs.cornell.edu>
 * Mofidied by: Aleksey Nogin <nogin@cs.cornell.edu>
 *
 *)

extends Itt_equal
extends Itt_set
extends Itt_rfun
extends Itt_esquash

open Basic_tactics

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "quot"{'A; x, y. 'E['x; 'y]}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_quot

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- quot x1, y1: A1 // E1 = quot x2, y2. A2 // E2 in Ui
 * by quotientEquality x y z u v
 *
 * H >- A1 = A2 in Ui
 * H, x: A1, y: A1 >- E1[x, y] = E2[x, y] in Ui
 * H, x: A1 >- E1[x, x]
 * H, x: A1, y: A1, u: E1[x, y] >- E1[y, x]
 * H, x: A1, y: A1, z: A1, u: E1[x, y], v: E1[y, z] >- E1[x, z]
 *)
rule quotientEquality :
   sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   sequent { <H>; x: 'A1; y: 'A1 >- 'E1['x; 'y] = 'E2['x; 'y] in univ[i:l] } -->
   sequent { <H> >- "type"{.quot x1, y1: 'A1 // 'E1['x1; 'y1]} } -->
   sequent { <H> >- quot x1, y1: 'A1 // 'E1['x1; 'y1]
                   = quot x2, y2: 'A2 // 'E2['x2; 'y2]
                   in univ[i:l]
           }

(*
 * Typehood.
 *)
rule quotientType :
   sequent { <H> >- "type"{'A} } -->
   sequent { <H>; u: 'A; v: 'A >- "type"{'E['u; 'v]} } -->
   sequent { <H>; u: 'A >- 'E['u; 'u] } -->
   sequent { <H>; u: 'A; v: 'A; 'E['u; 'v] >- 'E['v; 'u] } -->
   sequent { <H>; u: 'A; v: 'A; w: 'A; 'E['u; 'v]; 'E['v; 'w] >- 'E['u; 'w] } -->
   sequent { <H> >- "type"{.quot x, y: 'A // 'E['x; 'y]} }

(*
 * H >- quot x, y: A // E ext a
 * by quotient_memberFormation
 *
 * H >- quot x, y: A // E = quot x, y: A // E in Ui
 * H >- A ext a
 *)
rule quotient_memberFormation :
   sequent { <H> >- "type"{(quot x, y: 'A // 'E['x; 'y])} } -->
   sequent { <H> >- 'A } -->
   sequent { <H> >- quot x, y: 'A // 'E['x; 'y] }

(*
 * H >- a1 = a2 in quot x, y: A // E
 * by quotient_memberWeakEquality
 *
 * H >- quot x, y: A // E = quot x, y: A // E in Ui
 * H >- x1 = a2 in A
 *)
rule quotient_memberWeakEquality :
   sequent { <H> >- "type"{(quot x, y: 'A // 'E['x; 'y])} } -->
   sequent { <H> >- 'a1 = 'a2 in 'A } -->
   sequent { <H> >- 'a1 = 'a2 in quot x, y: 'A // 'E['x; 'y] }

(*
 * H >- a1 = a2 in quot x, y: A // E
 * by quotient_memberEquality
 *
 * H >- a1 = a1 in quot x, y: A // E
 * H >- a2 = a2 in quot x, y: A // E
 * H >- [[ E[a1; a2] ]]
 *)
rule quotient_memberEquality :
   sequent { <H> >- 'a1 in quot x, y: 'A // 'E['x; 'y] } -->
   sequent { <H> >- 'a2 in quot x, y: 'A // 'E['x; 'y] } -->
   sequent { <H> >- esquash{'E['a1; 'a2]} } -->
   sequent { <H> >- 'a1 = 'a2 in quot x, y: 'A // 'E['x; 'y] }

(*
 * H, a: quot x, y: A // E, J[a] >- s[a] = t[a] in T[a]
 * by quotientElimination v w z
 *
 * H, a: quot x, y: A // E, J[a] >- T[a] = T[a] in Ui
 * H, a: quot x, y: A // E, J[a], v: A, w: A, z: E[v, w] >- s[v] = t[w] in T[v]
 *)
rule quotientElimination1 'H :
   sequent { <H>; a: quot x, y: 'A // 'E['x; 'y]; <J['a]> >- "type"{'T['a]} } -->
   sequent { <H>; a: quot x, y: 'A // 'E['x; 'y]; <J['a]>;
             v: 'A; w: 'A; 'E['v; 'w] >- 's['v] = 't['w] in 'T['v]
           } -->
   sequent { <H>; a: quot x, y: 'A // 'E['x; 'y]; <J['a]> >- 's['a] = 't['a] in 'T['a] }
(*
rule quotientElimination2 'H 'v 'w 'z :
   sequent { <H>; a: quot x, y: 'A // 'E['x; 'y]; <J['a]> >- "type"{'T['a]} } -->
   sequent { <H>; a: quot x, y: 'A // 'E['x; 'y];
             v: 'A; w: 'A; z: 'E['v; 'w]; <J['v]> >- 's['v] = 't['w] in 'T['v]
           } -->
   sequent { <H>; a: quot x, y: 'A // 'E['x; 'y]; <J['a]> >- 's['a] = 't['a] in 'T['a] }
*)
(*
 * H, x: a1 = a2 in quot x, y: A // E, J[x] >- T[x]
 * by quotient_equalityElimination v
 *
 * H, x: a1 = a2 in quot x, y: A // E, J[x], v: esquash(E[a, b]) >- T[x]
 *)
rule quotient_equalityElimination 'H :
   sequent { <H>; x: 'a1 = 'a2 in quot x, y: 'A // 'E['x; 'y]; <J['x]>; esquash{'E['a1; 'a2]} >- 'T['x] } -->
   sequent { <H>; x: 'a1 = 'a2 in quot x, y: 'A // 'E['x; 'y]; <J['x]> >- 'T['x] }

(*
 * H >- quot x1, y1: A1 // E1[x1; y1] <= quot x2, y2: A2 // E2[x2; y2]
 * by quotientSubtype
 *
 * H >- A1 <= A2
 * H, x1: A1, y1: A1 >- E1[x1; y1] => E2[x2; y2]
 * H >- quot x1, y1: A1 // E1[x1; y1] in type
 * H >- quot x2, y2: A2 // E2[x2; y2] in type
 *)
rule quotientSubtype :
   sequent { <H> >- \subtype{'A1; 'A2} } -->
   sequent { <H>; a1: 'A1; a2: 'A1 (* ; 'E1['a1; 'a2] *) >- 'E2['a1; 'a2] } -->
   sequent { <H> >- "type"{(quot x1, y1: 'A1 // 'E1['x1; 'y1])} } -->
   sequent { <H> >- "type"{(quot x2, y2: 'A2 // 'E2['x2; 'y2])} } -->
   sequent { <H> >- \subtype{ (quot x1, y1: 'A1 // 'E1['x1; 'y1]); (quot x2, y2: 'A2 // 'E2['x2; 'y2]) } };;

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val is_quotient_term : term -> bool
val dest_quotient : term -> var * var * term * term
val mk_quotient_term : var -> var -> term -> term -> term

topval quotientT : int -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
