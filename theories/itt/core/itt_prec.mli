(*
 * PArameterized recursive type.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/htmlman/default.html or visit http://metaprl.org/
 * for more information.
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
extends Itt_subtype
extends Itt_dfun
extends Itt_prod

open Lm_symbol

open Refiner.Refiner.TermType

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*
 * Parameterized recursive type has an additional
 * argument x, with initial value a.
 *)
declare "prec"{T, x. 'B['T; 'x]; 'a}
declare precind{'a; p, h. 'g['p; 'h]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite reducePrecind : precind{'a; p, h. 'g['p; 'h]} <-->
   'g[lambda{a. precind{'a; p, h. 'g['p; 'h]}}; 'a]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- prec(A1, x1. B1[A1; x1]; a1) = prec(A2, x2. B2[A2; x2]; a2) in Ui
 * by precEquality A
 *
 * H >- a1 = a2 in A
 * H; x: A; T: A -> Ui >- B1[T; x] = B2[T; x] in Ui
 * H; P1: A -> Ui; P2: A -> Ui; z: x:A -> y: P1 x -> (y in P2 x); x:A; y: B1[P1; x]
 *   >- y = y in B2[P2; x]
 *)
rule precEquality 'A :
   sequent { <H> >- 'a1 = 'a2 in 'A } -->
   sequent { <H>; x: 'A; T: 'A -> univ[i:l] >- 'B1['T; 'x] = 'B2['T; 'x] in univ[i:l] } -->
   sequent { <H>;
             P1: 'A -> univ[i:l];
             P2: 'A -> univ[i:l];
             z: x:'A -> \subtype{('P1 'x); ('P2 'x)};
             x: 'A;
             y: 'B1['P1; 'x]
           >- 'y = 'y in 'B1['P2; 'x]
           } -->
   sequent { <H> >- "prec"{A1, x1. 'B1['A1; 'x1]; 'a1}
                   = "prec"{A2, x2. 'B2['A2; 'x2]; 'a2}
                   in univ[i:l]
           }

(*
 * H >- prec(T, x. B[T; x]; a) ext t
 * by precMemberFormation
 *
 * H >- B[lambda(a. prec(T, x. B[T; x])); a]
 * H >- prec(T, x. B[T; x]; a) = prec(T, x. B[T; x]; a) in type
 *)
rule precMemberFormation :
   sequent { <H> >- 'B[lambda{z. "prec"{T, x. 'B['T; 'x]; 'z}}; 'a] } -->
   sequent { <H> >- "type"{("prec"{T, x. 'B['T; 'x]; 'a})} } -->
   sequent { <H> >- "prec"{T, x. 'B['T; 'x]; 'a} }

(*
 * H >- a1 = a2 in prec(T, x. B[T; x]. a)
 * by precMemberEquality
 *
 * H >- prec(T, x. B[T; x]. a) = prec(T, x. B[T; x]. a) in type
 * H >- a1 = a2 in B[lambda(a. prec(T, x. B[T; x]); a); a]
 *)
rule precMemberEquality :
   sequent { <H> >- "type"{("prec"{T, x. 'B['T; 'x]; 'a})} } -->
   sequent { <H> >- 'a1 = 'a2 in 'B[lambda{z. "prec"{T, x. 'B['T; 'x]; 'z}}; 'a] } -->
   sequent { <H> >- 'a1 = 'a2 in "prec"{T, x. 'B['T; 'x]; 'a} }

(*
 * H; r: prec(T, x. B[T; x]; a); J[r] >- T[a]
 * by precElimination lambda(z. T[z]) A Z u h y
 *
 * H; r: prec(T, x. B[T; x]; a); J[r] >- a = a in A
 * H; r: prec(T, x. B[T; x]; a); J[r]; Z: A -> Ui
 *   u: p: (a: A * Z a) -> (p = p in a: A * prec(T, x. B[T; x]; a);
 *   h: p: (a: A * Z a) -> G[p];
 *   p: a: A * B[Z, a]
 * >- T[p]
 *)
rule precElimination 'H lambda{z. 'G['z]} 'A univ[i:l] :
   sequent { <H>; r: "prec"{T, x. 'B['T; 'x]; 'a}; <J['r]> >- 'a = 'a in 'A } -->
   sequent { <H>; r: "prec"{T, x. 'B['T; 'x]; 'a}; <J['r]>;
      Z: 'A -> univ[i:l];
      u: \subtype{(a: 'A * 'Z 'a); (a: 'A * "prec"{T, x. 'B['T; 'x]; 'a})};
      h: p: (a: 'A * 'Z 'a) -> 'G['p];
      p: a: 'A * 'B['Z; 'a]
   >- 'G['p]
   } -->
   sequent { <H>; r: "prec"{T, x. 'B['T; 'x]; 'a}; <J['r]> >- 'G['a] }

(*
 * H; r: prec(T, x. B[T; x]; a); J[r] >- T[r]
 * by precUnrollElimination y u
 *
 * H; r: prec(T, x. B[T; x]; a); J[r];
 *   y: B[lambda(a. prec(T, x. B[T; x]); a); a];
 *   u: r = y in B[lambda(a. prec(T, x. B[T; x]); a); a]
 *   >- T[y]
 *)
rule precUnrollElimination 'H :
   sequent { <H>; r: "prec"{T, x. 'B['T; 'x]; 'a}; <J['r]>;
             y: 'B[lambda{z. "prec"{T, x. 'B['T; 'x]; 'z}}; 'a];
             u: 'r = 'y in 'B[lambda{z. "prec"{T, x. 'B['T; 'x]; 'z}}; 'a]
             >- 'G['y]
           } -->
   sequent { <H>; r: "prec"{T, x. 'B['T; 'x]; 'a}; <J['r]> >- 'G['r] }

(*
 * H >- precind(r1; h1, z1. t1[r1, z1]) = precind(r2; h2, z2. t2[r2; z2]) in S[r1]
 * by precindEquality lambda(x. S[x]) (a:A * prec(T, y. B[T; y]; a))
 *
 * H >- r1 = r2 in a:A * prec(T, y. B[T, y]; a)
 * H; Z: A -> Ui;
 *   u: z: (a:A * Z a) -> (z = z in a:A * prec(T, x. B[t, x]; a));
 *   h: z: (a:A * Z a) -> S[z];
 *   z: a: A * B[Z; a]
 *   >- t1[h; z] = t2[h; z] in S[z]
 *)
rule precindEquality lambda{x. 'S['x]} (a:'A * "prec"{T, y. 'B['T; 'y]; 'a}) univ[i:l] :
   sequent { <H> >- 'r1 = 'r2 in a: 'A * "prec"{T, y. 'B['T; 'y]; 'a} } -->
   sequent { <H>; Z: 'A -> univ[i:l];
             u: \subtype{(a: 'A * 'Z 'a); (a: 'A * "prec"{T, x. 'B['T; 'x]; 'a})};
             h: z: (a: 'A * 'Z 'a) -> 'S['z];
             z: a: 'A * 'B['Z; 'a]
             >- 't1['h; 'z] = 't2['h; 'z] in 'S['z]
           } -->
   sequent { <H> >- precind{'r1; h1, z1. 't1['h1; 'z1]}
                   = precind{'r2; h2, z2. 't2['h2; 'z2]}
                   in 'S['r1]
           }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val is_prec_term : term -> bool
val dest_prec : term -> var * var * term * term
val mk_prec_term : var -> var -> term -> term -> term

val is_precind_term : term -> bool
val dest_precind : term -> var * var * term * term
val mk_precind_term : var -> var -> term -> term -> term

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
