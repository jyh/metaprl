(*
 * Dependent functions.
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
extends Itt_set
extends Itt_void

open Lm_symbol

open Refiner.Refiner.Term

open Tactic_type.Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "fun"{'A; x. 'B['x]}
declare "fun"{'A; 'B}
declare rfun{'A; f, x. 'B['f; 'x]}

declare lambda{x. 'b['x]}
declare apply{'f; 'a}

declare well_founded{'A; x, y. 'R['x; 'y]}
declare well_founded_assum{'A; a1, a2. 'R['a1; 'a2]; 'P}
declare well_founded_prop{'A}
declare well_founded_apply{'P; 'a}
declare fix{f. 'b['f]}

define unfold_let : "let"{'a;x.'b['x]} <--> (lambda{x.'b['x]} 'a)

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_fun
prec prec_apply
prec prec_lambda

declare declaration{'decl;'term}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite reduce_beta : (lambda{v. 'b['v]} 'a) <--> 'b['a]
rewrite reduce_fix : fix{f. 'b['f]} <--> 'b[fix{f. 'b['f]}]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext { f | a:A -> B }
 * by rfunctionFormation { f | a: A -> B }
 *
 * H >- { f | a: A -> B } = { f | a: A -> B } in Ui
 *)
rule rfunctionFormation { f | a: 'A -> 'B['f; 'a] } :
   sequent { <H> >- { f | a: 'A -> 'B['f; 'a] } = { f | a: 'A -> 'B['f; 'a] } in univ[i:l] } -->
   sequent { <H> >- univ[i:l] }

(*
 * H >- { f1 | a1:A1 -> B1[f1, a1] } = { f2 | a2:A2 -> B2[f2, a2] } in Ui
 * by rfunctionEquality R[a, b]
 *
 * H >- A1 = A2 in Ui
 * H >- well_founded(A1; a, b. R[a, b])
 * H, y:A, g : { f1 | x1: { z: A1 | R z y } -> B1[f1, x1] } >- B1[g, y] = B2[g, y] in Ui
 *)
rule rfunctionEquality lambda{a. lambda{b. 'R['a; 'b]}} :
   sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   sequent { <H> >- well_founded{'A1; a, b. 'R['a; 'b]} } -->
   sequent { <H>;
             y: 'A1;
             g: { f1 | x1: { z: 'A1 | 'R['z; 'y] } -> 'B1['f1; 'x1] }
             >- 'B1['g; 'y] = 'B2['g; 'y] in univ[i:l]
           } -->
   sequent { <H> >- { f1 | a1:'A1 -> 'B1['f1; 'a1] }
                   = { f2 | a2:'A2 -> 'B2['f2; 'a2] }
                   in univ[i:l]
           }

(*
 * H >- { f | a:A -> B[a] } ext lambda(y. fix(g. b[g, y]))
 * by rfunctionLambdaFormation R[a, b]
 *
 * H >- A = A in Ui
 * H >- well_founded(A; a, b. R[a, b])
 * H, y: A, g: { f | { z: A | R z y } -> B[f, x] } >- B[g, y] ext b[g, y]
 *)
rule rfunction_lambdaFormation lambda{a. lambda{b. 'R['a; 'b]}} :
   sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- well_founded{'A; a, b. 'R['a; 'b]} } -->
   sequent { <H>; y: 'A; g: { f | x: { z: 'A | 'R['z; 'y] } -> 'B['f; 'x] } >- 'B['g; 'y] } -->
   sequent { <H> >- { f | x:'A -> 'B['f; 'x] } }

(*
 * H >- lambda(x1. b1[x1]) = lambda(x2. b2[x2]) in {f | x:A -> B[f, x] }
 * by rfunction_lambdaEquality
 *
 * H >- { f | x:A -> B[f, x] } = { f | x:A -> B[f, x] } in type
 * H, y: A >- b1[y] = b2[y] in B[lambda(x1. b1[x1]); y]
 *)
rule rfunction_lambdaEquality :
   sequent { <H> >- "type"{{ f | x: 'A -> 'B['f; 'x] }} } -->
   sequent { <H>; y: 'A >- 'b1['y] = 'b2['y] in 'B[lambda{x1. 'b1['x1]}; 'y] } -->
   sequent { <H> >- lambda{x1. 'b1['x1]} = lambda{x2. 'b2['x2]} in { f | x: 'A -> 'B['f; 'x] } }

(*
 * H >- f1 = f2 in { g | x:A -> B[g, x] }
 * by rfunctionExtensionality { g1 | x1:A1 -> B1[g1, x1] } { g2 | x2:A2 -> B2[g2, x2] }
 *
 * H >- { g | x:A -> B[g, x] } = { g | x:A -> B[g, x] } in type
 * H, y: A >- f1 y = f2 y in B[f1, x]
 * H >- f1 = f1 in { g1 | x1:A1 -> B1[g1, x1] }
 * H >- f2 = f2 in { g2 | x2:A2 -> B2[g2, x2] }
 *)
rule rfunctionExtensionality
        ({ g1 | x1:'A1 -> 'B1['g1; 'x1] })
        ({ g2 | x2:'A2 -> 'B2['g2; 'x2] }) :
   sequent { <H> >- "type"{{ g | x:'A -> 'B['g; 'x] }} } -->
   sequent { <H>; y: 'A >- 'f1 'y = 'f2 'y in 'B['f1; 'y] } -->
   sequent { <H> >- 'f1 = 'f1 in { g1 | x1:'A1 -> 'B1['g1; 'x1] } } -->
   sequent { <H> >- 'f2 = 'f2 in { g2 | x2:'A2 -> 'B2['g2; 'x2] } } -->
   sequent { <H> >- 'f1 = 'f2 in { g | x:'A -> 'B['g; 'x] } }

(*
 * H, f: { g | x:A -> B[g, x] }, J[f] >- T[f] ext t[f, f a, it]
 * by rfunctionElimination a
 *
 * H, f: { g | x:A -> B[g, x] }, J[f] >- a = a in A
 * H, f: { g | x:A -> B[g, x] }, J[f], y: B[f, a], v: y = f a in B[f, a] >- T[f] ext t[f, y, v]
 *)
rule rfunctionElimination 'H 'a :
   sequent { <H>; f: { g | x:'A -> 'B['g; 'x] }; <J['f]> >- 'a in 'A } -->
   sequent { <H>;
             f: { g | x:'A -> 'B['g; 'x] };
             <J['f]>;
             y: 'B['f; 'a];
             'y = 'f 'a in 'B['f; 'a]
             >- 'T['f] } -->
   sequent { <H>; f: { g | x:'A -> 'B['g; 'x] }; <J['f]> >- 'T['f] }

(*
 * H >- f1 a1 = f2 a2 in B[f1, a1]
 * by rfunction_applyEquality { f | x:A -> B[f, x] }
 *
 * H >- f1 = f2 in { f | x:A -> B[f, x] }
 * H >- a1 = a2 in A
 *)
rule rfunction_applyEquality ({ f | x:'A -> 'B['f; 'x] }) :
   sequent { <H> >- 'f1 = 'f2 in { f | x:'A -> 'B['f; 'x] } } -->
   sequent { <H> >- 'a1 = 'a2 in 'A } -->
   sequent { <H> >- 'f1 'a1 = 'f2 'a2 in 'B['f1; 'a1] }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val rfun_term : term
val is_rfun_term : term -> bool
val dest_rfun : term -> var * var * term * term
val mk_rfun_term : var -> var -> term -> term -> term

val dfun_term : term
val is_dfun_term : term -> bool
val dest_dfun : term -> var * term * term
val mk_dfun_term : var -> term -> term -> term

val fun_term : term
val is_fun_term : term -> bool
val dest_fun : term -> term * term
val mk_fun_term : term -> term -> term

val well_founded_term : term
val is_well_founded_term : term -> bool
val dest_well_founded : term -> var * var * term * term
val mk_well_founded_term : var -> var -> term -> term -> term

val lambda_term : term
val is_lambda_term : term -> bool
val dest_lambda : term -> var * term
val mk_lambda_term : var -> term -> term

val fix_term : term
val is_fix_term : term -> bool
val dest_fix : term -> var * term
val mk_fix_term : var -> term -> term

val apply_term : term
val is_apply_term : term -> bool
val dest_apply : term -> term * term
val mk_apply_term : term -> term -> term

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_fun
prec prec_apply
prec prec_lambda

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite reduce_beta : (lambda{v. 'b['v]} 'a) <--> 'b['a]
rewrite reduce_fix : fix{f. 'b['f]} <--> 'b[fix{f. 'b['f]}]

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

topval rfunction_extensionalityT : term -> term -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
