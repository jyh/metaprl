(*
 * Dependent functions.
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
 * Copyright (C) 1998-2005 MetaPRL Group, Cornell University and Caltech
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
 * Modified By: Alexei Kopylov <kopylov@cs.caltech.edu>
 *              Aleksey Nogin <nogin@cs.caltech.edu>
 *
 *)
extends Itt_equal
extends Itt_set
extends Itt_void

open Basic_tactics

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "fun"{'A; x. 'B['x]}

declare lambda{x. 'b['x]}
declare apply{'f; 'a}

declare ycomb
declare fix{f. 'b['f]}

define unfold_let : "let"{'a;x.'b['x]} <--> (lambda{x.'b['x]} 'a)

topval fold_fix : conv
topval fold_ycomb : conv

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite reduce_beta : (lambda{v. 'b['v]} 'a) <--> 'b['a]
rewrite reduce_fix : fix{f. 'b['f]} <--> 'b[fix{f. 'b['f]}]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext a:A -> B
 * by functionFormation a A
 *
 * H >- A = A in Ui
 * H, a: A >- Ui ext B
 *)
rule functionFormation 'A :
   sequent { <H> >- 'A in univ[i:l] } -->
   sequent { <H>; a: 'A >- univ[i:l] } -->
   sequent { <H> >- univ[i:l] }

(*
 * H >- (a1:A1 -> B1[a1]) = (a2:A2 -> B2[a2]) in Ui
 * by functionEquality x
 *
 * H >- A1 = A2 in Ui
 * H, x: A1 >- B1[x] = B2[x] in Ui
 *)
rule functionEquality :
   sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   sequent { <H>; x: 'A1 >- 'B1['x] = 'B2['x] in univ[i:l] } -->
   sequent { <H> >- (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[i:l] }

(*
 * Typehood.
 *)
rule functionType :
   sequent { <H> >- "type"{'A} } -->
   sequent { <H>; a: 'A >- "type"{'B['a]} } -->
   sequent { <H> >- "type"{ a:'A -> 'B['a] } }

(*
 * H >- a:A -> B[a] ext lambda(z. b[z])
 * by lambdaFormation Ui
 *
 * H >- A = A in Ui
 * H, z: A >- B[z] ext b[z]
 *)
rule lambdaFormation :
   sequent { <H> >- "type"{'A} } -->
   sequent { <H>; z: 'A >- 'B['z] } -->
   sequent { <H> >- a:'A -> 'B['a] }

(*
 * H >- lambda(a1. b1[a1]) = lambda(a2. b2[a2]) in a:A -> B
 * by lambdaEquality Ui
 *
 * H >- A = A in Ui
 * H, x: A >- b1[x] = b2[x] in B[x]
 *)
rule lambdaEquality :
   sequent { <H> >- "type"{'A} } -->
   sequent { <H>; x: 'A >- 'b1['x] = 'b2['x] in 'B['x] } -->
   sequent { <H> >- lambda{a1. 'b1['a1]} = lambda{a2. 'b2['a2]} in a:'A -> 'B['a] }

(*
 * H >- f = g in x:A -> B
 * by functionExtensionality Ui (y:C -> D) (z:E -> F) u
 *
 * H, u:A >- f(u) = g(u) in B[u]
 * H >- A = A in Ui
 * H >- f = f in y:C -> D
 * H >- g = g in z:E -> F
 *)
rule functionExtensionality (y:'C -> 'D['y]) (z:'E -> 'F['z]) :
   sequent { <H>; u: 'A >- ('f 'u) = ('g 'u) in 'B['u] } -->
   sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- 'f in y:'C -> 'D['y] } -->
   sequent { <H> >- 'g in z:'E -> 'F['z] } -->
   sequent { <H> >- 'f = 'g in x:'A -> 'B['x] }

(*
 * H, f: (x:A -> B), J[x] >- T[f] t[f, f a, it]
 * by functionElimination i a
 *
 * H, f: (x:A -> B), J[x] >- a = a in A
 * H, f: (x:A -> B), J[x], y: B[a], v: y = f(a) in B[a] >- T[f] ext t[f, y, v]
 *)
rule functionElimination 'H 'a :
   sequent { <H>; f: x:'A -> 'B['x]; <J['f]> >- 'a in 'A } -->
   sequent { <H>; f: x:'A -> 'B['x]; <J['f]>; y: 'B['a]; v: 'y = ('f 'a) in 'B['a] >- 'T['f] } -->
   sequent { <H>; f: x:'A -> 'B['x]; <J['f]> >- 'T['f] }

(*
 * H >- (f1 a1) = (f2 a2) in B[a1]
 * by applyEquality (x:A -> B[x])
 *
 * H >- f1 = f2 in x:A -> B[x]
 * H >- a1 = a2 in A
 *)
rule applyEquality (x:'A -> 'B['x]) :
   sequent { <H> >- 'f1 = 'f2 in x:'A -> 'B['x] } -->
   sequent { <H> >- 'a1 = 'a2 in 'A } -->
   sequent { <H> >- ('f1 'a1) = ('f2 'a2) in 'B['a1] }

(*
 * H >- a1:A1 -> B1 <= a2:A2 -> B2
 * by functionSubtype
 *
 * H >- A2 <= A1
 * H, a: A1 >- B1[a] <= B2[a]
 *)
rule functionSubtype :
   sequent { <H> >- \subtype{'A2; 'A1} } -->
   sequent { <H>; a: 'A1 >- \subtype{'B1['a]; 'B2['a]} } -->
   sequent { <H> >- \subtype{ (a1:'A1 -> 'B1['a1]); (a2:'A2 -> 'B2['a2]) } }

(*
(*
 * H; x: a1:A1 -> B1 <= a2:A2 -> B2; J[x] >- T[x]
 * by function_subtypeElimination i
 *
 * H; x: a1:A1 -> B1 <= a2:A2 -> B2; y: A2 <= A1; z: a:A2 -> B2[a] <= B1[a]; J[x] >- T[x]
 *)
rule function_subtypeElimination 'H 'x 'y 'z 'a :
   sequent { <H>;
             x: \subtype{(a1:'A1 -> 'B1['a1]); (a2:'A2 -> 'B2['a2])};
             <J['x]>;
             y: \subtype{'A2; 'A1};
             z: a:'A2 -> \subtype{'B1['a]; 'B2['a]}
             >- 'T['x]
           } -->
   sequent { <H>; x: \subtype{(a1:'A1 -> 'B1['a1]); (a2:'A2 -> 'B2['a2])}; <J['x]> >- 'T['x] }
*)

(*
 * JYH: this rule assumes an intentional type theory, and the rule doesn't belong
 * in this module.
 *
 * H; x: a1:A1 -> B1 = a2:A2 -> B2 in Ui; J[x] >- T[x]
 * by function_equalityElimination
 *
 * H; x: a1:A1 -> B1 = a2:A2 -> B2 in Ui; y: A1 = A2 in Ui; z: a:A1 -> B1[a] = B2[a] in Ui; J[x] >- T[x]
rule function_equalityElimination 'H 'x 'y 'z 'a :
   sequent { <H>;
             x: (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[i:l];
             <J['x]>;
             y: 'A1 = 'A2 in univ[i:l];
             z: a:'A1 -> ('B1['a] = 'B2['a] in univ[i:l])
             >- 'T['x]
           } -->
   sequent { <H>; x: (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[i:l]; <J['x]> >- 'T['x] }
 *)

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val dfun_term : term
val is_dfun_term : term -> bool
val dest_dfun : term -> var * term * term
val mk_dfun_term : var -> term -> term -> term

(*
 * Dfun terms, where the image type does not depend on the variable
 *)
val is_fun_term : term -> bool
val dest_fun : term -> term * term
val mk_fun_term : term -> term -> term

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

topval fnExtensionalityT : term -> term -> tactic
topval fnExtenT : term -> tactic
topval fnExtenVoidT : tactic

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_fun
prec prec_apply
prec prec_lambda

declare declaration{'decl : Dform ;'term : Dform } : Dform

(************************************************************************
 * Grammar.
 *)
declare tok_Fun       : Terminal

lex_token xterm : "Fun" --> tok_Fun

production xterm_apply_term{'e1 'e2} <--
   xterm_apply_term{'e1}; xterm_simple_term{'e2}

production xterm_term{'t1 -> 't2} <--
   xterm_term{'t1}; tok_arrow; xterm_term{'t2}

production xterm_term{x: 't1 -> 't2} <--
   tok_Fun; tok_id[x:s]; tok_colon; xterm_apply_term{'t1}; tok_arrow; xterm_term{'t2}

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
