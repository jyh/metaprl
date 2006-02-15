(*
 * Rules for dependent product.
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

extends Itt_rfun
extends Itt_dfun_imp
extends Itt_unit
extends Itt_union

open Lm_debug
open Lm_printf

open Tactic_type
open Var
open Dtactic
open Top_conversionals

open Itt_struct

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

define unfold_two : two <--> (unit + unit)
define unfold_left : left <--> inl{it}
define unfold_right : right <--> inr{it}
define unfold_choose : choose{'x; 'a; 'b} <--> decide{'x; y. 'a; y. 'b}
define unfold_two_order : two_order{'a; 'b} <--> choose{'a; choose{'b; void; unit}; void}

define unfold_dprod : prod{'A; x. 'B['x]} <--> { f | x: two -> choose{'x; 'A; 'B['f left]} }

define unfold_pair : pair{'a; 'b} <--> lambda{x. choose{'x; 'a; 'b}}
define unfold_spread : spread{'e; a, b. 'c['a; 'b]} <--> 'c['e inl{it}; 'e inr{it}]
define unfold_fst : fst{'e} <--> spread{'e; u, v. 'u}
define unfold_snd : snd{'e} <--> spread{'e; u, v. 'v}

interactive_rw reduce_choose_left {| reduce |} : choose{left; 'a; 'b} <--> 'a
interactive_rw reduce_choose_right {| reduce |} : choose{right; 'a; 'b} <--> 'b

let fold_two = makeFoldC << two >> unfold_two
let fold_left = makeFoldC << left >> unfold_left
let fold_right = makeFoldC << right >> unfold_right

interactive_rw reduce_spread {| reduce |} : spread{('a, 'b); c, d. 'e['c; 'd]} <--> 'e['a; 'b]

interactive_rw reduce_fst {| reduce |} : fst{pair{'a; 'b}} <--> 'a
interactive_rw reduce_snd {| reduce |} : snd{pair{'a; 'b}} <--> 'b

interactive_rw reduce_two_order1 {| reduce |} : two_order{left; left} <--> void
interactive_rw reduce_two_order2 {| reduce |} : two_order{left; right} <--> unit
interactive_rw reduce_two_order3 {| reduce |} : two_order{right; left} <--> void
interactive_rw reduce_two_order4 {| reduce |} : two_order{right; right} <--> void

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform two_df : except_mode[src] :: two =
   `"2"

dform left_df : left =
   `"left"

dform right_df : right =
   `"right"

dform choose_df : except_mode[src] :: choose{'x; 'a; 'b} =
   szone pushm[6] keyword["match"] " " slot{'x} " " keyword["with"] hspace keyword["left -> "] slot{'a} hspace keyword["right -> "] slot{'b} popm ezone

dform two_order_df : except_mode[src] :: two_order{'a; 'b} =
   slot{'a} `" <" Mpsymbols!subtwo " " slot{'b}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_prod
prec prec_spread

dform prod_df :  parens :: "prec"[prec_prod] :: prod{'A; x. 'B} =
   slot{'x} `":" slot{'A} " " times " " slot{'B}

dform pair_prl_df : except_mode[src] :: pair{'a; 'b} =
   pushm[0] `"<" slot{'a}`"," slot{'b} `">" popm

dform pair_src_df : parens :: mode[src] :: pair{'a; 'b} =
   pushm[0] slot{'a}`"," slot{'b} popm

dform spread_prl_df1 : except_mode[src] :: parens :: "prec"[prec_spread] :: spread{'e; u, v. 'b} =
   `"let " pair{'u; 'v} `" = " slot{'e} `" in " slot{'b}

dform fst_df1 : except_mode[src] :: fst{'e} =
   slot{'e} `".1"

dform snd_df1 : except_mode[src] :: snd{'e} =
   slot{'e} `".2"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Two order is well-founded.
 *)
interactive two_type {| intro [] |} :
   sequent { <H> >- "type"{two} }

interactive left_member {| intro [] |} :
   sequent { <H> >- left in two }

interactive right_member {| intro [] |} :
   sequent { <H> >- right in two }

interactive two_elim {| elim |} 'H :
   [main] sequent { <H>; <J[left]> >- 'C[left] } -->
   [main] sequent { <H>; <J[right]> >- 'C[right] } -->
   sequent { <H>; x: two; <J['x]> >- 'C['x] }

interactive two_well_founded {| intro [] |} :
   sequent { <H> >- well_founded{two; a, b. two_order{'a; 'b}} }

(*
 * H >- x1:A1 * B1 = x2:A2 * B2 in Ui
 * by productEquality y
 * H >- A1 = A2 in Ui
 * H, y:A1 >- B1[y] = B2[y] in Ui
 *)
interactive productEquality {| intro [] |} :
   [wf] sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent { <H>; y: 'A1 >- 'B1['y] = 'B2['y] in univ[i:l] } -->
   sequent { <H> >- x1:'A1 * 'B1['x1] = x2:'A2 * 'B2['x2] in univ[i:l] }

(*
 * H >- Ui ext x:A * B
 * by productFormation A x
 * H >- A = A in Ui
 * H, x:A >- Ui ext B
 *)
interactive productFormation 'A :
   [wf] sequent { <H> >- 'A in univ[i:l] } -->
   [main] ('B['x] : sequent { <H>; x: 'A >- univ[i:l] }) -->
   sequent { <H> >- univ[i:l] }

(*
 * Typehood.
 *)
interactive productType {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A1} } -->
   [wf] sequent { <H>; x: 'A1 >- "type"{'A2['x]} } -->
   sequent { <H> >- "type"{y:'A1 * 'A2['y]} }

(*
 * H >- x:A * B ext (a, b)
 * by pairFormation a
 * H >- a = a in A
 * H >- B[a] ext b
 * H, y:A >- B[y] = B[y] in Ui
 *)
interactive pairFormation {| intro [] |} 'a :
   [wf] sequent { <H> >- 'a in 'A } -->
   [main] ('b : sequent { <H> >- 'B['a] }) -->
   [wf] sequent { <H>; y: 'A >- "type"{'B['y]} } -->
   sequent { <H> >- x:'A * 'B['x] }

(*
 * H >- (a1, b1) = (a2, b2) in x:A * B
 * by pairEquality y
 * H >- a1 = a2 in A
 * H >- b1 = b2 in B[a1]
 * H, y:A >- B[y] = B[y] in Ui
 *)
interactive pairEquality {| intro [] |} :
   [wf] sequent { <H> >- 'a1 = 'a2 in 'A } -->
   [wf] sequent { <H> >- 'b1 = 'b2 in 'B['a1] } -->
   [wf] sequent { <H>; y: 'A >- "type"{'B['y]} } -->
   sequent { <H> >- ('a1, 'b1) = ('a2, 'b2) in x:'A * 'B['x] }

(*
 * H, x:A * B[x], J[x] >- T[x] ext spread(x; u, v. t[u, v])
 * by productElimination u v
 * H, x:A * B, u:A, v:B[u], J[u, v] >- T[u, v] ext t[u, v]
 *)
interactive productElimination {| elim |} 'H :
   [wf] sequent { <H>; u: 'A; v: 'B['u]; <J['u, 'v]> >- 'T['u, 'v] } -->
   sequent { <H>; z: x:'A * 'B['x]; <J['z]> >- 'T['z] }

(*
 * H >- spread(e1; u1, v1. b1) = spread(e2; u2, v2. b2) in T[e1]
 * by spreadEquality (w:A * B)
 * H >- e1 = e2 in w:A * B
 * H, u:A, v: B[u], a: e1 = (u, v) in w:A * B >- b1[u; v] = b2[u; v] in T[u, v]
 *)
interactive spreadEquality {| intro [] |} bind{z. 'T['z]} (w:'A * 'B['w]) :
   [wf] sequent { <H> >- 'e1 = 'e2 in w:'A * 'B['w] } -->
   [wf] sequent { <H>; u: 'A; v: 'B['u]; a: 'e1 = ('u, 'v) in w:'A * 'B['w] >-
             'b1['u; 'v] = 'b2['u; 'v] in 'T['u, 'v] } -->
   sequent { <H> >- spread{'e1; u1, v1. 'b1['u1; 'v1]} = spread{'e2; u2, v2. 'b2['u2; 'v2]} in 'T['e1] }

(*
 * H >- a1:A1 * B1 <= a2:A2 * B2
 * by functionSubtype
 *
 * H >- A1 <= A2
 * H, a: A1 >- B1[a] <= B2[a]
 *)
interactive productSubtype {| intro [] |} :
   sequent { <H> >- \subtype{'A1; 'A2} } -->
   sequent { <H>; a: 'A1 >- \subtype{'B1['a]; 'B2['a]} } -->
   sequent { <H> >- \subtype{ (a1:'A1 * 'B1['a1]); (a2:'A2 * 'B2['a2]) } }

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
