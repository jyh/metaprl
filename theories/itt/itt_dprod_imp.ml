(*
 * Rules for dependent product.
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

extends Itt_rfun
extends Itt_dfun
extends Itt_fun
extends Itt_unit
extends Itt_union

open Mp_debug
open Printf

open Tactic_type
open Tactic_type.Conversionals
open Var

open Base_dtactic

open Itt_struct

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_dprod_imp%t"

(* debug_string DebugLoad "Loading itt_dprod..." *)

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

interactive_rw reduce_choose_left : choose{left; 'a; 'b} <--> 'a
interactive_rw reduce_choose_right : choose{right; 'a; 'b} <--> 'b

let fold_two = makeFoldC << two >> unfold_two
let fold_left = makeFoldC << left >> unfold_left
let fold_right = makeFoldC << right >> unfold_right

let resource reduce +=
   [<< choose{left; 'a; 'b} >>, reduce_choose_left;
    << choose{right; 'a; 'b} >>, reduce_choose_right]

interactive_rw reduce_spread : spread{.('a, 'b); c, d. 'e['c; 'd]} <--> 'e['a; 'b]

let resource reduce += << spread{.('a, 'b); c, d. 'e['c; 'd]} >>, reduce_spread

interactive_rw reduce_fst : fst{pair{'a; 'b}} <--> 'a
interactive_rw reduce_snd : snd{pair{'a; 'b}} <--> 'b

let resource reduce +=
   [<< fst{.('a, 'b)} >>, reduce_fst;
    << snd{.('a, 'b)} >>, reduce_snd]

interactive_rw reduce_two_order1 : two_order{left; left} <--> void
interactive_rw reduce_two_order2 : two_order{left; right} <--> unit
interactive_rw reduce_two_order3 : two_order{right; left} <--> void
interactive_rw reduce_two_order4 : two_order{right; right} <--> void

let resource reduce +=
   [<< two_order{left; left} >>, reduce_two_order1;
    << two_order{left; right} >>, reduce_two_order2;
    << two_order{right; left} >>, reduce_two_order3;
    << two_order{right; right} >>, reduce_two_order4]

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
   slot{'a} `" <" Nuprl_font!subtwo " " slot{'b}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_prod
prec prec_spread

dform prod_df : parens :: "prec"[prec_prod] :: prod{'A; 'B} =
   pushm[0] slot{'A} " " times " " slot{'B} popm

dform prod_df2 :  parens :: "prec"[prec_prod] :: prod{'A; x. 'B} =
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
   sequent ['ext] { <H> >- "type"{two} }

interactive left_member {| intro [] |} :
   sequent ['ext] { <H> >- left in two }

interactive right_member {| intro [] |} :
   sequent ['ext] { <H> >- right in two }

interactive two_elim {| elim [ThinOption thinT] |} 'H :
   [main] sequent ['ext] { <H>; x: two; <J[left]> >- 'C[left] } -->
   [main] sequent ['ext] { <H>; x: two; <J[right]> >- 'C[right] } -->
   sequent ['ext] { <H>; x: two; <J['x]> >- 'C['x] }

interactive two_well_founded {| intro [] |} :
   sequent ['ext] { <H> >- well_founded{two; a, b. two_order{'a; 'b}} }

(*
 * H >- x1:A1 * B1 = x2:A2 * B2 in Ui
 * by productEquality y
 * H >- A1 = A2 in Ui
 * H, y:A1 >- B1[y] = B2[y] in Ui
 *)
interactive productEquality {| intro []; eqcd |} 'y :
   [wf] sequent [squash] { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { <H>; y: 'A1 >- 'B1['y] = 'B2['y] in univ[i:l] } -->
   sequent ['ext] { <H> >- x1:'A1 * 'B1['x1] = x2:'A2 * 'B2['x2] in univ[i:l] }

interactive productMember {| intro [] |} 'y :
   [wf] sequent [squash] { <H> >- 'A in univ[i:l] } -->
   [wf] sequent [squash] { <H>; y: 'A >- 'B['y] in univ[i:l] } -->
   sequent ['ext] { <H> >- (x:'A * 'B['x]) in univ[i:l] }

(*
 * H >- Ui ext x:A * B
 * by productFormation A x
 * H >- A = A in Ui
 * H, x:A >- Ui ext B
 *)
interactive productFormation 'A 'x :
   [wf] sequent [squash] { <H> >- 'A in univ[i:l] } -->
   [main] ('B['x] : sequent ['ext] { <H>; x: 'A >- univ[i:l] }) -->
   sequent ['ext] { <H> >- univ[i:l] }

(*
 * Typehood.
 *)
interactive productType {| intro [] |} 'x :
   [wf] sequent [squash] { <H> >- "type"{'A1} } -->
   [wf] sequent [squash] { <H>; x: 'A1 >- "type"{'A2['x]} } -->
   sequent ['ext] { <H> >- "type"{.y:'A1 * 'A2['y]} }

(*
 * H >- x:A * B ext (a, b)
 * by pairFormation a
 * H >- a = a in A
 * H >- B[a] ext b
 * H, y:A >- B[y] = B[y] in Ui
 *)
interactive pairFormation {| intro [] |} 'a :
   [wf] sequent [squash] { <H> >- 'a in 'A } -->
   [main] ('b : sequent ['ext] { <H> >- 'B['a] }) -->
   [wf] sequent [squash] { <H>; y: 'A >- "type"{'B['y]} } -->
   sequent ['ext] { <H> >- x:'A * 'B['x] }

(*
 * H >- (a1, b1) = (a2, b2) in x:A * B
 * by pairEquality y
 * H >- a1 = a2 in A
 * H >- b1 = b2 in B[a1]
 * H, y:A >- B[y] = B[y] in Ui
 *)
interactive pairEquality {| intro []; eqcd |} :
   [wf] sequent [squash] { <H> >- 'a1 = 'a2 in 'A } -->
   [wf] sequent [squash] { <H> >- 'b1 = 'b2 in 'B['a1] } -->
   [wf] sequent [squash] { <H>; y: 'A >- "type"{'B['y]} } -->
   sequent ['ext] { <H> >- ('a1, 'b1) = ('a2, 'b2) in x:'A * 'B['x] }

(*
 * H, x:A * B[x], J[x] >- T[x] ext spread(x; u, v. t[u, v])
 * by productElimination u v
 * H, x:A * B, u:A, v:B[u], J[u, v] >- T[u, v] ext t[u, v]
 *)
interactive productElimination {| elim [ThinOption thinT] |} 'H :
   [wf] ('t['u; 'v] : sequent ['ext] { <H>; z: x:'A * 'B['x]; u: 'A; v: 'B['u]; <J['u, 'v]> >- 'T['u, 'v] }) -->
   sequent ['ext] { <H>; z: x:'A * 'B['x]; <J['z]> >- 'T['z] }

(*
 * H >- spread(e1; u1, v1. b1) = spread(e2; u2, v2. b2) in T[e1]
 * by spreadEquality (w:A * B)
 * H >- e1 = e2 in w:A * B
 * H, u:A, v: B[u], a: e1 = (u, v) in w:A * B >- b1[u; v] = b2[u; v] in T[u, v]
 *)
interactive spreadEquality {| intro []; eqcd |} bind{z. 'T['z]} (w:'A * 'B['w]) :
   [wf] sequent [squash] { <H> >- 'e1 = 'e2 in w:'A * 'B['w] } -->
   [wf] sequent [squash] { <H>; u: 'A; v: 'B['u]; a: 'e1 = ('u, 'v) in w:'A * 'B['w] >-
             'b1['u; 'v] = 'b2['u; 'v] in 'T['u, 'v] } -->
   sequent ['ext] { <H> >- spread{'e1; u1, v1. 'b1['u1; 'v1]} = spread{'e2; u2, v2. 'b2['u2; 'v2]} in 'T['e1] }

(*
 * H >- a1:A1 * B1 <= a2:A2 * B2
 * by functionSubtype
 *
 * H >- A1 <= A2
 * H, a: A1 >- B1[a] <= B2[a]
 *)
interactive productSubtype {| intro [] |} :
   sequent [squash] { <H> >- \subtype{'A1; 'A2} } -->
   sequent [squash] { <H>; a: 'A1 >- \subtype{'B1['a]; 'B2['a]} } -->
   sequent ['ext] { <H> >- \subtype{ (a1:'A1 * 'B1['a1]); (a2:'A2 * 'B2['a2]) } }

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
