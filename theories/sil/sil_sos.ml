(*
 * Operational semantics of the imperative programs.
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
 * Copyright (C) 1999 Jason Hickey, Cornell University
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

extends Base_theory

extends Sil_state
extends Sil_programs

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare evalsto{'t1; 't2}
declare eval{'e1; 's1}
declare "value"{'e1; 's1}

declare eq_int{'t1; 't2}
declare neq_int{'t1; 't2}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_evalsto
prec prec_eq_int
prec prec_evalsto < prec_eq_int

dform evalsto_df : parens :: "prec"[prec_evalsto] :: evalsto{'e1; 'e2} =
   slot{'e1} " " Nuprl_font!downarrow " " slot{'e2}

dform eval_df : eval{'e; 's} =
   `"eval(" slot{'e} `"," slot{'s} `")"

dform value_df : "value"{'v; 's} =
   `"value(" slot{'v} `"," slot{'s} `")"

dform eq_int_df : parens :: "prec"[prec_eq_int] :: "eq_int"{'t1; 't2} =
   slot{'t1} hspace `"= " slot{'t2}

dform neq_int_df : parens :: "prec"[prec_eq_int] :: "neq_int"{'t1; 't2} =
   slot{'t1} hspace Nuprl_font!neq " " slot{'t2}

(************************************************************************
 * NATURAL SEMANTICS                                                    *
 ************************************************************************)

(*
 * Numbers.
 *)
prim snumber_eval :
   sequent ['ext] { 'H >- evalsto{eval{number[i:n]; 's}; ."value"{number[i:n]; 's}}} =
   it

prim add_eval 's2 :
   [main] sequent [squash] { 'H >- evalsto{eval{'e1; 's1}; ."value"{number[i:n]; 's2}} } -->
   [main] sequent [squash] { 'H >- evalsto{eval{'e2; 's2}; ."value"{number[j:n]; 's3}} } -->
   sequent ['ext] { 'H >- evalsto{eval{add{'e1; 'e2}; 's1}; ."value"{meta_sum[i:n, j:n]; 's3}} } =
   it

prim sub_eval 's2 :
   [main] sequent [squash] { 'H >- evalsto{eval{'e1; 's1}; ."value"{number[i:n]; 's2}} } -->
   [main] sequent [squash] { 'H >- evalsto{eval{'e2; 's2}; ."value"{number[j:n]; 's3}} } -->
   sequent ['ext] { 'H >- evalsto{eval{sub{'e1; 'e2}; 's1}; eval{meta_diff[i:n, j:n]; 's3}} } =
   it

prim if_eval_true (number[i:n]) 's2 (number[j:n]) 's3 :
   [main] sequent [squash] { 'H >- evalsto{eval{'e1; 's1}; ."value"{number[i:n]; 's2}} } -->
   [main] sequent [squash] { 'H >- evalsto{eval{'e2; 's2}; ."value"{number[j:n]; 's3}} } -->
   [assertion] sequent [squash] { 'H >- meta_eq[i:n, j:n]{."true"; ."false"} } -->
   [main] sequent [squash] { 'H >- evalsto{eval{'e3; 's3}; ."value"{'v3; 's4}} } -->
   sequent ['ext] { 'H >- evalsto{eval{."if"{'e1; 'e2; 'e3; 'e4}; 's1}; ."value"{'v3; 's4}} } =
   it

(*
 * Disjoint union.
 *)
prim inl_eval :
   [main] sequent [squash] { 'H >- evalsto{eval{'e1; 's1}; ."value"{'v1; 's2}} } -->
   sequent ['ext] { 'H >- evalsto{eval{inl{'e1}; 's1}; ."value"{inl{'v1}; 's2}} } =
   it

prim inr_eval :
   [main] sequent [squash] { 'H >- evalsto{eval{'e1; 's1}; ."value"{'v1; 's2}} } -->
   sequent ['ext] { 'H >- evalsto{eval{inr{'e1}; 's1}; ."value"{inr{'v1}; 's2}} } =
   it

prim decide_eval_left 'v1 's2 :
   [main] sequent [squash] { 'H >- evalsto{eval{'e1; 's1}; ."value"{.inl{'v1}; 's2}} } -->
   [main] sequent [squash] { 'H >- evalsto{eval{'e2['v1]; 's2}; ."value"{'v2; 's3}} } -->
   sequent ['ext] { 'H >- evalsto{eval{decide{'e1; x. 'e2['x]; y. 'e3['y]}; 's1}; ."value"{'v2; 's3}} } =
   it

prim decide_eval_right 'v1 's2 :
   [main] sequent [squash] { 'H >- evalsto{eval{'e1; 's1}; ."value"{inr{'v1}; 's2}} } -->
   [main] sequent [squash] { 'H >- evalsto{eval{'e3['v1]; 's2}; ."value"{'v3; 's3}} } -->
   sequent ['ext] { 'H >- evalsto{eval{decide{'e1; x. 'e2['x]; y. 'e3['y]}; 's1}; ."value"{'v3; 's3}} } =
   it

(*
 * Pairs.
 *)
prim pair_eval 's2 :
   [main] sequent [squash] { 'H >- evalsto{eval{'e1; 's1}; ."value"{'v1; 's2}} } -->
   [main] sequent [squash] { 'H >- evalsto{eval{'e2; 's2}; ."value"{'v2; 's3}} } -->
   sequent ['ext] { 'H >- evalsto{eval{pair{'e1; 'e2}; 's1}; ."value"{pair{'v1; 'v2}; 's3}} } =
   it

prim spread_eval 'v1 'v2 's2 :
   [main] sequent [squash] { 'H >- evalsto{eval{'e1; 's1}; ."value"{pair{'v1; 'v2}; 's2}} } -->
   [main] sequent [squash] { 'H >- evalsto{eval{'e2['v1; 'v2]; 's2}; ."value"{'v3; 's3}} } -->
   sequent ['ext] { 'H >- evalsto{eval{spread{'e1; x, y. 'e2['x; 'y]}; 's1}; ."value"{'v3; 's3}} } =
   it

(*
 * Reference cells.
 *)
prim ref_eval 'v1 's2 :
   [main] sequent [squash] { 'H >- evalsto{eval{'e1; 's1}; ."value"{'v1; 's2}} } -->
   sequent ['ext] { 'H >- evalsto{eval{ref{'e1}; 's1}; alloc{'s2; 'v1; s3, l. "value"{'l; 's3}}} } =
   it

prim deref_eval 'v1 :
   [main] sequent [squash] { 'H >- evalsto{eval{'e1; 's1}; ."value"{'v1; 's2}} } -->
   sequent ['ext] { 'H >- evalsto{eval{deref{'e1}; 's1}; ."value"{fetch{'s2; 'v1}; 's2}} } =
   it

prim assign_eval 's2 :
   [main] sequent [squash] { 'H >- evalsto{eval{'e1; 's1}; ."value"{'v1; 's2}} } -->
   [main] sequent [squash] { 'H >- evalsto{eval{'e2; 's2}; ."value"{'v2; 's3}} } -->
   sequent ['ext] { 'H >- evalsto{eval{assign{'e1; 'e2}; 's1}; ."value"{.dot; store{'s3; 'v1; 'v2}}} } =
   it

prim dot_eval :
   sequent ['ext] { 'H >- evalsto{eval{dot; 's1}; ."value"{dot; 's1}} } =
   it

(*
 * Functions.
 *)
prim lambda_eval :
   sequent ['ext] { 'H >- evalsto{eval{lambda{v. 'e1['v]}; 's1}; ."value"{lambda{v. 'e1['v]}; 's1}} } =
   it

prim apply_eval 'v2 's2 (lambda{v. 'e3['v]}) 's3 :
   [main] sequent [squash] { 'H >- evalsto{eval{'e2; 's1}; ."value"{'v2; 's2}} } -->
   [main] sequent [squash] { 'H >- evalsto{eval{'e1; 's2}; ."value"{lambda{v. 'e3['v]}; 's3}} } -->
   [main] sequent [squash] { 'H >- evalsto{eval{'e3['v2]; 's3}; ."value"{'v3; 's4}} } -->
   sequent ['ext] { 'H >- evalsto{eval{apply{'e1; 'e2}; 's1}; ."value"{'v3; 's4}} } =
   it

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
