(*
 * Model the state as a dependant record.
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

extends Itt_theory

extends Sil_state

open Base_dtactic
open Itt_struct

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

(*
 * Type of labels.
 * We carry alnong the type, but we don't use it right now.
 *)
declare label_type
declare eq_label{'l1; 'l2}

(*
 * Declarations are syntax for constructing state types.
 *)
declare empty_decl
declare store_decl{'decl; 'l; 'v}
declare alloc_decl{'decl; 'l; 'v}

(*
 * Well-orderings.
 *)
declare order_type
declare discrete_order
declare next_order{'order; 'l}
declare order_apply{'order; 'a; 'b}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_next_order

dform label_type_df : label_type =
   `"Label"

dform eq_label_df : eq_label{'l1; 'l2} =
   slot{'l1} `" =l " slot{'l2}

dform empty_decl_df : empty_decl =
   `"[]"

dform store_decl_df : store_decl{'decl; 'l; 'v} =
   slot{'decl} `"[" slot{'l} `" = " slot{'v} `"]"

dform alloc_decl_df : alloc_decl{'decl; 'l; 'v} =
   slot{'decl} `"+[" slot{'l} `" = " slot{'v} `"]"

dform order_type_df : order_type =
   `"OrderType"

dform discrete_order_df : discrete_order =
   `"discrete"

dform next_order_df : parens :: "prec"[prec_next_order] :: next_order{'order; 'l} =
   `"next(" slot{'order} `" < " slot{'l} `")"

dform order_apply_df : order_apply{'order; 'l1; 'l2} =
   `"order_apply(" slot{'order} `", " slot{'l1} `", " slot{'l2} `")"

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

(*
 * We'll model labels as lists, because we'll otherwise run into trouble with wf.
 *)
prim_rw unfold_label_type : label_type <--> list{unit}

prim_rw unfold_first : first <--> nil
prim_rw unfold_next : next{'l} <--> cons{it; 'l}

(*
 * Comparsions.
 *)
prim_rw unfold_eq_label : eq_label{'e1; 'e2} <-->
   (list_ind{'e1; lambda{e2. list_ind{'e2; btrue; u, v, g. bfalse}};
                u1, v1, g1. lambda{e2. list_ind{'e2; bfalse; u2, v2, g2. 'g1 'v2}}} 'e2)

prim_rw unfold_if_eq_label : if_eq_label{'e1; 'e2; 'e3; 'e4} <-->
   ifthenelse{eq_label{'e1; 'e2}; 'e3; 'e4}

interactive_rw reduce_eq_label1 : eq_label{first; first} <--> btrue
interactive_rw reduce_eq_label2 : eq_label{next{'l1}; first} <--> bfalse
interactive_rw reduce_eq_label3 : eq_label{first; next{'l1}} <--> bfalse
interactive_rw reduce_eq_label4 : eq_label{next{'l1}; next{'l2}} <--> eq_label{'l1; 'l2}

let reduce_info =
   [<< eq_label{first; first} >>, reduce_eq_label1;
    << eq_label{next{'l1}; first} >>, reduce_eq_label2;
    << eq_label{first; next{'l1}} >>, reduce_eq_label3;
    << eq_label{next{'l1}; next{'l2}} >>, reduce_eq_label4]

let reduce_resource = Top_conversionals.add_reduce_info reduce_resource reduce_info

interactive_rw reduce_if_eq_label1 : if_eq_label{first; first; 'e1; 'e2} <--> 'e1
interactive_rw reduce_if_eq_label2 : if_eq_label{next{'l1}; first; 'e1; 'e2} <--> 'e2
interactive_rw reduce_if_eq_label3 : if_eq_label{first; next{'l1}; 'e1; 'e2} <--> 'e2
interactive_rw reduce_if_eq_label4 : if_eq_label{next{'l1}; next{'l2}; 'e1; 'e2} <--> if_eq_label{'l1; 'l2; 'e1; 'e2}

(*
 * State is a record construction, with an allocation set as its first
 * element.
 *)
prim_rw unfold_empty : empty <--> lambda{l. next{first}}

prim_rw unfold_fetch : fetch{'s; 'l} <--> ('s 'l)

prim_rw unfold_store : store{'s; 'l1; 'v1} <-->
   lambda{l2. ifthenelse{eq_label{'l2; 'l1}; 'v1; .'s 'l2}}

prim_rw unfold_alloc : alloc{'s; 'v1; s2, l. 'e['s2; 'l]} <-->
   (lambda{l1. 'e[store{store{'s; first; 'l1}; 'l1; 'v1}; 'l1]} next{fetch{'s; first}})

(*
 * Fetch operation.
 *)
interactive_rw reduce_fetch : fetch{store{'s; 'l1; 'v}; 'l2} <--> ifthenelse{eq_label{'l2; 'l1}; 'v; fetch{'s; 'l2}}

(*
 * Declarations are type functions with a well-ordering on the domain.
 *)
prim_rw unfold_order_type : order_type <--> (label_type -> label_type -> univ[1:l])

prim_rw unfold_order_apply : order_apply{'order; 'a; 'b} <--> ('order 'a 'b)

prim_rw unfold_discrete_order : discrete_order <--> lambda{l1. lambda{l2. void}}

prim_rw unfold_next_order : next_order{'order; 'l} <-->
   lambda{l1. lambda{l2. ifthenelse{eq_label{'l1; 'l}; void; ifthenelse{eq_label{'l2; 'l}; unit; order_apply{'order; 'l1; 'l2}}}}}

prim_rw unfold_empty_decl : empty_decl <--> (discrete_order, lambda{l. lambda{s. ifthenelse{eq_label{'l; first}; label_type; top}}})

prim_rw unfold_store_decl : store_decl{'decl; 'l; 'v} <-->
   spread{'decl; order, f. ('order, lambda{l2. ifthenelse{eq_label{'l2; 'l}; 'v; .'f 'l2}})}

prim_rw unfold_alloc_decl : alloc_decl{'decl; 'l; 'v} <-->
   spread{'decl; order, f. (next_order{'order; 'l}, lambda{l2. ifthenelse{eq_label{'l2; 'l}; 'v; .'f 'l2}})}

(************************************************************************
 * DECLARATION RULES                                                    *
 ************************************************************************)

(*
 * Labels are in their type.
 *)
interactive label_type_member {| intro [] |} :
   sequent ['ext] { 'H >- member{univ[i:l]; label_type} }

interactive label_type_type {| intro [] |} :
   sequent ['ext] { 'H >- "type"{label_type} }

interactive first_member {| intro [] |} :
   sequent ['ext] { 'H >- member{label_type; first} }

interactive next_member {| intro [] |} :
   [wf] sequent [squash] { 'H >- member{label_type; 'l} } -->
   sequent ['ext] { 'H >- member{label_type; next{'l}} }

interactive label_elim {| elim [ThinOption thinT] |} 'H :
   [main] sequent ['ext] { 'H; l: label_type; 'J['l] >- 'C[first] } -->
   [main] sequent ['ext] { 'H; l: label_type; 'J['l]; v: label_type; w: 'C['v] >- 'C[next{'v}] } -->
   sequent ['ext] { 'H; l: label_type; 'J['l] >- 'C['l] }

interactive eq_label_member {| intro [] |} :
   [wf] sequent [squash] { 'H >- member{label_type; 'l1} } -->
   [wf] sequent [squash] { 'H >- member{label_type; 'l2} } -->
   sequent ['ext] { 'H >- member{bool; eq_label{'l1; 'l2}} }

interactive label_eq_member {| intro [] |} :
   [wf] sequent [squash] { 'H >- member{label_type; 'l1} } -->
   [wf] sequent [squash] { 'H >- member{label_type; 'l2} } -->
   [wf] sequent [squash] { 'H; v: "assert"{eq_label{'l1; 'l2}} >- member{'T; 'e1} } -->
   [wf] sequent [squash] { 'H; v: "assert"{bnot{eq_label{'l1; 'l2}}} >- member{'T; 'e2} } -->
   sequent ['ext] { 'H >- member{'T; if_eq_label{'l1; 'l2; 'e1; 'e2}} }

(*
 * Orderings.
 *)
interactive order_type_member {| intro [] |} :
   sequent ['ext] { 'H >- member{univ[i:l]; order_type} }

interactive order_type_type {| intro [] |} :
   sequent ['ext] { 'H >- "type"{order_type} }

interactive order_apply_member {| intro [] |} :
   [wf] sequent [squash] { 'H >- member{order_type; 'order} } -->
   [wf] sequent [squash] { 'H >- member{label_type; 'l1} } -->
   [wf] sequent [squash] { 'H >- member{label_type; 'l2} } -->
   sequent ['ext] { 'H >- member{univ[i:l]; order_apply{'order; 'l1; 'l2}} }

interactive order_apply_type {| intro [] |} :
   [wf] sequent [squash] { 'H >- member{order_type; 'order} } -->
   [wf] sequent [squash] { 'H >- member{label_type; 'l1} } -->
   [wf] sequent [squash] { 'H >- member{label_type; 'l2} } -->
   sequent ['ext] { 'H >- "type"{order_apply{'order; 'l1; 'l2}} }

(*
 * Discrete order is well-formed, and well-founded.
 *)
interactive discrete_order_wf {| intro [] |} :
   sequent ['ext] { 'H >- member{order_type; discrete_order} }

interactive discrete_order_well_founded {| intro [] |} :
   sequent ['ext] { 'H >- well_founded{label_type; l1, l2. discrete_order 'l1 'l2} }

(*
 * Next order is well-formed and well-founded.
 *)
interactive next_order_wf {| intro [] |} :
   [wf] sequent [squash] { 'H >- member{order_type; 'order} } -->
   [wf] sequent [squash] { 'H >- member{label_type; 'l} } -->
   sequent ['ext] { 'H >- member{order_type; next_order{'order; 'l}} }

interactive next_order_anti_ref {| intro [] |} 'a :
   [wf] sequent [squash] { 'H >- member{order_type; 'order} } -->
   [wf] sequent [squash] { 'H; a: label_type >- not{order_apply{'order; 'a; 'a}} } -->
   [wf] sequent [squash] { 'H >- member{label_type; 'l1} } -->
   [wf] sequent [squash] { 'H >- member{label_type; 'l2} } -->
   sequent ['ext] { 'H >- not{order_apply{next{'order; 'l1}; 'l2; 'l2}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
