(*
 * Interpret the state types.
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

include Itt_theory
include Sil_itt_state
include Sil_state_types

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare next_label{'D; 'l}
declare eq_label_fun

declare decl_type[i:l]

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform next_label_df : next_label{'D; 'l} =
   `"next_label(" slot{'D} `", " slot{'l} `")"

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

prim_rw unfold_label_type : label_type <--> list{unit}

prim_rw unfold_eq_label_fun : eq_label_fun <--> lambda{l1. lambda{l2. eq_label{'l1; 'l2}}}

prim_rw unfold_decl_type : decl_type[i:l] <--> (label_type * univ[i:l])

prim_rw unfold_empty_decl : empty_decl <--> cons{pair{first; label_type}; nil}

prim_rw unfold_store_decl : store_decl{'D; 'l; 'T} <-->
   cons{pair{'l; 'T}; 'D}

prim_rw unfold_alloc_decl : alloc_decl{'D; 'T} <-->
   store_decl{'D; next_label{'D; first}; 'T}

prim_rw unfold_next_label : next_label{'D; 'l} <-->
   (list_ind{'D; lambda{l. next{'l}}; u, v, g.
      lambda{l1. spread{'u; l2, T.
         ifthenelse{le_label{'l1; 'l2}; .'g 'l2; .'g 'l1}}}} 'l)

interactive_rw reduce_next_label1 : next_label{empty_decl; 'l} <--> next{'l}

interactive_rw reduce_next_label2 : next_label{store{'D; 'l1; 'T}; 'l2} <-->
   ifthenelse{le_label{'l2; 'l1};
      next_label{'D; 'l1};
      next_label{'D; 'l2}}

interactive_rw reduce_next_label3 : next_label{alloc{'D; 'T}; 'l} <-->
   ifthenelse{le_label{'l; next_label{'D; first}};
      next_label{'D; next_label{'D; first}};
      next_label{'D; 'l}}


(*
 * State builds a function from the declaration.
 *)
prim_rw unfold_state : state{'D} <-->
   (l : label_type -> assoc{eq_label_fun; 'l; 'D; T. 'T; top})

(************************************************************************
 * THEOREMS                                                             *
 ************************************************************************)

(*
 * Well-formedness of label type.
 *)
interactive label_wf {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- member{univ[i:l]; label_type} }

interactive label_type {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- "type"{label_type} }

(*
 * Well-formedness of eqlabel_fun
 *)
interactive eq_label_fun_wf {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- member{.label_type -> label_type -> bool; eq_label_fun} }

(*
 * Type of declaration lists.
 *)
interactive decl_type_wf {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- member{univ[i ':l]; decl_type[i:l]} }

interactive empty_decl_wf {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- member{decl_type[i:l]; empty_decl} }

interactive store_decl_wf {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- member{decl_type[i:l]; 'D} } -->
   [wf] sequent [squash] { 'H >- member{label_type; 'l} } -->
   [wf] sequent [squash] { 'H >- member{univ[i:l]; 'T} } -->
   sequent ['ext] { 'H >- member{decl_type[i:l]; store_decl{'D; 'l; 'T}} }

interactive alloc_decl_wf {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- member{decl_type[i:l]; 'D} } -->
   [wf] sequent [squash] { 'H >- member{univ[i:l]; 'T} } -->
   sequent ['ext] { 'H >- member{decl_type[i:l]; alloc_decl{'D; 'T}} }

(*
 * Well-formedness of next_label.
 *)
interactive next_label_wf {| intro_resource [] |} 'H (univ[i:l]) :
   [wf] sequent [squash] { 'H >- member{decl_type[i:l]; 'D} } -->
   [wf] sequent [squash] { 'H >- member{label_type; 'l} } -->
   sequent ['ext] { 'H >- member{label_type; next_label{'D; 'l}} }

(*
 * Well-formedness of state.
 *)
interactive state_wf {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- member{decl_type[i:l]; 'D} } -->
   sequent ['ext] { 'H >- member{univ[i:l]; state{'D}} }

(*
 * Well-formedness of states.
 *)
interactive empty_wf {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- member{state{empty_decl}; empty} }

interactive store_wf1 {| intro_resource [] |} 'H (univ[i:l]) :
   [wf] sequent [squash] { 'H >- member{decl_type[i:l]; 'D} } -->
   [wf] sequent [squash] { 'H >- 'l1 = 'l2 in label_type } -->
   [wf] sequent [squash] { 'H >- member{'T; 'v} } -->
   sequent ['ext] { 'H >- member{state{store_decl{'D; 'l1; 'T}}; store{'s; 'l2; 'v}} }

interactive store_wf2 {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'T} } -->
   [wf] sequent [squash] { 'H >- member{label_type; 'l1} } -->
   [wf] sequent [squash] { 'H >- member{label_type; 'l2} } -->
   [wf] sequent [squash] { 'H >- "not"{.'l1 = 'l2 in label_type} } -->
   [wf] sequent [squash] { 'H >- member{state{'D}; store{'s; 'l2; 'v}} } -->
   sequent ['ext] { 'H >- member{state{store_decl{'D; 'l1; 'T}}; store{'s; 'l2; 'v}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
