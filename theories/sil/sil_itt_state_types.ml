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

extends Itt_theory
extends Sil_itt_state
extends Sil_state_types

open Dtactic

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

interactive_rw reduce_next_label3 : next_label{alloc_decl{'D; 'T}; 'l} <-->
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
interactive label_wf {| intro [] |} :
   sequent { <H> >- label_type IN univ[i:l] }

interactive label_type {| intro [] |} :
   sequent { <H> >- "type"{label_type} }

(*
 * Well-formedness of eqlabel_fun
 *)
interactive eq_label_fun_wf {| intro [] |} :
   sequent { <H> >- eq_label_fun IN (label_type -> label_type -> bool) }

(*
 * Type of declaration lists.
 *)
interactive decl_type_wf {| intro [] |} :
   sequent { <H> >- decl_type[i:l] IN univ[i':l] }

interactive empty_decl_wf {| intro [] |} :
   sequent { <H> >- empty_decl IN decl_type[i:l] }

interactive store_decl_wf {| intro [] |} :
   [wf] sequent { <H> >- 'D IN decl_type[i:l] } -->
   [wf] sequent { <H> >- 'l IN label_type } -->
   [wf] sequent { <H> >- 'T IN univ[i:l] } -->
   sequent { <H> >- store_decl{'D; 'l; 'T} IN decl_type[i:l] }

interactive alloc_decl_wf {| intro [] |} :
   [wf] sequent { <H> >- 'D IN decl_type[i:l] } -->
   [wf] sequent { <H> >- 'T IN univ[i:l] } -->
   sequent { <H> >- alloc_decl{'D; 'T} IN decl_type[i:l] }

(*
 * Well-formedness of next_label.
 *)
interactive next_label_wf {| intro [] |} (univ[i:l]) :
   [wf] sequent { <H> >- 'D IN decl_type[i:l] } -->
   [wf] sequent { <H> >- 'l IN label_type } -->
   sequent { <H> >- next_label{'D; 'l} IN label_type }

(*
 * Well-formedness of state.
 *)
interactive state_wf {| intro [] |} :
   [wf] sequent { <H> >- 'D IN decl_type[i:l] } -->
   sequent { <H> >- state{'D} IN univ[i:l] }

(*
 * Well-formedness of states.
 *)
interactive empty_wf {| intro [] |} :
   sequent { <H> >- empty IN state{empty_decl} }

interactive store_wf1 {| intro [] |} (univ[i:l]) :
   [wf] sequent { <H> >- 'D IN decl_type[i:l] } -->
   [wf] sequent { <H> >- 'l1 = 'l2 in label_type } -->
   [wf] sequent { <H> >- 'v IN 'T } -->
   sequent { <H> >- store{'s; 'l2; 'v} IN state{store_decl{'D; 'l1; 'T}} }

interactive store_wf2 {| intro [] |} :
   [wf] sequent { <H> >- "type"{'T} } -->
   [wf] sequent { <H> >- 'l1 IN label_type } -->
   [wf] sequent { <H> >- 'l2 IN label_type } -->
   [wf] sequent { <H> >- "not"{.'l1 = 'l2 in label_type} } -->
   [wf] sequent { <H> >- store{'s; 'l2; 'v} IN state{'D} } -->
   sequent { <H> >- store{'s; 'l2; 'v} IN state{store_decl{'D; 'l1; 'T}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
