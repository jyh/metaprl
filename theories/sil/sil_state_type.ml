(*
 * Type judgments for the state.
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

include Sil_state

open Tactic_type

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

(*
 * Type definitions.
 *)
declare label_type

declare decl_type[i:l]
declare state_empty_decl
declare state_alloc_decl{'r; 't}
declare state_store_decl{'r; 'l; 't}

declare in_domain{'r; 'decl}

declare state_type{'decl}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform label_type_df : label_type =
   `"Label"

dform decl_type_df : decl_type[i:l] =
   `"Decl[" slot[i:l] `"]"

dform in_domain_df : in_domain{'r; 'l} =
   slot{'l} " " Nuprl_font!member `" Dom(" slot{'r} `")"

dform state_empty_decl_df : state_empty_decl =
   `"[]"

dform state_alloc_decl_df : state_alloc_decl{'r; 't} =
   slot{'r} `"@" slot{'t}

dform state_store_decl_df : state_store_decl{'r; 'l; 't} =
   slot{'r} `"." slot{'l} `"=" slot{'t}

dform state_type_df : state_type{'decl} =
   `"{" slot{'decl} `"}"

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

prim_rw unfold_label_type : label_type <--> int

prim_rw unfold_decl_type : decl_type[i:l] <--> list{univ[i:l]}

prim_rw unfold_in_domain : in_domain{'r; 'l} <--> (ge{'l; 0} & lt{'l; length{'r}})

prim_rw unfold_state_empty_decl : state_empty_decl <--> nil

prim_rw unfold_state_alloc_decl : state_alloc_decl{'r; 't} <-->
   append{'r; cons{'t; nil}}

prim_rw unfold_state_store_decl : state_store_decl{'r; 'l; 't} <-->
   replace_nth{'r; 'l; 't}

prim_rw unfold_state_type : state_type{'decl} <-->
   (l: { i: label_type | in_domain{'decl; 'i} } -> nth{'decl; 'l})

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Need this unhiding.
 *)
interactive unhide_in_domain {| elim [] |} 'H 'J :
   sequent ['ext] { 'H; u: in_domain{'decl; 'l}; 'J['u] >- 'C['u] } -->
   sequent ['ext] { 'H; u: hide{in_domain{'decl; 'l}}; 'J['u] >- 'C['u] }

(*
 * Typing rules.
 *)
interactive label_type_member {| intro [] |} 'H :
   sequent ['ext] { 'H >- member{univ[i:l]; label_type} }

interactive label_type_type {| intro [] |} 'H :
   sequent ['ext] { 'H >- "type"{label_type} }

interactive in_domain_member {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- member{decl_type[i:l]; 'r} } -->
   [wf] sequent [squash] { 'H >- member{label_type; 'l} } -->
   sequent ['ext] { 'H >- member{univ[i:l]; in_domain{'r; 'l}} }

interactive in_domain_type {| intro [] |} 'H decl_type[i:l] :
   [wf] sequent [squash] { 'H >- member{decl_type[i:l]; 'r} } -->
   [wf] sequent [squash] { 'H >- member{label_type; 'l} } -->
   sequent ['ext] { 'H >- "type"{in_domain{'r; 'l}} }

interactive empty_member {| intro [] |} 'H :
   sequent ['ext] { 'H >- member{decl_type[i:l]; state_empty_decl} }

interactive alloc_member {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- member{decl_type[i:l]; 'r} } -->
   [wf] sequent [squash] { 'H >- member{univ[i:l]; 't} } -->
   sequent ['ext] { 'H >- member{decl_type[i:l]; state_alloc_decl{'r; 't}} }

interactive store_member {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- member{decl_type[i:l]; 'r} } -->
   [wf] sequent [squash] { 'H >- in_domain{'r; 'l} } -->
   [wf] sequent [squash] { 'H >- member{univ[i:l]; 't} } -->
   sequent [squash] { 'H >- member{decl_type[i:l]; state_store_decl{'r; 'l; 't}} }

interactive state_type_member {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- member{decl_type[i:l]; 'decl} } -->
   sequent ['ext] { 'H >- member{univ[i:l]; state_type{'decl}} }

interactive state_type_type {| intro [] |} 'H decl_type[i:l] :
   [wf] sequent [squash] { 'H >- member{decl_type[i:l]; 'decl} } -->
   sequent ['ext] { 'H >- "type"{state_type{'decl}} }

(*
 * Membership of state operations.
 *)
interactive empty_member2 {| intro [] |} 'H :
   sequent ['ext] { 'H >- member{state_type{state_empty_decl}; empty} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
