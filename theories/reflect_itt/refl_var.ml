(*
 * Vars are lists of atoms and ints.
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
 *)

include Itt_theory

open Mp_resource

open Tacticals
open Conversionals
open Var

open Base_dtactic

open Itt_equal
open Itt_atom_bool

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare vnil
declare var[@t:t]
declare ivar{'i; 'v}
declare tvar{'t; 'v}
declare var_type
declare eq_varc{'v1; 'v2}
declare eq_var{'v1; 'v2}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform vnil_df : mode[prl] :: vnil =
   `""

dform var_df : mode[prl] :: var[@t:t] =
   slot[@t:s]

dform ivar_df : mode[prl] :: ivar{'i; 'v} =
   slot{'v} slot{'i}

dform tvar_df : mode[prl] :: tvar{'t; 'v} =
   slot{'v} slot{'t}

dform var_type_df : mode[prl] :: var_type =
   `"Var"

dform eq_varc_df : mode[prl] :: parens :: "prec"[prec_eq_atom] :: eq_varc{'v1; 'v2} =
   slot{'v1} space `"=v" space slot{'v2}

dform eq_var_df : mode[prl] :: parens :: "prec"[prec_eq_atom] :: eq_var{'v1; 'v2} =
   slot{'v1} space `"=v" space slot{'v2}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

prim_rw unfold_vnil : vnil <--> nil

prim_rw unfold_ivar : ivar{'i; 'v} <-->
   cons{inl{'i}; 'v}

prim_rw unfold_tvar : tvar{'t; 'v} <-->
   cons{inr{'t}; 'v}

prim_rw unfold_var : var[@v:t] <--> tvar{token[@v:t]; vnil}

prim_rw unfold_var_type : var_type <--> list{.int + atom}

prim_rw unfold_eq_varc : eq_varc{'a; 'b} <-->
   decide{'a; x. decide{'b; y. eq_int{'x; 'y}; y. bfalse};
              x. decide{'b; y. bfalse; y. eq_atom{'x; 'y}}}

prim_rw unfold_eq_var : eq_var{'x; 'y} <-->
   (list_ind{'x; lambda{y. list_ind{'y; btrue; h, t, g. bfalse}};
             h1, t1, g1. lambda{y. list_ind{'y; bfalse;
                                   h2, t2, g2. band{eq_varc{'h1; 'h2}; .'g1 't2}}}} 'y)

let fold_vnil = makeFoldC << vnil >> unfold_vnil
let fold_ivar = makeFoldC << ivar{'i; 'v} >> unfold_ivar
let fold_tvar = makeFoldC << tvar{'t; 'v} >> unfold_tvar
let fold_var = makeFoldC << var[@t:t] >> unfold_var
let fold_var_type = makeFoldC << var_type >> unfold_var_type
let fold_eq_varc = makeFoldC << eq_varc{'x; 'y} >> unfold_eq_varc
let fold_eq_var = makeFoldC << eq_var{'x; 'y} >> unfold_eq_var

(************************************************************************
 * REDUCTION                                                            *
 ************************************************************************)

interactive_rw reduce_eq_var_nil1 : eq_var{vnil; vnil} <--> btrue

interactive_rw reduce_eq_var_nil2 : eq_var{vnil; var[@t:t]} <--> bfalse

interactive_rw reduce_eq_var_nil3 : eq_var{vnil; tvar{'t; 'v}} <--> bfalse

interactive_rw reduce_eq_var_nil4 : eq_var{vnil; ivar{'i; 'v}} <--> bfalse

interactive_rw reduce_eq_var_var1 : eq_var{var[@t:t]; vnil} <--> bfalse

interactive_rw reduce_eq_var_var2 : eq_var{var[@t1:t]; var[@t2:t]} <-->
   band{eq_atom{token[@t1:t]; token[@t2:t]}; btrue}

interactive_rw reduce_eq_var_var3 : eq_var{var[@t1:t]; tvar{token[@t2:t]; 'v}} <-->
   band{eq_atom{token[@t1:t]; token[@t2:t]}; eq_var{vnil; 'v}}

interactive_rw reduce_eq_var_var4 : eq_var{var[@t:t]; ivar{'i; 'v}} <--> bfalse

interactive_rw reduce_eq_var_tvar1 : eq_var{tvar{'t; 'v}; vnil} <--> bfalse

interactive_rw reduce_eq_var_tvar2 : eq_var{tvar{token[@t1:t]; 'v}; var[@t2:t]} <-->
   band{eq_atom{token[@t1:t]; token[@t2:t]}; eq_var{'v; vnil}}

interactive_rw reduce_eq_var_tvar3 : eq_var{tvar{'t1; 'v1}; tvar{'t2; 'v2}} <-->
   band{eq_atom{'t1; 't2}; eq_var{'v1; 'v2}}

interactive_rw reduce_eq_var_tvar4 : eq_var{tvar{'t1; 'v1}; ivar{'i2; 'v2}} <--> bfalse

interactive_rw reduce_eq_var_ivar1 : eq_var{ivar{'i1; 'v1}; vnil} <--> bfalse

interactive_rw reduce_eq_var_ivar2 : eq_var{ivar{'i1; 'v1}; var[@t:t]} <--> bfalse

interactive_rw reduce_eq_var_ivar3 : eq_var{ivar{'i1; 'v1}; tvar{'t2; 'v2}} <--> bfalse

interactive_rw reduce_eq_var_ivar4 : eq_var{ivar{'i1; 'v1}; ivar{'i2; 'v2}} <-->
   band{eq_int{'i1; 'i2}; eq_var{'v1; 'v2}}

let reduce_info =
   [<< eq_var{vnil; vnil} >>, reduce_eq_var_nil1;
    << eq_var{vnil; var[@t:t]} >>, reduce_eq_var_nil2;
    << eq_var{vnil; tvar{'t; 'v}} >>, reduce_eq_var_nil3;
    << eq_var{vnil; ivar{'i; 'v}} >>, reduce_eq_var_nil4;
    << eq_var{var[@t:t]; vnil} >>, reduce_eq_var_var1;
    << eq_var{var[@t1:t]; var[@t2:t]} >>, reduce_eq_var_var2;
    << eq_var{var[@t2:t]; tvar{token[@t2:t]; 'v}} >>, reduce_eq_var_var3;
    << eq_var{var[@t:t]; ivar{'i; 'v}} >>, reduce_eq_var_var4;
    << eq_var{tvar{'t1; 'v1}; vnil} >>, reduce_eq_var_tvar1;
    << eq_var{tvar{token[@t1:t]; 'v1}; var[@t2:t]} >>, reduce_eq_var_tvar2;
    << eq_var{tvar{'t1; 'v1}; tvar{'t2; 'v2}} >>, reduce_eq_var_tvar3;
    << eq_var{tvar{'t1; 'v1}; ivar{'i2; 'v2}} >>, reduce_eq_var_tvar4;
    << eq_var{ivar{'i1; 'v1}; vnil} >>, reduce_eq_var_ivar1;
    << eq_var{ivar{'i1; 'v1}; var[@t:t]} >>, reduce_eq_var_ivar2;
    << eq_var{ivar{'i1; 'v1}; tvar{'t2; 'v2}} >>, reduce_eq_var_ivar3;
    << eq_var{ivar{'i1; 'v1}; ivar{'i2; 'v2}} >>, reduce_eq_var_ivar4]

let reduce_resource = add_reduce_info reduce_resource reduce_info

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Var is a type.
 *)
interactive var_type_type 'H : :
   sequent ['ext] { 'H >- "type"{var_type} }

(*
 * Induction.
 *)
interactive var_type_elim 'H 'J 'i 't 'v 'w :
   sequent ['ext] { 'H; x: var_type; 'J['x] >- 'C[vnil] } -->
   sequent ['ext] { 'H; x: var_type; 'J['x]; i: int; v: var_type; w: 'C['v] >- 'C[ivar{'i; 'v}] } -->
   sequent ['ext] { 'H; x: var_type; 'J['x]; t: atom; v: var_type; w: 'C['v] >- 'C[tvar{'t; 'v}] } -->
   sequent ['ext] { 'H; x: var_type; 'J['x] >- 'C['x] }

(*
 * Typehood.
 *)
interactive vnil_wf 'H : :
   sequent ['ext] { 'H >- member{var_type; vnil} }

interactive var_wf 'H : :
   sequent ['ext] { 'H >- member{var_type; var[@t:t]} }

interactive ivar_wf 'H :
   sequent [squash] { 'H >- member{var_type; 'v} } -->
   sequent [squash] { 'H >- member{int; 'i} } -->
   sequent ['ext] { 'H >- member{var_type; ivar{'i; 'v}} }

interactive tvar_wf 'H :
   sequent [squash] { 'H >- member{var_type; 'v} } -->
   sequent [squash] { 'H >- member{atom; 't} } -->
   sequent ['ext] { 'H >- member{var_type; tvar{'t; 'v}} }

interactive eq_var_wf 'H :
   sequent [squash] { 'H >- member{var_type; 'x} } -->
   sequent [squash] { 'H >- member{var_type; 'y} } -->
   sequent ['ext] { 'H >- member{bool; eq_var{'x; 'y}} }

(*
 * Sqiggle equality.
 *)
interactive var_sqequal 'H :
   sequent [squash] { 'H >- 'x = 'y in var_type } -->
   sequent ['ext] { 'H >- Perv!"rewrite"{'x; 'y} }

(*
 * Translate to equality.
 *)
interactive eq_var_assert_intro 'H :
   sequent [squash] { 'H >- 'v1 = 'v2 in var_type } -->
   sequent ['ext] { 'H >- "assert"{eq_var{'v1; 'v2}} }

interactive eq_var_assert_elim2 'H 'J :
   sequent [squash] { 'H; x: "assert"{eq_var{'v1; 'v2}}; 'J['x] >- member{var_type; 'v1} } -->
   sequent [squash] { 'H; x: "assert"{eq_var{'v1; 'v2}}; 'J['x] >- member{var_type; 'v2} } -->
   sequent ['ext] { 'H; x: 'v1 = 'v2 in var_type; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: "assert"{eq_var{'v1; 'v2}}; 'J['x] >- 'C['x] }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Typehood.
 *)
let d_var_type_typeT p =
   var_type_type (Sequent.hyp_count_addr p) p

let var_type_type_term = << "type"{var_type} >>

(*
 * Well-formedness.
 *)
let d_resource = Mp_resource.improve d_resource (var_type_type_term, wrap_intro d_var_type_typeT)

let d_info =
   [<< member{var_type; vnil} >>, vnil_wf;
    << member{var_type; var[@t:t]} >>, var_wf;
    << member{var_type; ivar{'i; 'v}} >>, ivar_wf;
    << member{var_type; tvar{'t; 'v}} >>, tvar_wf;
    << member{bool; eq_var{'v1;'v2}} >>, eq_var_wf]

let d_resource =
   let wrap (t, tac) =
      t, wrap_intro (fun p -> tac (Sequent.hyp_count_addr p) p)
   in
      add_d_info d_resource (List.map wrap d_info)

(*
 * Induction.
 *)
let d_var_typeT i p =
   let j, k = Sequent.hyp_indices p i in
   let i, t, v, w = maybe_new_vars4 p "i" "t" "v" "w" in
      (var_type_elim j k i t v w
       thenLT [addHiddenLabelT "base case";
               addHiddenLabelT "induction step";
               addHiddenLabelT "induction step"]) p

let var_type_term = << var_type >>

let d_resource = Mp_resource.improve d_resource (var_type_term, d_var_typeT)

(*
 * Squiggle equality.
 *)
let varSqequalT p =
   var_sqequal (Sequent.hyp_count_addr p) p

(*
 * Equality.
 *)
let d_eq_var_assertT i p =
   if i = 0 then
      eq_var_assert_intro (Sequent.hyp_count_addr p) p
   else
      let j, k = Sequent.hyp_indices p i in
         eq_var_assert_elim2 j k p

let eq_var_assert_term = << "assert"{eq_var{'v1; 'v2}} >>

let d_resource = Mp_resource.improve d_resource (eq_var_assert_term, d_eq_var_assertT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
