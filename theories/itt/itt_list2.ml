(*
 * Additional operations on lists.
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

include Itt_list
include Itt_logic
include Itt_bool
include Itt_int
include Itt_int_bool

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Var

open Typeinf

open Itt_equal
open Itt_list
open Itt_rfun
open Itt_dprod

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

define unfold_is_nil :
   is_nil{'l} <--> list_ind{'l; btrue; h, t, g. bfalse}

define unfold_append :
   append{'l1; 'l2} <-->
      list_ind{'l1; 'l2; h, t, g. 'h :: 'g}

define unfold_ball2 :
   ball2{'l1; 'l2; x, y. 'b['x; 'y]} <-->
      (list_ind{'l1; lambda{z. list_ind{'z; btrue; h, t, g. bfalse}};
                     h1, t1, g1. lambda{z. list_ind{'z; bfalse;
                     h2, t2, g2. band{'b['h1; 'h2]; .'g1 't2}}}} 'l2)

define unfold_assoc :
   assoc{'eq; 'x; 'l; y. 'b['y]; 'z} <-->
      list_ind{'l; 'z; h, t, g.
         spread{'h; u, v.
            ifthenelse{.'eq 'u 'x; 'b['v]; 'g}}}

define unfold_rev_assoc :
   rev_assoc{'eq; 'x; 'l; y. 'b['y]; 'z} <-->
      list_ind{'l; 'z; h, t, g.
         spread{'h; u, v.
            ifthenelse{.'eq 'v 'x; 'b['u]; 'g}}}

define unfold_map : map{'f; 'l} <-->
   list_ind{'l; nil; h, t, g. cons{.'f 'h; 'g}}

define unfold_fold_left :
   fold_left{'f; 'v; 'l} <-->
      (list_ind{'l; lambda{v. 'v}; h, t, g. lambda{v. 'g ('f 'h 'v)}} 'v)

define unfold_length :
   length{'l} <--> list_ind{'l; 0; u, v, g. 'g +@ 1}

define unfold_nth :
   nth{'l; 'i} <-->
      (list_ind{'l; it; u, v, g. lambda{j. ifthenelse{eq_int{'j; 0}; 'u; .'g ('j -@ 1)}}} 'i)

define unfold_replace_nth :
   replace_nth{'l; 'i; 't} <-->
      (list_ind{'l; nil; u, v, g. lambda{j. ifthenelse{eq_int{'j; 0}; cons{'t; 'v}; cons{'u; .'g ('j -@ 1)}}}} 'i)

define unfold_rev : rev{'l} <-->
   list_ind{'l; nil; u, v, g. append{'g; cons{'u; nil} }}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_append
prec prec_ball
prec prec_assoc

dform is_nil_df : except_mode[src] :: parens :: "prec"[prec_equal] :: is_nil{'l} =
   slot{'l} `" =" subb `" []"

dform append_df : except_mode[src] :: parens :: "prec"[prec_append] :: append{'l1; 'l2} =
   slot{'l1} `" @" space slot{'l2}

dform ball2_df : except_mode[src] :: parens :: "prec"[prec_ball] :: ball2{'l1; 'l2; x, y. 'b} =
   pushm[3] Nuprl_font!forall subb slot{'x} `", " slot{'y} space
      Nuprl_font!member space slot{'l1} `", " slot{'l2} sbreak["",". "]
      slot{'b} popm

dform assoc_df : except_mode[src] :: parens :: "prec"[prec_assoc] :: assoc{'eq; 'x; 'l; v. 'b; 'z} =
   szone pushm[0] pushm[3]
   `"try" hspace
      pushm[3]
      `"let " slot{'v} `" = assoc " slot{'x} space Nuprl_font!member slot{'eq} space slot{'l} popm hspace
      pushm[3] `"in" hspace
      slot{'b} popm popm hspace
   pushm[3] `"with Not_found ->" hspace
   slot{'z} popm popm ezone

dform rev_assoc_df : except_mode[src] :: parens :: "prec"[prec_assoc] :: rev_assoc{'eq; 'x; 'l; v. 'b; 'z} =
   szone pushm[0] pushm[3]
   `"try" hspace
      pushm[3]
      `"let " slot{'v} `" = rev_assoc " slot{'x} space Nuprl_font!member slot{'eq} space slot{'l} popm hspace
      pushm[3] `"in" hspace
      slot{'b} popm popm hspace
   pushm[3] `"with Not_found ->" hspace
   slot{'z} popm popm ezone

dform map_df : except_mode[src] :: parens :: "prec"[prec_apply] :: map{'f; 'l} =
   `"map" space slot{'f} space slot{'l}

dform fold_left_df : except_mode[src] :: fold_left{'f; 'v; 'l} =
   `"fold_left(" slot{'f} `", " slot{'v} `", " slot{'l} `")"

dform length_df : except_mode[src] :: length{'l} =
   `"length(" slot{'l} `")"

dform nth_df : except_mode[src] :: nth{'l; 'i} =
   `"nth(" slot{'l} `", " slot{'i} `")"

dform replace_nth_df : except_mode[src] :: replace_nth{'l; 'i; 'v} =
   szone `"replace_nth(" pushm[0] slot{'l} `"," hspace slot{'i} `"," hspace slot{'v} `")" popm ezone

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*
 * Is_nil test.
 *)
let fold_is_nil = makeFoldC << is_nil{'l} >> unfold_is_nil

interactive_rw reduce_is_nil_nil : is_nil{nil} <--> btrue

interactive_rw reduce_is_nil_cons : is_nil{cons{'h; 't}} <--> bfalse

(*
 * Append two lists.
 *)
let fold_append = makeFoldC << append{'l1; 'l2} >> unfold_append

interactive_rw reduce_append_nil : append{nil; 'l2} <--> 'l2

interactive_rw reduce_append_cons : append{cons{'x; 'l1}; 'l2} <--> cons{'x; append{'l1; 'l2}}

(*
 * Boolean universal quanitifier.
 *)
let fold_ball2 = makeFoldC << ball2{'l1; 'l2; x, y. 'b['x; 'y]} >> unfold_ball2

interactive_rw reduce_ball2_nil_nil :
   ball2{nil; nil; x, y. 'b['x; 'y]} <--> btrue

interactive_rw reduce_ball2_nil_cons :
   ball2{nil; cons{'h; 't}; x, y.'b['x; 'y]} <--> bfalse

interactive_rw reduce_ball2_cons_nil :
   ball2{cons{'h; 't}; nil; x, y. 'b['x; 'y]} <--> bfalse

interactive_rw reduce_ball2_cons_cons :
   ball2{cons{'h1; 't1}; cons{'h2; 't2}; x, y. 'b['x; 'y]} <-->
      band{'b['h1; 'h2]; ball2{'t1; 't2; x, y. 'b['x; 'y]}}

(*
 * Association lists.
 *)
let fold_assoc = makeFoldC << assoc{'eq; 'x; 'l; v. 'b['v]; 'z} >> unfold_assoc

interactive_rw reduce_assoc_nil :
   assoc{'eq; 'x; nil; y. 'b['y]; 'z} <--> 'z

interactive_rw reduce_assoc_cons :
   assoc{'eq; 'x; cons{pair{'u; 'v}; 'l}; y. 'b['y]; 'z} <-->
      ifthenelse{.'eq 'u 'x; 'b['v]; assoc{'eq; 'x; 'l; y. 'b['y]; 'z}}

let fold_rev_assoc = makeFoldC << rev_assoc{'eq; 'x; 'l; v. 'b['v]; 'z} >> unfold_rev_assoc

interactive_rw reduce_rev_assoc_nil :
   rev_assoc{'eq; 'x; nil; y. 'b['y]; 'z} <--> 'z

interactive_rw reduce_rev_assoc_cons :
   rev_assoc{'eq; 'x; cons{pair{'u; 'v}; 'l}; y. 'b['y]; 'z} <-->
      ifthenelse{.'eq 'v 'x; 'b['u]; rev_assoc{'eq; 'x; 'l; y. 'b['y]; 'z}}

(*
 * Maps.
 *)
let fold_map = makeFoldC << map{'f; 'l} >> unfold_map

interactive_rw reduce_map_nil :
   map{'f; nil} <--> nil

interactive_rw reduce_map_cons :
   map{'f; cons{'h; 't}} <--> cons{.'f 'h; map{'f; 't}}

(*
 * Fold left.
 *)
let fold_fold_left = makeFoldC << fold_left{'f; 'v; 'l} >> unfold_fold_left

interactive_rw reduce_fold_left_nil :
   fold_left{'f; 'v; nil} <--> 'v

interactive_rw reduce_fold_left_cons :
   fold_left{'f; 'v; cons{'h; 't}} <-->
   fold_left{'f; .'f 'h 'v; 't}

(*
 * Nth element.
 *)
let fold_length = makeFoldC << length{'l} >> unfold_length

interactive_rw reduce_length_nil : length{nil} <--> 0

interactive_rw reduce_length_cons : length{cons{'u; 'v}} <--> (length{'v} +@ 1)

let fold_nth = makeFoldC << nth{'l; 'i} >> unfold_nth

interactive_rw reduce_nth_cons :
   nth{cons{'u; 'v}; 'i} <--> ifthenelse{eq_int{'i; 0}; 'u; nth{'v; .'i -@ 1}}

let fold_replace_nth = makeFoldC << replace_nth{'l; 'i; 't} >> unfold_replace_nth

interactive_rw reduce_replace_nth_cons :
   replace_nth{cons{'u; 'v}; 'i; 't} <-->
      ifthenelse{eq_int{'i; 0}; cons{'t; 'v}; cons{'u; replace_nth{'v; .'i -@ 1; 't}}}

let fold_rev = makeFoldC << rev{'l} >> unfold_rev

interactive_rw reduce_rev_nil : rev{nil} <--> nil

interactive_rw reduce_rev_cons : rev{cons{'u;'v}} <--> append{rev{'v};cons{'u;nil}}

(************************************************************************
 * REDUCTION                                                            *
 ************************************************************************)

let reduce_info =
   [<< is_nil{nil} >>, reduce_is_nil_nil;
    << is_nil{cons{'h; 't}} >>, reduce_is_nil_cons;
    << append{cons{'h; 't}; 'l} >>, reduce_append_cons;
    << append{nil; 'l} >>, reduce_append_nil;
    << ball2{nil; nil; x, y. 'b['x; 'y]} >>, reduce_ball2_nil_nil;
    << ball2{nil; cons{'h; 't}; x, y. 'b['x; 'y]} >>, reduce_ball2_nil_cons;
    << ball2{cons{'h; 't}; nil; x, y. 'b['x; 'y]} >>, reduce_ball2_cons_nil;
    << ball2{cons{'h1; 't1}; cons{'h2; 't2}; x, y. 'b['x; 'y]} >>, reduce_ball2_cons_cons;
    << assoc{'eq; 'x; nil; v. 'b['v]; 'z} >>, reduce_assoc_nil;
    << assoc{'eq; 'x; cons{pair{'u; 'v}; 'l}; y. 'b['y]; 'z} >>, reduce_assoc_cons;
    << rev_assoc{'eq; 'x; nil; v. 'b['v]; 'z} >>, reduce_rev_assoc_nil;
    << rev_assoc{'eq; 'x; cons{pair{'u; 'v}; 'l}; y. 'b['y]; 'z} >>, reduce_rev_assoc_cons;
    << map{'f; nil} >>, reduce_map_nil;
    << map{'f; cons{'h; 't}} >>, reduce_map_cons;
    << fold_left{'f; 'v; nil} >>, reduce_fold_left_nil;
    << fold_left{'f; 'v; cons{'h; 't}} >>, reduce_fold_left_cons;
    << length{nil} >>, reduce_length_nil;
    << length{cons{'u; 'v}} >>, reduce_length_cons;
    << nth{cons{'u; 'v}; 'i} >>, reduce_nth_cons;
    << replace_nth{cons{'u; 'v}; 'i; 't} >>, reduce_replace_nth_cons;
    << rev{nil} >>, reduce_rev_nil;
    << rev{cons{'u;'v}} >> , reduce_rev_cons ]

let reduce_resource = Top_conversionals.add_reduce_info reduce_resource reduce_info

(* We need a proper implementation of rewrites in order to do this.

interactive_rw append_nil 'A :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- 'l IN list{'A} } -->
   sequent ['ext] { 'H>- append{'l;nil} <--> 'l }

let reduce_resource = Top_conversionals.add_reduce_info reduce_resource [ <<append{'a; nil}>>, append_nil ]

interactive_rw rev_append :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- 'a IN list{'A} } -->
   [wf] sequent [squash] { 'H >- 'b IN list{'A} } -->
   sequent ['ext] { 'H>- rev{append{'a;'b}} <--> append{rev{'b};rev{'a}} }

let reduce_resource = Top_conversionals.add_reduce_info reduce_resource [ <<rev{append{'a;'b}}>>, rev_append ]

interactive_rw rev2 :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- 'l IN list{'A} } -->
   sequent ['ext] { 'H>- rev{rev{'l}} <--> 'l }

*)

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Is_nil.
 *)
interactive is_nil_wf {| intro_resource [] |} 'H 'T :
   [wf] sequent [squash] { 'H >- 'l IN list{'T} } -->
   sequent ['ext] { 'H >- is_nil{'l} IN bool }

(*
 * Append.
 *)
interactive append_wf2 {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- 'l1 IN list{'T} } -->
   [wf] sequent [squash] { 'H >- 'l2 IN list{'T} } -->
   sequent ['ext] { 'H >- append{'l1; 'l2} IN list{'T} }

(*
 * Ball2.
 *)
interactive ball2_wf2 {| intro_resource [] |} 'H 'T1 'T2 'u 'v :
   [wf] sequent [squash] { 'H >- "type"{'T1} } -->
   [wf] sequent [squash] { 'H >- "type"{'T2} } -->
   [wf] sequent [squash] { 'H >- 'l1 IN list{'T1} } -->
   [wf] sequent [squash] { 'H >- 'l2 IN list{'T2} } -->
   [wf] sequent [squash] { 'H; u: 'T1; v: 'T2 >- 'b['u; 'v] IN bool } -->
   sequent ['ext] { 'H >- ball2{'l1; 'l2; x, y. 'b['x; 'y]} IN bool }

(*
 * assoc2.
 *)
interactive assoc_wf {| intro_resource [] |} 'H 'z 'T1 'T2 :
   [wf] sequent [squash] { 'H >- "type"{'T2} } -->
   [wf] sequent [squash] { 'H >- 'eq IN 'T1 -> 'T1 -> bool } -->
   [wf] sequent [squash] { 'H >- 'x IN 'T1 } -->
   [wf] sequent [squash] { 'H >- 'l IN list{.'T1 * 'T2} } -->
   [wf] sequent [squash] { 'H; z: 'T2 >- 'b['z] IN 'T } -->
   [wf] sequent [squash] { 'H >- 'z IN 'T } -->
   sequent ['ext] { 'H >- assoc{'eq; 'x; 'l; v. 'b['v]; 'z} IN 'T }

interactive rev_assoc_wf {| intro_resource [] |} 'H 'z 'T1 'T2 :
   [wf] sequent [squash] { 'H >- "type"{'T1} } -->
   [wf] sequent [squash] { 'H >- 'eq IN 'T2 -> 'T2 -> bool } -->
   [wf] sequent [squash] { 'H >- 'x IN 'T2 } -->
   [wf] sequent [squash] { 'H >- 'l IN list{.'T1 * 'T2} } -->
   [wf] sequent [squash] { 'H; z: 'T1 >- 'b['z] IN 'T } -->
   [wf] sequent [squash] { 'H >- 'z IN 'T } -->
   sequent ['ext] { 'H >- rev_assoc{'eq; 'x; 'l; v. 'b['v]; 'z} IN 'T }

(*
 * map.
 *)
interactive map_wf {| intro_resource [] |} 'H 'T1 :
   [wf] sequent [squash] { 'H >- "type"{'T1} } -->
   [wf] sequent [squash] { 'H >- "type"{'T2} } -->
   [wf] sequent [squash] { 'H >- 'f IN 'T1 -> 'T2 } -->
   [wf] sequent [squash] { 'H >- 'l IN list{'T1} } -->
   sequent ['ext] { 'H >- map{'f; 'l} IN list{'T2} }

(*
 * Fold_left.
 *)
interactive fold_left_wf {| intro_resource [] |} 'H 'T1 'T2 :
   [wf] sequent [squash] { 'H >- "type"{'T1} } -->
   [wf] sequent [squash] { 'H >- "type"{'T2} } -->
   [wf] sequent [squash] { 'H >- 'f IN 'T1 -> 'T2 -> 'T2 } -->
   [wf] sequent [squash] { 'H >- 'v IN 'T2 } -->
   [wf] sequent [squash] { 'H >- 'l IN list{'T1} } -->
   sequent ['ext] { 'H >- fold_left{'f; 'v; 'l} IN 'T2 }

(*
 * Length.
 *)
interactive length_wf {| intro_resource [] |} 'H 'T1 :
   [wf] sequent [squash] { 'H >- "type"{'T1} } -->
   [wf] sequent [squash] { 'H >- 'l IN list{'T1} } -->
   sequent ['ext] { 'H >- length{'l} IN int }

interactive nth_wf {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'T} } -->
   [wf] sequent [squash] { 'H >- 'l IN list{'T} } -->
   [wf] sequent [squash] { 'H >- ge{'i; 0} } -->
   [wf] sequent [squash] { 'H >- lt{'i; length{'l}} } -->
   sequent ['ext] { 'H >- nth{'l; 'i} IN 'T }

interactive replace_nth_wf {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'T} } -->
   [wf] sequent [squash] { 'H >- 'l IN list{'T} } -->
   [wf] sequent [squash] { 'H >- ge{'i; 0} } -->
   [wf] sequent [squash] { 'H >- lt{'i; length{'l}} } -->
   [wf] sequent [squash] { 'H >- 't IN 'T } -->
   sequent ['ext] { 'H >- replace_nth{'l; 'i; 't} IN list{'T} }

(*
 * Reverse.
 *)
interactive rev_wf {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- 'l IN list{'A} } -->
   sequent ['ext] { 'H >- rev{'l} IN list{'A} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let ball2_term = << ball2{'l1; 'l2; x, y. 'b['x; 'y]} >>
let ball2_opname = opname_of_term ball2_term
let is_ball2_term = is_dep0_dep0_dep2_term ball2_opname
let mk_ball2_term = mk_dep0_dep0_dep2_term ball2_opname
let dest_ball2 = dest_dep0_dep0_dep2_term ball2_opname

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
