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

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.RefineError
open Mp_resource

open Tacticals
open Conversionals
open Var

open Typeinf

open Itt_equal
open Itt_list
open Itt_rfun
open Itt_dprod

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare is_nil{'l}
declare append{'l1; 'l2}
declare ball2{'l1; 'l2; x, y.'b['x; 'y]}
declare assoc{'eq; 'x; 'l; y. 'b['y]; 'z}
declare rev_assoc{'eq; 'x; 'l; y. 'b['y]; 'z}
declare map{'f; 'l}
declare fold_left{'f; 'v; 'l}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_append
prec prec_ball
prec prec_assoc

dform is_nil_df : mode[prl] :: parens :: "prec"[prec_equal] :: is_nil{'l} =
   slot{'l} `" =" subb `" []"

dform append_df : mode[prl] :: parens :: "prec"[prec_append] :: append{'l1; 'l2} =
   slot{'l1} `" @" space slot{'l2}

dform ball2_df : mode[prl] :: parens :: "prec"[prec_ball] :: ball2{'l1; 'l2; x, y. 'b} =
   pushm[3] Nuprl_font!forall subb slot{'x} `", " slot{'y} space
      Nuprl_font!member space slot{'l1} `", " slot{'l2} sbreak["",". "]
      slot{'b} popm

dform assoc_df : mode[prl] :: parens :: "prec"[prec_assoc] :: assoc{'eq; 'x; 'l; v. 'b; 'z} =
   szone pushm[0] pushm[3]
   `"try" hspace
      pushm[3]
      `"let " slot{'v} `" = assoc " slot{'x} space Nuprl_font!member slot{'eq} space slot{'l} popm hspace
      pushm[3] `"in" hspace
      slot{'b} popm popm hspace
   pushm[3] `"with Not_found ->" hspace
   slot{'z} popm popm ezone

dform rev_assoc_df : mode[prl] :: parens :: "prec"[prec_assoc] :: rev_assoc{'eq; 'x; 'l; v. 'b; 'z} =
   szone pushm[0] pushm[3]
   `"try" hspace
      pushm[3]
      `"let " slot{'v} `" = rev_assoc " slot{'x} space Nuprl_font!member slot{'eq} space slot{'l} popm hspace
      pushm[3] `"in" hspace
      slot{'b} popm popm hspace
   pushm[3] `"with Not_found ->" hspace
   slot{'z} popm popm ezone

dform map_df : mode[prl] :: parens :: "prec"[prec_apply] :: map{'f; 'l} =
   `"map" space slot{'f} space slot{'l}

dform fold_left_df : mode[prl] :: fold_left{'f; 'v; 'l} =
   `"fold_left(" slot{'f} `", " slot{'v} `", " slot{'l} `")"

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*
 * Is_nil test.
 *)
prim_rw unfold_is_nil :
   is_nil{'l} <--> list_ind{'l; btrue; h, t, g. bfalse}

let fold_is_nil = makeFoldC << is_nil{'l} >> unfold_is_nil

interactive_rw reduce_is_nil_nil : is_nil{nil} <--> btrue

interactive_rw reduce_is_nil_cons : is_nil{cons{'h; 't}} <--> bfalse

(*
 * Append two lists.
 *)
prim_rw unfold_append :
   append{'l1; 'l2} <-->
      list_ind{'l1; 'l2; h, t, g. 'h :: 'g}

let fold_append = makeFoldC << append{'l1; 'l2} >> unfold_append

interactive_rw reduce_append_nil : append{nil; 'l2} <--> 'l2

interactive_rw reduce_append_cons : append{cons{'x; 'l1}; 'l2} <--> cons{'x; append{'l1; 'l2}}

(*
 * Boolean universal quanitifier.
 *)
prim_rw unfold_ball2 :
   ball2{'l1; 'l2; x, y. 'b['x; 'y]} <-->
      (list_ind{'l1; lambda{z. list_ind{'z; btrue; h, t, g. bfalse}};
                     h1, t1, g1. lambda{z. list_ind{'z; bfalse;
                     h2, t2, g2. band{'b['h1; 'h2]; .'g1 't2}}}} 'l2)

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
prim_rw unfold_assoc :
   assoc{'eq; 'x; 'l; y. 'b['y]; 'z} <-->
      list_ind{'l; 'z; h, t, g.
         spread{'h; u, v.
            ifthenelse{.'eq 'u 'x; 'b['v]; 'g}}}

let fold_assoc = makeFoldC << assoc{'eq; 'x; 'l; v. 'b['v]; 'z} >> unfold_assoc

interactive_rw reduce_assoc_nil :
   assoc{'eq; 'x; nil; y. 'b['y]; 'z} <--> 'z

interactive_rw reduce_assoc_cons :
   assoc{'eq; 'x; cons{pair{'u; 'v}; 'l}; y. 'b['y]; 'z} <-->
      ifthenelse{.'eq 'u 'x; 'b['v]; assoc{'eq; 'x; 'l; y. 'b['y]; 'z}}

prim_rw unfold_rev_assoc :
   rev_assoc{'eq; 'x; 'l; y. 'b['y]; 'z} <-->
      list_ind{'l; 'z; h, t, g.
         spread{'h; u, v.
            ifthenelse{.'eq 'v 'x; 'b['u]; 'g}}}

let fold_rev_assoc = makeFoldC << rev_assoc{'eq; 'x; 'l; v. 'b['v]; 'z} >> unfold_rev_assoc

interactive_rw reduce_rev_assoc_nil :
   rev_assoc{'eq; 'x; nil; y. 'b['y]; 'z} <--> 'z

interactive_rw reduce_rev_assoc_cons :
   rev_assoc{'eq; 'x; cons{pair{'u; 'v}; 'l}; y. 'b['y]; 'z} <-->
      ifthenelse{.'eq 'v 'x; 'b['u]; rev_assoc{'eq; 'x; 'l; y. 'b['y]; 'z}}

(*
 * Maps.
 *)
prim_rw unfold_map : map{'f; 'l} <-->
   list_ind{'l; nil; h, t, g. cons{.'f 'h; 'g}}

let fold_map = makeFoldC << map{'f; 'l} >> unfold_map

interactive_rw reduce_map_nil :
   map{'f; nil} <--> nil

interactive_rw reduce_map_cons :
   map{'f; cons{'h; 't}} <--> cons{.'f 'h; map{'f; 't}}

(*
 * Fold left.
 *)
prim_rw unfold_fold_left :
   fold_left{'f; 'v; 'l} <-->
      (list_ind{'l; lambda{v. 'v}; h, t, g. lambda{v. 'g ('f 'h 'v)}} 'v)

let fold_fold_left = makeFoldC << fold_left{'f; 'v; 'l} >> unfold_fold_left

interactive_rw reduce_fold_left_nil :
   fold_left{'f; 'v; nil} <--> 'v

interactive_rw reduce_fold_left_cons :
   fold_left{'f; 'v; cons{'h; 't}} <-->
   fold_left{'f; .'f 'h 'v; 't}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Is_nil.
 *)
interactive is_nil_wf 'H 'T :
   sequent [squash] { 'H >- member{list{'T}; 'l} } -->
   sequent ['ext] { 'H >- member{bool; is_nil{'l}} }

(*
 * Append.
 *)
interactive append_wf2 'H :
   sequent [squash] { 'H >- member{list{'T}; 'l1} } -->
   sequent [squash] { 'H >- member{list{'T}; 'l2} } -->
   sequent ['ext] { 'H >- member{list{'T}; append{'l1; 'l2}} }

(*
 * Ball2.
 *)
interactive ball2_wf2 'H 'T1 'T2 'u 'v :
   sequent [squash] { 'H >- "type"{'T1} } -->
   sequent [squash] { 'H >- "type"{'T2} } -->
   sequent [squash] { 'H >- member{list{'T1}; 'l1} } -->
   sequent [squash] { 'H >- member{list{'T2}; 'l2} } -->
   sequent [squash] { 'H; u: 'T1; v: 'T2 >- member{bool; 'b['u; 'v]} } -->
   sequent ['ext] { 'H >- member{bool; ball2{'l1; 'l2; x, y. 'b['x; 'y]}} }

(*
 * assoc2.
 *)
interactive assoc_wf 'H 'z 'T1 'T2 :
   sequent [squash] { 'H >- "type"{'T2} } -->
   sequent [squash] { 'H >- member{.'T1 -> 'T1 -> bool; 'eq} } -->
   sequent [squash] { 'H >- member{'T1; 'x} } -->
   sequent [squash] { 'H >- member{list{.'T1 * 'T2}; 'l} } -->
   sequent [squash] { 'H; z: 'T2 >- member{'T; 'b['z]} } -->
   sequent [squash] { 'H >- member{'T; 'z} } -->
   sequent ['ext] { 'H >- member{'T; assoc{'eq; 'x; 'l; v. 'b['v]; 'z}} }

interactive rev_assoc_wf 'H 'z 'T1 'T2 :
   sequent [squash] { 'H >- "type"{'T1} } -->
   sequent [squash] { 'H >- member{.'T2 -> 'T2 -> bool; 'eq} } -->
   sequent [squash] { 'H >- member{'T2; 'x} } -->
   sequent [squash] { 'H >- member{list{.'T1 * 'T2}; 'l} } -->
   sequent [squash] { 'H; z: 'T1 >- member{'T; 'b['z]} } -->
   sequent [squash] { 'H >- member{'T; 'z} } -->
   sequent ['ext] { 'H >- member{'T; rev_assoc{'eq; 'x; 'l; v. 'b['v]; 'z}} }

(*
 * map.
 *)
interactive map_wf 'H 'T1 :
   sequent [squash] { 'H >- "type"{'T1} } -->
   sequent [squash] { 'H >- "type"{'T2} } -->
   sequent [squash] { 'H >- member{.'T1 -> 'T2; 'f} } -->
   sequent [squash] { 'H >- member{.list{'T1}; 'l} } -->
   sequent ['ext] { 'H >- member{list{'T2}; map{'f; 'l}} }

(*
 * Fold_left.
 *)
interactive fold_left_wf 'H 'T1 'T2 :
   sequent [squash] { 'H >- "type"{'T1} } -->
   sequent [squash] { 'H >- "type"{'T2} } -->
   sequent [squash] { 'H >- member{.'T1 -> 'T2 -> 'T2; 'f} } -->
   sequent [squash] { 'H >- member{'T2; 'v} } -->
   sequent [squash] { 'H >- member{list{'T1}; 'l} } -->
   sequent ['ext] { 'H >- member{'T2; fold_left{'f; 'v; 'l}} }

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
    << fold_left{'f; 'v; cons{'h; 't}} >>, reduce_fold_left_cons]

let reduce_resource = add_reduce_info reduce_resource reduce_info

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let ball2_term = << ball2{'l1; 'l2; x, y. 'b['x; 'y]} >>
let ball2_opname = opname_of_term ball2_term
let is_ball2_term = is_dep0_dep0_dep2_term ball2_opname
let mk_ball2_term = mk_dep0_dep0_dep2_term ball2_opname
let dest_ball2 = dest_dep0_dep0_dep2_term ball2_opname

(*
 * is_nil.
 *)
let d_is_nil_wfT p =
   let t =
      try get_univ_arg p with
         RefineError _ ->
            let t = Sequent.concl p in
            let _, t = dest_member t in
            let t = one_subterm t in
            let _, t = infer_type p t in
               t
   in
   let t = dest_list t in
      (is_nil_wf (Sequent.hyp_count_addr p) t
       thenT addHiddenLabelT "wf") p

let is_nil_wf_term = << member{bool; is_nil{'l}} >>

let d_resource = Mp_resource.improve d_resource (is_nil_wf_term, wrap_intro d_is_nil_wfT)

(*
 * Append.
 *)
let d_append_memberT p =
   append_wf2 (Sequent.hyp_count_addr p) p

let append_member_term = << member{list{'T}; append{'l1; 'l2}} >>

let d_resource = Mp_resource.improve d_resource (append_member_term, wrap_intro d_append_memberT)

(*
 * ball2.
 *)
let d_ball2_wfT p =
   let concl = Sequent.concl p in
   let _, t = dest_member concl in
   let t1, t2, u, v, _ = dest_ball2 t in
   let t1, t2 =
      try
         let t = get_univ_arg p in
            t, t
      with
         RefineError _ ->
               try
                  let _, t1 = infer_type p t1 in
                  let t1 = dest_list t1 in
                     try
                        let _, t2 = infer_type p t2 in
                        let t2 = dest_list t2 in
                           t1, t2
                     with
                        RefineError _ ->
                           t1, t1
               with
                  RefineError _ ->
                     let _, t2 = infer_type p t2 in
                     let t2 = dest_list t2 in
                        t2, t2
   in
   let u, v = maybe_new_vars2 p u v in
      (ball2_wf2 (Sequent.hyp_count_addr p) t1 t2 u v
       thenT addHiddenLabelT "wf") p

let ball2_member_term = << member{bool; ball2{'l1; 'l2; x, y. 'b['x; 'y]}} >>

let d_resource = Mp_resource.improve d_resource (ball2_member_term, wrap_intro d_ball2_wfT)

(*
 * Assoc.
 *)
let d_assoc_wfT assoc_wf p =
   let t = Sequent.concl p in
   let _, t = dest_member t in
   let v, t =
      match dest_term t with
         { term_terms = [_; _; l; bt; _]} ->
            begin
               let { bterm = l } = dest_bterm l in
                  match dest_bterm bt with
                     { bvars = [v] } ->
                        v, l
                   | _ ->
                        raise (RefineError ("d_assoc_wfT", StringTermError ("not an assoc", t)))
            end
       | _ ->
            raise (RefineError ("d_assoc_wfT", StringTermError ("not an assoc", t)))
   in
   let t =
      try get_univ_arg p with
         RefineError _ ->
            let _, t = infer_type p t in
               t
   in
   let v = maybe_new_vars1 p v in
   let t1, t2 = dest_prod t in
      (assoc_wf (Sequent.hyp_count_addr p) v t1 t2
       thenT addHiddenLabelT "wf") p

let assoc_wf_term = << member{'T; assoc{'eq; 'x; 'l; v. 'b['v]; 'z}} >>
let rev_assoc_wf_term = << member{'T; rev_assoc{'eq; 'x; 'l; v. 'b['v]; 'z}} >>

let d_resource = Mp_resource.improve d_resource (assoc_wf_term, wrap_intro (d_assoc_wfT assoc_wf))
let d_resource = Mp_resource.improve d_resource (rev_assoc_wf_term, wrap_intro (d_assoc_wfT rev_assoc_wf))

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
