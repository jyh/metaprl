(*
 * Set of variables.
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

include Refl_var

open Refiner.Refiner.RefineError

open Tacticals
open Conversionals
open Var

open Base_dtactic

open Itt_equal

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare var_set
declare vequal

declare vmember{'v; 's}

declare vempty
declare vsingleton{'v}
declare vunion{'s1; 's2}
declare visect{'s1; 's2}
declare vsub{'s1; 's2}
declare voflist{'sl}

(************************************************************************
 * DISPLAYS                                                             *
 ************************************************************************)

prec prec_vmember
prec prec_vunion
prec prec_visect
prec prec_vsub
prec prec_voflist

prec prec_vunion < prec_visect
prec prec_visect < prec_vunion
prec prec_vsub < prec_vmember
prec prec_vmember < prec_voflist

dform var_set_df : mode[prl] :: var_set =
   `"Var Set"

dform vequal_df : mode[prl] :: vequal = `"VEqual"

dform vmember_df : mode[prl] :: parens :: "prec"[prec_vmember] :: vmember{'v; 's} =
   slot{'v} space Nuprl_font!member space slot{'s}

dform vempty_df : mode[prl] :: vempty = `"{}"

dform vunion_df : mode[prl] :: parens :: "prec"[prec_vunion] :: vunion{'s1; 's2} =
   slot{'s1} space Nuprl_font!cup space slot{'s2}

dform visect_df : mode[prl] :: parens :: "prec"[prec_visect] :: visect{'s1; 's2} =
   slot{'s1} space Nuprl_font!cap space slot{'s2}

dform vsub_df : mode[prl] :: parens :: "prec"[prec_vsub] :: vsub{'s1; 's2} =
   slot{'s1} space `"-" space slot{'s2}

dform voflist_df : mode[prl] :: parens :: "prec"[prec_voflist] :: voflist{'sl} =
   `"of_list " slot{'sl}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

prim_rw unfold_vequal : vequal <--> lambda{v1. lambda{v2. eq_var{'v1; 'v2}}}

prim_rw unfold_var_set : var_set <--> fset{vequal; var_type}

prim_rw unfold_vmember :
   vmember{'v; 's} <--> fmember{vequal; 'v; 's}

prim_rw unfold_vempty :
   vempty <--> fempty

prim_rw unfold_vsingleton :
   vsingleton{'v} <--> fsingleton{'v}

prim_rw unfold_vunion :
   vunion{'s1; 's2} <--> funion{vequal; 's1; 's2}

prim_rw unfold_visect :
   visect{'s1; 's2} <--> fisect{vequal; 's1; 's2}

prim_rw unfold_vsub :
   vsub{'s1; 's2} <--> fsub{vequal; 's1; 's2}

prim_rw unfold_voflist :
   voflist{'sl} <--> foflist{'sl}

let fold_vequal = makeFoldC << vequal >> unfold_vequal
let fold_var_set = makeFoldC << var_set >> unfold_var_set
let fold_vmember = makeFoldC << vmember{'v; 's} >> unfold_vmember
let fold_vempty = makeFoldC << vempty >> unfold_vempty
let fold_vsingleton = makeFoldC << vsingleton{'v} >> unfold_vsingleton
let fold_vunion = makeFoldC << vunion{'s1; 's2} >> unfold_vunion
let fold_visect = makeFoldC << visect{'s1; 's2} >> unfold_visect
let fold_vsub = makeFoldC << vsub{'s1; 's2} >> unfold_vsub
let fold_voflist = makeFoldC << voflist{'sl} >> unfold_voflist

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

interactive vequal_fequalp 'H : :
   sequent ['ext] { 'H >- fequalp{vequal; var_type} }

interactive var_set_wf 'H : :
   sequent ['ext] { 'H >- "type"{var_set} }

(*
 * MEmbership.
 *)
interactive vmember_wf 'H :
   sequent [squash] { 'H >- member{var_type; 'v} } -->
   sequent [squash] { 'H >- member{var_set; 's} } -->
   sequent ['ext] { 'H >- member{bool; vmember{'v; 's}} }

(*
 * Empty.
 *)
interactive vempty_wf 'H : :
   sequent ['ext] { 'H >- member{var_set; vempty} }

interactive vempty_member_elim 'H 'J : :
   sequent ['ext] { 'H; x: "assert"{vmember{'v; vempty}}; 'J['x] >- 'C['x] }

(*
 * Singleton.
 *)
interactive vsingleton_wf 'H :
   sequent [squash] { 'H >- member{var_type; 'v} } -->
   sequent ['ext] { 'H >- member{var_set; vsingleton{'v}} }

interactive vsingleton_member_intro 'H :
   sequent [squash] { 'H >- 'v1 = 'v2 in var_type } -->
   sequent ['ext] { 'H >- "assert"{vmember{'v1; vsingleton{'v2}}} }

interactive vsingleton_member_elim 'H 'J :
   sequent [squash] { 'H; x: "assert"{vmember{'v1; vsingleton{'v2}}}; 'J['x] >- member{var_type; 'v1} } -->
   sequent [squash] { 'H; x: "assert"{vmember{'v1; vsingleton{'v2}}}; 'J['x] >- member{var_type; 'v2} } -->
   sequent ['ext] { 'H; x: 'v1 = 'v2 in var_type; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: "assert"{vmember{'v1; vsingleton{'v2}}}; 'J['x] >- 'C['x] }

(*
 * Union.
 *)
interactive vunion_wf 'H :
   sequent [squash] { 'H >- member{var_set; 's1} } -->
   sequent [squash] { 'H >- member{var_set; 's2} } -->
   sequent ['ext] { 'H >- member{var_set; vunion{'s1; 's2}} }

interactive vunion_member_intro_left 'H :
   sequent [squash] { 'H >- member{var_type; 'v} } -->
   sequent [squash] { 'H >- member{var_set; 's1} } -->
   sequent [squash] { 'H >- member{var_set; 's2} } -->
   sequent [squash] { 'H >- "assert"{vmember{'v; 's1}} } -->
   sequent ['ext] { 'H >- "assert"{vmember{'v; vunion{'s1; 's2}}} }

interactive vunion_member_intro_right 'H :
   sequent [squash] { 'H >- member{var_type; 'v} } -->
   sequent [squash] { 'H >- member{var_set; 's1} } -->
   sequent [squash] { 'H >- member{var_set; 's2} } -->
   sequent [squash] { 'H >- "assert"{vmember{'v; 's2}} } -->
   sequent ['ext] { 'H >- "assert"{vmember{'v; vunion{'s1; 's2}}} }

interactive vunion_member_elim 'H 'J :
   sequent [squash] { 'H; x: "assert"{vmember{'v; vunion{'s1; 's2}}}; 'J['x] >- member{var_type; 'v} } -->
   sequent [squash] { 'H; x: "assert"{vmember{'v; vunion{'s1; 's2}}}; 'J['x] >- member{var_set; 's1} } -->
   sequent [squash] { 'H; x: "assert"{vmember{'v; vunion{'s1; 's2}}}; 'J['x] >- member{var_set; 's2} } -->
   sequent ['ext] { 'H; x: "assert"{vmember{'v; 's1}}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: "assert"{vmember{'v; 's2}}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: "assert"{vmember{'v; vunion{'s1; 's2}}}; 'J['x] >- 'C['x] }

(*
 * Intersection.
 *)
interactive visect_wf 'H :
   sequent [squash] { 'H >- member{var_set; 's1} } -->
   sequent [squash] { 'H >- member{var_set; 's2} } -->
   sequent ['ext] { 'H >- member{var_set; visect{'s1; 's2}} }

interactive visect_member_intro3 'H :
   sequent [squash] { 'H >- member{var_type; 'x} } -->
   sequent [squash] { 'H >- member{var_set; 's1} } -->
   sequent [squash] { 'H >- member{var_set; 's2} } -->
   sequent [squash] { 'H >- "assert"{vmember{'x; 's1}} } -->
   sequent [squash] { 'H >- "assert"{vmember{'x; 's2}} } -->
   sequent ['ext] { 'H >- "assert"{vmember{'x; visect{'s1; 's2}}} }

interactive visect_member_elim3 'H 'J 'u 'v :
   sequent [squash] { 'H; z: "assert"{vmember{'x; visect{'s1; 's2}}}; 'J['z] >- member{var_type; 'x} } -->
   sequent [squash] { 'H; z: "assert"{vmember{'x; visect{'s1; 's2}}}; 'J['z] >- member{var_set; 's1} } -->
   sequent [squash] { 'H; z: "assert"{vmember{'x; visect{'s1; 's2}}}; 'J['z] >- member{var_set; 's2} } -->
   sequent ['ext] { 'H; u: "assert"{vmember{'x; 's1}}; v: "assert"{vmember{'x; 's2}}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; z: "assert"{vmember{'x; visect{'s1; 's2}}}; 'J['z] >- 'C['z] }

(*
 * Subtraction.
 *)
interactive vsub_wf 'H :
   sequent [squash] { 'H >- member{var_set; 's1} } -->
   sequent [squash] { 'H >- member{var_set; 's2} } -->
   sequent ['ext] { 'H >- member{var_set; vsub{'s1; 's2}} }

interactive vsub_member_intro3 'H :
   sequent [squash] { 'H >- member{var_type; 'x} } -->
   sequent [squash] { 'H >- member{var_set; 's1} } -->
   sequent [squash] { 'H >- member{var_set; 's2} } -->
   sequent [squash] { 'H >- "assert"{vmember{'x; 's1}} } -->
   sequent [squash] { 'H >- "assert"{bnot{vmember{'x; 's2}}} } -->
   sequent ['ext] { 'H >- "assert"{vmember{'x; vsub{'s1; 's2}}} }

interactive vsub_member_elim3 'H 'J 'u 'v :
   sequent [squash] { 'H; z: "assert"{vmember{'x; vsub{'s1; 's2}}}; 'J['z] >- member{var_type; 'x} } -->
   sequent [squash] { 'H; z: "assert"{vmember{'x; vsub{'s1; 's2}}}; 'J['z] >- member{var_set; 's1} } -->
   sequent [squash] { 'H; z: "assert"{vmember{'x; vsub{'s1; 's2}}}; 'J['z] >- member{var_set; 's2} } -->
   sequent ['ext] { 'H; u: "assert"{vmember{'x; 's1}}; v: "assert"{bnot{vmember{'x; 's2}}}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; z: "assert"{vmember{'x; vsub{'s1; 's2}}}; 'J['z] >- 'C['z] }

(*
 * Of a list.
 *)
interactive voflist_wf 'H :
   sequent [squash] { 'H >- member{list{var_type}; 'l} } -->
   sequent ['ext] { 'H >- member{var_set; voflist{'l}} }

interactive voflist_member_intro_left 'H :
   sequent [squash] { 'H >- member{list{var_type}; 't} } -->
   sequent [squash] { 'H >- 'v1 = 'v2 in var_type } -->
   sequent ['ext] { 'H >- "assert"{vmember{'v1; voflist{cons{'v2; 't}}}} }

interactive voflist_member_intro_right 'H :
   sequent [squash] { 'H >- member{var_type; 'v1} } -->
   sequent [squash] { 'H >- member{var_type; 'v2} } -->
   sequent [squash] { 'H >- member{list{var_type}; 't} } -->
   sequent [squash] { 'H >- "assert"{vmember{'v1; 't}} } -->
   sequent ['ext] { 'H >- "assert"{vmember{'v1; voflist{cons{'v2; 't}}}} }

interactive voflist_member_elim_nil 'H 'J : :
   sequent ['ext] { 'H; x: "assert"{vmember{'v; voflist{nil}}}; 'J['x] >- 'C['x] }

interactive voflist_member_elim_cons2 'H 'J :
   sequent [squash] { 'H; x: "assert"{vmember{'v1; voflist{cons{'v2; 't}}}}; 'J['x] >- member{var_type; 'v1} } -->
   sequent [squash] { 'H; x: "assert"{vmember{'v1; voflist{cons{'v2; 't}}}}; 'J['x] >- member{var_type; 'v2} } -->
   sequent [squash] { 'H; x: "assert"{vmember{'v1; voflist{cons{'v2; 't}}}}; 'J['x] >- member{list{var_type}; 't} } -->
   sequent ['ext] { 'H; x: 'v1 = 'v2 in var_type; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: "assert"{vmember{'v1; voflist{'t}}}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: "assert"{vmember{'v1; voflist{cons{'v2; 't}}}}; 'J['x] >- 'C['x] }

(*
 * Extensionality.
 *)
interactive var_set_equal 'H 'v 'w :
   sequent [squash] { 'H >- member{var_set; 's1} } -->
   sequent [squash] { 'H >- member{var_set; 's2} } -->
   sequent [squash] { 'H; v: var_type; w: "assert"{vmember{'v; 's2}} >- "assert"{vmember{'v; 's1}} } -->
   sequent [squash] { 'H; v: var_type; w: "assert"{vmember{'v; 's1}} >- "assert"{vmember{'v; 's2}} } -->
   sequent ['ext] { 'H >- 's1 = 's2 in var_set }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let wrap_wf tac i p =
   wrap_intro (tac (Sequent.hyp_count_addr p)
               thenT addHiddenLabelT "wf") i p

let d_vunion_memberT i p =
   if i = 0 then
      let tac =
         if get_sel_arg p = 1 then
            vunion_member_intro_left
         else
            vunion_member_intro_right
      in
         (tac (Sequent.hyp_count_addr p)
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  addHiddenLabelT "main"]) p
   else
      let j, k = Sequent.hyp_indices p i in
         (vunion_member_elim j k
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  addHiddenLabelT "main";
                  addHiddenLabelT "main"]) p

let d_visect_memberT i p =
   if i = 0 then
      (visect_member_intro3 (Sequent.hyp_count_addr p)
       thenLT [addHiddenLabelT "wf";
               addHiddenLabelT "wf";
               addHiddenLabelT "wf";
               addHiddenLabelT "main";
               addHiddenLabelT "main"]) p
   else
      let j, k = Sequent.hyp_indices p i in
      let u, v = maybe_new_vars2 p "u" "v" in
         (visect_member_elim3 j k u v
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  addHiddenLabelT "main"]) p

let d_vsub_memberT i p =
   if i = 0 then
      (vsub_member_intro3 (Sequent.hyp_count_addr p)
       thenLT [addHiddenLabelT "wf";
               addHiddenLabelT "wf";
               addHiddenLabelT "wf";
               addHiddenLabelT "main";
               addHiddenLabelT "main"]) p
   else
      let j, k = Sequent.hyp_indices p i in
      let u, v = maybe_new_vars2 p "u" "v" in
         (vsub_member_elim3 j k u v
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  addHiddenLabelT "main"]) p

let d_voflist_member_nilT i p =
   if i = 0 then
      raise (RefineError ("d_voflist_member_nilT", StringError "no introduction rule"))
   else
      let j, k = Sequent.hyp_indices p i in
         voflist_member_elim_nil j k p

let d_voflist_member_consT i p =
   if i = 0 then
         if get_sel_arg p = 1 then
            (voflist_member_intro_left (Sequent.hyp_count_addr p)
             thenLT [addHiddenLabelT "wf";
                     addHiddenLabelT "main"]) p
         else
            (voflist_member_intro_right (Sequent.hyp_count_addr p)
             thenLT [addHiddenLabelT "wf";
                     addHiddenLabelT "wf";
                     addHiddenLabelT "wf";
                     addHiddenLabelT "main"]) p
   else
      let j, k = Sequent.hyp_indices p i in
         (voflist_member_elim_cons2 j k
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  addHiddenLabelT "main";
                  addHiddenLabelT "main"]) p

let d_var_set_equalT p =
   let v, w = maybe_new_vars2 p "v" "w" in
      (var_set_equal (Sequent.hyp_count_addr p) v w
       thenLT [addHiddenLabelT "wf";
               addHiddenLabelT "wf";
               addHiddenLabelT "main";
               addHiddenLabelT "main"]) p

let d_info =
   [<< "type"{var_set} >>, wrap_wf var_set_wf;
    << member{bool; vmember{'v; 's}} >>, wrap_wf vmember_wf;
    << member{var_set; vempty} >>, wrap_wf vempty_wf;
    << member{var_set; vsingleton{'v}} >>, wrap_wf vsingleton_wf;
    << member{var_set; vunion{'s1; 's2}} >>, wrap_wf vunion_wf;
    << member{var_set; visect{'s1; 's2}} >>, wrap_wf visect_wf;
    << member{var_set; vsub{'s1; 's2}} >>, wrap_wf vsub_wf;
    << member{var_set; voflist{'l}} >>, wrap_wf voflist_wf;
    << "assert"{vmember{'v; vunion{'s1; 's2}}} >>, d_vunion_memberT;
    << "assert"{vmember{'v; visect{'s1; 's2}}} >>, d_visect_memberT;
    << "assert"{vmember{'v; vsub{'s1; 's2}}} >>, d_vsub_memberT;
    << "assert"{vmember{'v; voflist{nil}}} >>, d_voflist_member_nilT;
    << "assert"{vmember{'v; voflist{cons{'h; 't}}}} >>, d_voflist_member_consT;
    << 's1 = 's2 in var_set >>, wrap_intro d_var_set_equalT]

let d_resource = add_d_info d_resource d_info

(*
 * Equality.
 *)
let vequal_equalpT p =
   vequal_fequalp (Sequent.hyp_count_addr p) p

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
