(*
 * Empty set.
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

include Czf_itt_member

open Printf
open Mp_debug

open Refiner.Refiner.RefineError
open Mp_resource

open Sequent
open Tacticals
open Conversionals
open Var

open Itt_logic

let _ =
   if !debug_load then
      eprintf "Loading Czf_itt_union%t" eflush

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "union"{'s1; 's2}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw unfold_union : union{'s1; 's2} <-->
   set_ind{'s1; a1, f1, g1.
      set_ind{'s2; a2, f2, g2.
         collect{.Itt_union!union{'a1; 'a2}; x. decide{'x; z. 'f1 'z; z. 'f2 'z}}}}

interactive_rw reduce_union : union{collect{'t1; x1. 'f1['x1]};
                                    collect{'t2; x2. 'f2['x2]}} <-->
   collect{.Itt_union!union{'t1; 't2}; x. decide{'x; z. 'f1['z]; z. 'f2['z]}}

let fold_union = makeFoldC << union{'s1; 's2} >> unfold_union

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform union_df : mode[prl] :: parens :: "prec"[prec_or] :: union{'s1; 's2} =
   slot{'s1} " " cup " " slot{'s2}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Union is a set.
 *)
interactive union_isset 'H :
   sequent ['ext] { 'H >- isset{'s1} } -->
   sequent ['ext] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- isset{union{'s1; 's2}} }

(*
 * Membership in a union.
 *)
interactive union_member_intro_left 'H :
   sequent ['ext] { 'H >- member{'x; 's1} } -->
   sequent ['ext] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- member{'x; union{'s1; 's2}} }

interactive union_member_intro_right 'H :
   sequent ['ext] { 'H >- member{'x; 's2} } -->
   sequent ['ext] { 'H >- isset{'s1} } -->
   sequent ['ext] { 'H >- member{'x; union{'s1; 's2}} }

(*
 * We get a slightly less powerful elim form.
 *)
interactive union_member_elim3 'H 'J 'z :
   sequent ['ext] { 'H; x: member{'y; union{'s1; 's2}}; 'J['x] >- isset{'s1} } -->
   sequent ['ext] { 'H; x: member{'y; union{'s1; 's2}}; 'J['x] >- isset{'s2} } -->
   sequent ['ext] { 'H; x: member{'y; union{'s1; 's2}}; 'J['x]; z: member{'y; 's1} >- 'T['x] } -->
   sequent ['ext] { 'H; x: member{'y; union{'s1; 's2}}; 'J['x]; z: member{'y; 's2} >- 'T['x] } -->
   sequent ['ext] { 'H; x: member{'y; union{'s1; 's2}}; 'J['x] >- 'T['x] }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Sethood.
 *)
let d_union_setT i p =
   if i = 0 then
      union_isset (hyp_count_addr p) p
   else
      raise (RefineError ("d_union_issetT", StringError "no elimination form"))

let union_isset_term = << isset{union{'s1; 's2}} >>

let d_resource = d_resource.resource_improve d_resource (union_isset_term, d_union_setT)

(*
 * Membership.
 *)
let d_unionT i p =
   if i = 0 then
      try
         let j = get_sel_arg p in
         let rule =
            if j = 1 then
               union_member_intro_left
            else
               union_member_intro_right
         in
            rule (hyp_count_addr p) p
      with
         RefineError _ ->
            raise (RefineError ("d_unionT", StringError "d_unionT requires a selT argument"))
   else
      let i, j = hyp_indices p i in
      let z = maybe_new_vars1 p "z" in
         union_member_elim3 i j z p

let union_member_term = << member{'x; union{'s1; 's2}} >>

let d_resource = d_resource.resource_improve d_resource (union_member_term, d_unionT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
