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
open Conversionals
open Tacticals
open Var

open Itt_rfun
open Itt_logic

let _ =
   if !debug_load then
      eprintf "Loading Czf_itt_sep%t" eflush

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare sep{'s; x. 'P['x]}
declare restricted{z. 'P['z]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw unfold_sep : sep{'s; x. 'P['x]} <-->
   set_ind{'s; T, f, g. collect{."prod"{'T; t. 'P['f 't]}; z. 'f fst{'z}}}

interactive_rw reduce_sep : sep{collect{'T; x. 'f['x]}; z. 'P['z]} <-->
   collect{. "prod"{'T; t. 'P['f['t]]}; w. 'f[fst{'w}]}

(*
 * A restricted formula has the separation property.
 *)
primrw unfold_restricted : restricted{z. 'P['z]} <-->
   (exst P2: (set -> univ[1:l]). (fun_prop{z. 'P2 'z} & (all z: set. "iff"{. 'P2 'z; 'P['z]})))

primrw unfold_drestricted : restricted{u. 'A['u]; x, y. 'B['x; 'y]} <-->
   (exst P2: (u: set -> 'A['u] -> univ[1:l]).
      (dfun_prop{u. 'A['u]; x, y. 'P2 'x 'y} &
         (all u: set. all x: 'A['u]. "iff"{.'P2 'u 'x; 'B['u; 'x]})))

primrw unfold_restricted2 : restricted{x, y. 'B['x; 'y]} <-->
   (exst P2: (set -> set -> univ[1:l]).
      ((all x: set. fun_prop{y. 'P2 'x 'y})
       & (all y: set. fun_prop{x. 'P2 'x 'y})
       & (all x: set. all y: set. "iff"{.'P2 'x 'y; 'B['x; 'y]})))

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform sep_df : mode[prl] :: sep{'s; x. 'P} =
   szone pushm[3] `"{ " slot{'x} " " Nuprl_font!member " " slot{'s} `" |"
   hspace slot{'P} " " `"}" popm ezone

dform restricted_df : mode[prl] :: parens :: "prec"[prec_quant] :: restricted{z. 'P} =
   Nuprl_font!forall slot{'z} `"." slot{'P} `" res"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Validity of separation.
 *)
interactive sep_isset 'H 'z :
   sequent ['ext] { 'H >- isset{'s} } -->
   sequent [squash] { 'H; z: set >- 'P['z] = 'P['z] in univ[1:l] } -->
   sequent ['ext] { 'H >- isset{.sep{'s; x. 'P['x]}} }

(*
 * Intro form.
 *)
interactive sep_intro2 'H :
   sequent [squash] { 'H; w: set >- 'P['w] = 'P['w] in univ[1:l] } -->
   sequent ['ext] { 'H >- fun_prop{z. 'P['z]} } -->
   sequent ['ext] { 'H >- member{'x; 's} } -->
   sequent ['ext] { 'H >- 'P['x] } -->
   sequent ['ext] { 'H >- member{'x; sep{'s; z. 'P['z]}} }

(*
 * Elim exposes the computational content.
 *)
interactive sep_elim 'H 'J 'u 'v 'z :
   sequent ['ext] { 'H; w: member{'x; sep{'s; y. 'P['y]}}; 'J['w] >- isset{'s} } -->
   sequent [squash] { 'H; w: member{'x; sep{'s; y. 'P['y]}}; 'J['w]; z: set >- 'P['z] = 'P['z] in univ[1:l] } -->
   sequent ['ext] { 'H; w: member{'x; sep{'s; y. 'P['y]}}; 'J['w] >- fun_prop{z. 'P['z]} } -->
   sequent ['ext] { 'H; w: member{'x; sep{'s; y. 'P['y]}}; 'J['w]; u: member{'x; 's}; v: 'P['x] >- 'T['w] } -->
   sequent ['ext] { 'H; w: member{'x; sep{'s; y. 'P['y]}}; 'J['w] >- 'T['w] }

(*
 * Functionality properties.
 *)
interactive sep_fun_set 'H :
   sequent ['ext] { 'H; w: set >- 'P['w] = 'P['w] in univ[1:l] } -->
   sequent ['ext] { 'H >- fun_prop{z. 'P['z]} } -->
   sequent ['ext] { 'H >- eq{'s1; 's2} } -->
   sequent ['ext] { 'H >- eq{sep{'s1; z. 'P['z]}; sep{'s2; z. 'P['z]}} }

interactive sep_fun 'H 'u 'v :
   sequent ['ext] { 'H; u: set; v: set >- 'P['u; 'v] = 'P['u; 'v] in univ[1:l] } -->
   sequent ['ext] { 'H; u: set >- fun_prop{z. 'P['z; 'u]} } -->
   sequent ['ext] { 'H; u: set >- fun_prop{z. 'P['u; 'z]} } -->
   sequent ['ext] { 'H >- fun_set{z. 's['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. sep{'s['z]; x. 'P['x; 'z]}} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Typehood.
 *)
let d_sep_setT i p =
   if i = 0 then
      let z = maybe_new_vars1 p "z" in
         sep_isset (hyp_count_addr p) z p
   else
      raise (RefineError ("d_sep_isset", StringError "no elimination form"))

let sep_isset_term = << isset{sep{'s; x. 'P['x]}} >>

let d_resource = Mp_resource.improve d_resource (sep_isset_term, d_sep_setT)

(*
 * Membership.
 *)
let d_sep_memberT i p =
   if i = 0 then
      (sep_intro2 (hyp_count_addr p)
       thenLT [addHiddenLabelT "wf";
               addHiddenLabelT "wf";
               addHiddenLabelT "main";
               addHiddenLabelT "main"]) p
   else
      let u, v, z = maybe_new_vars3 p "u" "v" "z" in
      let j, k = hyp_indices p i in
         (sep_elim j k u v z
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  addHiddenLabelT "main"]) p

let sep_member_term = << member{'x; sep{'s; y. 'P['y]}} >>

let d_resource = Mp_resource.improve d_resource (sep_member_term, d_sep_memberT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
