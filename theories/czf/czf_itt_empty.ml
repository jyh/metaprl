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

include Czf_itt_set

open Printf
open Mp_debug

open Refiner.Refiner.RefineError

open Tactic_type.Sequent
open Mp_resource
open Tactic_type.Tacticals

let _ =
   if !debug_load then
      eprintf "Loading Czf_itt_empty%t" eflush

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "empty"

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

prim_rw unfold_empty : empty <--> collect{void; x. 'x}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform empty_df : empty =
   `"{}"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Empty is a set.
 *)
interactive empty_isset 'H : :
   sequent ['ext] { 'H >- isset{empty} }

(*
 * Nothing is in the empty set.
 *)
interactive empty_member_elim 'H 'J : :
   sequent ['ext] { 'H; x: member{'y; empty}; 'J >- 'T }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Elim form.
 *)
let d_emptyT i p =
   if i = 0 then
      raise (RefineError ("d_emptyT", StringError "no introduction form for empty"))
   else
      let i, j = hyp_indices p i in
         empty_member_elim i j p

let empty_member_term = << member{'x; empty} >>

let d_resource = Mp_resource.improve d_resource (empty_member_term, d_emptyT)

(*
 * Sethood.
 *)
let d_empty_setT i p =
   if i = 0 then
      empty_isset (hyp_count_addr p) p
   else
      raise (RefineError ("d_empty_setT", StringError "no elimination form"))

let empty_isset_term = << isset{empty} >>

let d_resource = Mp_resource.improve d_resource (empty_isset_term, d_empty_setT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
