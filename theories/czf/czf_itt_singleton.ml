(*
 * Singleton set.
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

open Tactic_type.Sequent
open Mp_resource
open Tactic_type.Tacticals

let _ =
   show_loading "Loading Czf_itt_singleton%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare sing{'s}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

prim_rw unfold_sing : sing{'s} <--> collect{unit; x. 's}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform sing_df : sing{'s} =
   `"{" slot{'s} `"}"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Empty is a set.
 *)
interactive sing_isset {| intro_resource [] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- isset{sing{'s}} }

(*
 * Nothing is in the empty set.
 *)
interactive sing_member_elim {| elim_resource [] |} 'H 'J :
   sequent ['ext] { 'H; x: member{'y; sing{'s}}; 'J['x]; w: eq{'y; 's} >- 'T['x] } -->
   sequent ['ext] { 'H; x: member{'y; sing{'s}}; 'J['x] >- 'T['x] }

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
