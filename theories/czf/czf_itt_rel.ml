(*
 * Assert a relation between two sets.
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

include Czf_itt_dall
include Czf_itt_dexists

open Refiner.Refiner.RefineError
open Mp_resource

open Sequent
open Var

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*
 * Relation P holds between the two sets.
 *)
declare rel{a, b. 'P['a; 'b]; 's1; 's2}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

prim_rw unfold_rel : rel{a, b. 'P['a; 'b]; 's1; 's2} <-->
   (dall{'s1; x. dexists{'s2; y. 'P['x; 'y]}} & dall{'s2; y. dexists{'s1; x. 'P['x; 'y]}})

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typehood.
 *)
interactive rel_type 'H 'u 'v :
   sequent [squash] { 'H; u: set; v: set >- "type"{'P['u; 'v]} } -->
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- "type"{rel{x, y. 'P['x; 'y]; 's1; 's2}} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Typehood.
 *)
let d_rel_typeT i p =
   if i = 0 then
      let u, v = maybe_new_vars2 p "u" "v" in
         rel_type (hyp_count_addr p) u v p
   else
      raise (RefineError ("d_rel_typeT", StringError "no elimination form"))

let rel_type_term = << "type"{rel{a, b. 'P['a; 'b]; 's1; 's2}} >>

let d_resource = Mp_resource.improve d_resource (rel_type_term, d_rel_typeT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
