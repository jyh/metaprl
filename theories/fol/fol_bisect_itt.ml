(*
 * Some properties about the intersection of Void and Unit.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of Nuprl-Light, a modular, higher order
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

open Refiner.Refiner.RefineError

(*
 * Intersection bounded by a type.
 *)
interactive bisect_bound_above 'H :
   sequent [squash] { 'H >- subtype{'T1; 'T3} } -->
   sequent [squash] { 'H >- subtype{'T2; 'T3} } -->
   sequent ['ext] { 'H >- subtype{bisect{'T1; 'T2}; 'T3} }

(*
 * Intersection bounded below.
 *)
interactive bisect_bound_below 'H :
   sequent [squash] { 'H >- subtype{'T3; 'T1} } -->
   sequent [squash] { 'H >- subtype{'T3; 'T2} } -->
   sequent ['ext] { 'H >- subtype{'T3; bisect{'T1; 'T2}} }

(*
 * Apply to Void and Unit types.
 *)
let d_bisect_belowT i p =
   if i = 0 then
      bisect_bound_above (Sequent.hyp_count_addr p) p
   else
      raise (RefineError ("d_bisect_belowT", StringError "no elimination form"))

let bisect_below_term = << subtype{bisect{'a; 'b}; 'c} >>

let d_resource = Mp_resource.improve d_resource (bisect_below_term, d_bisect_belowT)

let d_bisect_aboveT i p =
   if i = 0 then
      bisect_bound_above (Sequent.hyp_count_addr p) p
   else
      raise (RefineError ("d_bisect_aboveT", StringError "no elimination form"))

let bisect_above_term = << subtype{'a; bisect{'a; 'b}} >>

let d_resource = Mp_resource.improve d_resource (bisect_above_term, d_bisect_aboveT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
