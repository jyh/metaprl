(*!
 * @begin[doc]
 * @theory[Czf_itt_empty]
 *
 * The @tt{Czf_itt_empty} module defines an empty set
 * as the set $@collect{x; @void; x}$.  Since the $@void$
 * type is empty, the set has no elements.
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
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
 * @email{jyh@cs.cornell.edu}
 * @end[license]
 *)

(*! @doc{@parents} *)
include Czf_itt_member
(*! @docoff *)

open Printf
open Mp_debug

open Refiner.Refiner.RefineError

open Tactic_type.Sequent
open Mp_resource
open Tactic_type.Tacticals

let _ =
   show_loading "Loading Czf_itt_empty%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*! @doc{@terms} *)
declare "empty"

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 *
 * The empty set uses the empty index type $@void$.
 * @end[doc]
 *)
prim_rw unfold_empty : empty <--> collect{void; x. 'x}
(*! @docoff *)

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform empty_df : empty =
   `"{}"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rules
 *
 * There are only two rules for the empty set: it is
 * a well-formed set, and it has no elements.
 * @end[doc]
 *)
interactive empty_isset {| intro [] |} 'H :
   sequent ['ext] { 'H >- isset{empty} }

(*
 * Nothing is in the empty set.
 *)
interactive empty_member_elim {| elim [] |} 'H 'J :
   sequent ['ext] { 'H; x: mem{'y; empty}; 'J['x] >- 'T['x] }
(*! @docoff *)

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
