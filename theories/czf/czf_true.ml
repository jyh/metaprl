(*
 * Logical true.
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
include Czf_wf

declare "true"

prim_rw unfoldTrue : "true" <--> (0 = 0 in int)

(*
 * True is always true.
 *
 * H >- true
 * by true_intro
 *)
prim true_intro 'H : : sequent { 'H >- "true" } =
   it

(*
 * True is well formed.
 *
 * H >- wf{"true"}
 * by true_wf
 *)
prim true_wf 'H : :
   sequent { 'H >- wf{."true"} } =
   it

(*
 * True is a restricted formula.
 *)
prim true_res 'H : :
   sequent { 'H >- restricted{."true"} } =
   it

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
