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

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "empty"

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite unfold_empty : empty <--> collect{void; x. 'x}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Empty is a set.
 *)
rule empty_isset 'H :
   sequent ['ext] { 'H >- isset{empty} }

(*
 * Nothing is in the empty set.
 *)
rule empty_member_elim 'H 'J :
   sequent ['ext] { 'H; x: member{'y; empty}; 'J >- 'T }

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
