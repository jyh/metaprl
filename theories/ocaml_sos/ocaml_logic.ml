(*
 * Utilities for the semantics.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/htmlman/default.html or visit http://metaprl.org/
 * for more information.
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

open Lm_debug
open Lm_printf

let _ =
   show_loading "Loading Ocaml_logic%t"

(*
 * Basic propositional logic.
 *)
declare ptrue
declare pfalse
declare por{'p1; 'p2}
declare pand{'p1; 'p2}
declare pimplies{'p1; 'p2}

(*
 * Two out of three proposititons.
 *)
declare two_values{'p1; 'p2; 'p3}

prim_rw two_values_reduce :
   two_values{'p1; 'p2; 'p3} <-->
      por{pand{'p1; 'p2}; por{pand{'p1; 'p3}; pand{'p2; 'p3}}}

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
