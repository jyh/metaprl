(*
 * Primitiva interactiveatization of implication.
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

extends Czf_itt_and

open Lm_debug
open Lm_printf

open Dtactic

let _ =
   show_loading "Loading Czf_itt_implies%t"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Implication is restricted.
 *)
interactive fun_fun {| intro [] |} :
   ["wf"] sequent { <H>; w: set >- "type"{'A['w]} } -->
   ["wf"] sequent { <H>; w: set >- "type"{'B['w]} } -->
   sequent { <H> >- fun_prop{x. 'A['x]} } -->
   sequent { <H> >- fun_prop{x. 'B['x]} } -->
   sequent { <H> >- fun_prop{x. 'A['x] -> 'B['x]} }

(*
 * Implication is restricted.
 *)
interactive fun_res1 {| intro [] |} :
   sequent { <H> >- restricted{'A} } -->
   sequent { <H> >- restricted{'B} } -->
   sequent { <H> >- restricted{'A -> 'B} }

(*
 * Implication is restricted.
 *)
interactive implies_fun {| intro [] |} :
   ["wf"] sequent { <H>; w: set >- "type"{'A['w]} } -->
   ["wf"] sequent { <H>; w: set >- "type"{'B['w]} } -->
   sequent { <H> >- fun_prop{x. 'A['x]} } -->
   sequent { <H> >- fun_prop{x. 'B['x]} } -->
   sequent { <H> >- fun_prop{x. "implies"{'A['x]; 'B['x]}} }

(*
 * Implication is restricted.
 *)
interactive implies_res1 {| intro [] |} :
   sequent { <H> >- restricted{. 'A} } -->
   sequent { <H> >- restricted{. 'B} } -->
   sequent { <H> >- restricted{. "implies"{'A; 'B}} }

(*
 * Implication is restricted.
 *)
interactive iff_fun {| intro [] |} :
   ["wf"] sequent { <H>; w: set >- "type"{'A['w]} } -->
   ["wf"] sequent { <H>; w: set >- "type"{'B['w]} } -->
   sequent { <H> >- fun_prop{x. 'A['x]} } -->
   sequent { <H> >- fun_prop{x. 'B['x]} } -->
   sequent { <H> >- fun_prop{x. "iff"{'A['x]; 'B['x]}} }

(*
 * Implication is restricted.
 *)
interactive iff_res1 {| intro [] |} :
   sequent { <H> >- restricted{. 'A} } -->
   sequent { <H> >- restricted{. 'B} } -->
   sequent { <H> >- restricted{. "iff"{'A; 'B}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
