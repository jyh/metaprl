(*
 * Logical false.
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

extends Czf_itt_sep

open Printf
open Mp_debug

open Refiner.Refiner.RefineError

open Tactic_type.Sequent
open Tactic_type.Tacticals

open Dtactic

let _ =
   show_loading "Loading Czf_itt_false%t"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * False is a restricted formula.
 *)
interactive void_fun {| intro [] |} :
   sequent ['ext] { <H> >- fun_prop{x ."void"} }

(*
 * False is a restricted formula.
 *)
interactive void_res {| intro [] |} :
   sequent ['ext] { <H> >- restricted{."void"} }

(*
 * False is a restricted formula.
 *)
interactive false_fun {| intro [] |} :
   sequent ['ext] { <H> >- fun_prop{x ."false"} }

(*
 * False is a restricted formula.
 *)
interactive false_res {| intro [] |} :
   sequent ['ext] { <H> >- restricted{."false"} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)

