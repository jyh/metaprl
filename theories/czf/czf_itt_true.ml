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

extends Czf_itt_sep

open Printf
open Lm_debug

open Refiner.Refiner.RefineError

open Tactic_type.Sequent
open Tactic_type.Tacticals

open Dtactic

let _ =
   show_loading "Loading Czf_itt_true%t"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * True is functional.
 *)
interactive unit_fun {| intro [] |} :
   sequent { <H> >- fun_prop{z. "unit"} }

(*
 * True is a restricted formula.
 *)
interactive unit_res {| intro [] |} :
   sequent { <H> >- restricted{."unit"} }

(*
 * True is a restricted formula.
 *)
interactive true_fun {| intro [] |} :
   sequent { <H> >- fun_prop{x. "true"} }

(*
 * True is a restricted formula.
 *)
interactive true_res {| intro [] |} :
   sequent { <H> >- restricted{. "true"} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
