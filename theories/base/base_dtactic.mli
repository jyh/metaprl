(*
 * The D tactic performs a case selection on the conclusion opname.
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

include Base_auto_tactic

open Refiner.Refiner.Term
open Refiner.Refiner.Refine

open Tactic_type
open Tactic_type.Tacticals

open Base_auto_tactic

(*
 * This are the types.
 *)
type elim_data
type intro_data

type intro_option =
   (* Select among multiple introduction rules *)
   SelectOption of int

   (*
    * Function to supply the term arguments of the rule.
    * If the second argument is Some t, then the subterm described by t
    * is passed as the argument to the argument producer.
    *)
 | IntroArgsOption of (tactic_arg -> term -> term list) * term option

type elim_option =
   ThinOption of (int -> tactic)  (* Thin the eliminated hyp, unless overridden *)
 | ElimArgsOption of (tactic_arg -> term -> term list) * term option

resource (term * (int -> tactic), int -> tactic, elim_data, Tactic.pre_tactic * elim_option list) elim
resource (term * tactic, tactic, intro_data, Tactic.pre_tactic * intro_option list) intro

(*
 * The inherited d tactic.
 *)
val d_prec : auto_prec

topval dT : int -> tactic

(*
 * Run dT 0 so many times.
 *)
topval dForT : int -> tactic

val elim_univ_arg : elim_option
val intro_univ_arg : intro_option

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
