(*
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
 * Copyright (C) 1999 Jason Hickey, Cornell University
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

include Fol_type

open Tactic_type
open Tactic_type.Tacticals

open Base_auto_tactic

(*
 * Syntax and display.
 *)
declare pred

dform pred_df : pred = `"Pred"

(*
 * Type judgment.
 *)
prim pred_type 'H 'J :
   sequent ['ext] { 'H; x: pred; 'J['x] >- "type"{'x} } = trivial

let d_pred_type i p =
   let j, k = Sequent.hyp_indices p i in
      pred_type j k p

let resource trivial += {
   auto_name = "d_pred_type";
   auto_prec = trivial_prec;
   auto_tac = onSomeHypT d_pred_type
}

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
