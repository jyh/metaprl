(*
 * Testing.
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

open Printf
open Nl_debug

open Refiner.Refiner.Term
open Refiner.Refiner.TermAddr
open Refiner.Refiner.Refine

open Tacticals
open Conversionals

open Base_rewrite
open Base_dtactic
open Base_auto_tactic
open Itt_rfun
open Itt_int
open Itt_equal
open Itt_struct
open Itt_logic
open Itt_dprod
open Itt_prod
open Itt_prop_decide

open Nl

open Test

let _ = set_debug "prop_decide" true

let zi i =
  (let z = goal() in
     if (i=0) then Sequent.concl z
     else          snd(Sequent.nth_hyp z i))

let _ = load "test"
let _ = cd "test"

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
