(*
 * Display all the elements in a particular theory.
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

include Itt_theory

open Printf
open Mp_debug

open Refiner.Refiner.Refine

open Mp_resource

open Tactic_type.Tacticals
open Tactic_type.Conversionals

open Itt_rfun
open Itt_bool
open Itt_int
open Itt_int_bool

declare fact{'i}

prim_rw reduceFact : fact{'i} <--> ifthenelse{eq_int{'i; 0}; 1; .'i *@ fact{.'i -@ 1}}

let reduce_info =
   [<< fact{'i} >>, reduceFact]

let reduce_resource = Top_conversionals.add_reduce_info reduce_resource reduce_info

dform fact_df : parens :: "prec"[prec_apply] :: fact{'i} =
   `"fact" " " slot{'i}

let redex1C =
   firstC [reduce_beta;
           reduce_eq_int;
           reduce_ifthenelse_true;
           reduce_ifthenelse_false;
           reduce_add;
           reduce_sub;
           reduce_mul;
           reduce_div]

let redex2C =
   reduceFact

let redexC = (repeatC (higherC redex1C) andthenC (higherC redex2C))

interactive fact100 'H :
   sequent ['ext] { 'H >- fact{100} }

interactive fact250 'H :
   sequent ['ext] { 'H >- fact{250} }

interactive fact400 'H :
   sequent ['ext] { 'H >- fact{400} }

interactive fact650 'H :
   sequent ['ext] { 'H >- fact{650} }

let factT = rw (repeatC redexC) 0

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.top"
 * End:
 * -*-
 *)
