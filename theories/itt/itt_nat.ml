(*!
 * @spelling{gt_bool le_bool ge_bool gt le ge nequal mul div rem}
 *
 * @begin[doc]
 * @theory[Itt_int_ext]
 *
 * Some more about integers
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 2001 Alexei Kopylov, Cornell University
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
 * Author: Alexei Kopylov @email{kopylov@cs.cornell.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
include Itt_equal
include Itt_rfun
include Itt_logic
include Itt_bool
include Itt_struct3
include Itt_int_base
include Itt_int_ext
include Itt_int_arith
(*! @docoff *)

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type
open Tactic_type.Tacticals
open Var
open Mptop

open Base_dtactic
open Base_auto_tactic

(* Natural numberas *)

define unfold_nat : nat <--> ({x:int | 'x>=0})

dform nat_prl_df : except_mode [src] :: nat = mathbbN
dform nat_src_df : mode[src] :: nat = `"nat"

interactive natType {| intro [] |} 'H :
   sequent ['ext] { 'H >- "type"{nat} }

interactive natMemberEquality {| intro [] |} 'H :
   sequent [squash] { 'H >- 'a='b in int} -->
   sequent [squash] { 'H >- 'a >= 0}  -->
   sequent ['ext] { 'H >- 'a='b in nat}

interactive natMemberZero {| intro [] |} 'H :
   sequent ['ext] { 'H >- 0 IN nat}

interactive natElimination {| elim [] |} 'H 'J 'v :
   sequent ['ext] { 'H; x: int; v:'x>=0; 'J['x] >- 'C['x]}  -->
   sequent ['ext] { 'H; x: nat; 'J['x] >- 'C['x]}

interactive natInduction  'H 'J  :
   sequent ['ext] { 'H; n: nat; 'J['n] >- 'C[0] }  -->
   sequent ['ext] { 'H; n: nat; 'J['n]; m: nat;  z: 'C['m] >- 'C['m +@ 1] }  -->
   sequent ['ext] { 'H; n: nat; 'J['n] >- 'C['n] }

interactive natBackInduction 'H 'n bind{x.'C['x]}  :
   [wf] sequent [squash]{'H >- 'n IN nat }  -->
   sequent ['ext] { 'H >- 'C['n] }  -->
   sequent ['ext] { 'H; m: nat;  z: 'C['m +@ 1] >- 'C['m] }  -->
   sequent ['ext] { 'H  >- 'C[0] }


let natBackInductionT n p =
   let bind =
      try
         let b = get_with_arg p in
            if is_xbind_term b then
               b
            else
               raise (RefineError ("natBackInduction", StringTermError ("need a \"bind\" term: ", b)))
      with
         RefineError _ ->
               let z = get_opt_var_arg "z" p in
                  mk_xbind_term z (var_subst  (Sequent.concl p) <<0>> z)
   in
      natBackInduction (Sequent.hyp_count_addr p) n bind p



