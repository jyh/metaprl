(*!
 * @spelling{gt_bool le_bool ge_bool gt le ge nequal}
 *
 * @begin[doc]
 * @module[Itt_nat]
 *
 * Natural numbers
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
extends Itt_equal
extends Itt_rfun
extends Itt_logic
extends Itt_bool
extends Itt_struct3
extends Itt_int_base
extends Itt_int_ext
extends Itt_int_arith
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
open Itt_bool

(*! @doc{@terms} *)

define unfold_nat : nat <--> ({x:int | 'x>=0})

(******************
 *  Display Forms *
 ******************)

define unfoldInd : ind{'n; 'base; k,l. 'up['k;'l]} <-->
                   ind{'n; i,j.it; 'base; k,l . 'up['k;'l]}


(*! @docoff *)

dform nat_prl_df : except_mode [src] :: nat = mathbbN
dform nat_src_df : mode[src] :: nat = `"nat"

dform ind_df : parens :: "prec"[prec_bor] :: except_mode[src] ::
   ind{'x; 'base; k, l. 'up['k; 'l]} =
   szone pushm[3] szone display_ind{'x} space `"where" space display_ind_n space
   `"=" ezone hspace
   ((display_ind_eq{display_var["n":v]{nil};0}) =>
   (display_ind_eq{display_ind_n;'base})) hspace
   ((display_var["n":v]{nil} > 0) => (display_ind_eq{display_ind_n;
   'up[display_var["n":v]{nil}; display_ind{(display_var["n":v]{nil} -@ 1)}]}))
   popm ezone

(*! @doc{@rewrites} *)

interactive_rw reduce_ind_up :
   ('x in nat) -->
   ind{.'x +@ 1; 'base; k,l. 'up['k;'l]} <-->
   ('up['x +@ 1; ind{'x ; 'base; k,l. 'up['k;'l]}])

interactive_rw reduce_ind_base :
   (ind{0; 'base; k,l. 'up['k;'l]}) <-->
   'base

(*! @docoff *)
let resource reduce +=
   [<< ind{.'x +@ 1; 'base; k,l. 'up['k;'l]} >>, reduce_ind_up;
    << ind{0; 'base; k,l. 'up['k;'l]} >>, reduce_ind_base]

(*! @doc{@rules} *)

interactive natType {| intro [] |} 'H :
   sequent ['ext] { 'H >- "type"{nat} }

interactive natMemberEquality {| intro [] |} 'H :
   sequent [squash] { 'H >- 'a='b in int} -->
   sequent [squash] { 'H >- 'a >= 0}  -->
   sequent ['ext] { 'H >- 'a='b in nat}

interactive natMemberZero {| intro [] |} 'H :
   sequent ['ext] { 'H >- 0 in nat}

interactive nat_is_int {| intro[AutoMustComplete] |} 'H:
   sequent [squash] { 'H >- 'a='b in nat} -->
   sequent [squash] { 'H >- 'a='b in int}

interactive natElimination  'H 'J 'v :
   sequent ['ext] { 'H; x: int; v:'x>=0; 'J['x] >- 'C['x]}  -->
   sequent ['ext] { 'H; x: nat; 'J['x] >- 'C['x]}

interactive natInduction {| elim [] |} 'H 'J  :
   sequent ['ext] { 'H; n: nat; 'J['n] >- 'C[0] }  -->
   sequent ['ext] { 'H; n: nat; 'J['n]; m: nat;  z: 'C['m] >- 'C['m +@ 1] }  -->
   sequent ['ext] { 'H; n: nat; 'J['n] >- 'C['n] }

interactive natBackInduction 'H 'n bind{x.'C['x]}  :
   [wf] sequent [squash]{'H >- 'n in nat }  -->
   sequent ['ext] { 'H >- 'C['n] }  -->
   sequent ['ext] { 'H; m: nat;  z: 'C['m +@ 1] >- 'C['m] }  -->
   sequent ['ext] { 'H  >- 'C[0] }

interactive well_ordering_principle 'H bind{i.'P['i]} 'i :
   [wf] sequent [squash] { 'H; n: nat >- "type"{'P['n]} } -->
   [wf] sequent [squash] { 'H >- 'i in nat } -->
   sequent['ext] {'H >-
      all n:nat. ("not"{'P['n]} or "not"{.all n2:nat. ('P['n2] => 'n < 'n2)})} -->
   sequent['ext] {'H >- "not"{'P['i]}}

(*! @docoff *)

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

