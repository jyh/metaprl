doc <:doc< 
   @spelling{gt_bool le_bool ge_bool gt le ge nequal}
  
   @begin[doc]
   @module[Itt_nat]
  
   Theory of natural numbers.
   @end[doc]
  
   ----------------------------------------------------------------
  
   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.
  
   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.
  
   Copyright (C) 2001 Alexei Kopylov, Cornell University
  
   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.
  
   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
  
   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
  
   Author: Alexei Kopylov @email{kopylov@cs.cornell.edu}
   @end[license]
>>

doc <:doc< 
   @begin[doc]
   @parents
   @end[doc]
>>
extends Itt_equal
extends Itt_rfun
extends Itt_logic
extends Itt_bool
extends Itt_struct3
extends Itt_int_base
extends Itt_int_ext
extends Itt_int_arith
doc <:doc< @docoff >>

open Printf
open Lm_debug
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermAddr
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError
open Mp_resource
open Simple_print

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Mptop
open Var

open Dtactic
open Auto_tactic
open Top_conversionals
open Itt_bool

doc <:doc< @doc{@terms} >>

define unfold_nat : nat <--> ({x:int | 'x>=0})
define unfold_finite_nat : nat{'k} <--> int_seg{0; 'k}

let fold_finite_nat = makeFoldC << nat{'k} >> unfold_finite_nat

(******************
 *  Display Forms *
 ******************)

define unfoldInd : ind{'n; 'base; k,l. 'up['k;'l]} <-->
                   ind{'n; i,j.it; 'base; k,l . 'up['k;'l]}


doc <:doc< @docoff >>

dform nat_prl_df : except_mode [src] :: nat = mathbbN
dform nat_src_df : mode[src] :: nat = `"nat"
dform finite_nat_df1 : except_mode [src] :: nat{'k} = mathbbN sub{'k}
dform finite_nat_df2 : mode[src] :: nat{'k} = `"{0..(" slot{'k} `"-1)}"

dform ind_df : parens :: "prec"[prec_bor] :: except_mode[src] ::
   ind{'x; 'base; k, l. 'up['k; 'l]} =
   szone pushm[3] szone display_ind{'x} space `"where" space display_ind_n space
   `"=" ezone hspace
   ((display_ind_eq{math_it["n":s];0}) => (display_ind_eq{display_ind_n;'base})) hspace
   ((math_it["n":s] > 0) => (display_ind_eq{display_ind_n;
   'up[math_it["n":s]; display_ind{(math_it["n":s] -@ 1)}]}))
   popm ezone

doc <:doc< @doc{@rewrites} >>

interactive_rw reduce_ind_up {| reduce |} :
   ('x in nat) -->
   ind{.'x +@ 1; 'base; k,l. 'up['k;'l]} <-->
   ('up['x +@ 1; ind{'x ; 'base; k,l. 'up['k;'l]}])

interactive_rw reduce_ind_base {| reduce |} :
   (ind{0; 'base; k,l. 'up['k;'l]}) <-->
   'base

doc <:doc< @doc{@rules} >>

interactive natType {| intro [] |} :
   sequent { <H> >- "type"{nat} }

interactive natMemberEquality {| intro [] |} :
   sequent { <H> >- 'a='b in int} -->
   sequent { <H> >- 'a >= 0}  -->
   sequent { <H> >- 'a='b in nat}

interactive natMemberZero {| intro [] |} :
   sequent { <H> >- 0 in nat}

interactive nat_is_int {| intro[AutoMustComplete] |} :
   sequent { <H> >- 'a='b in nat} -->
   sequent { <H> >- 'a='b in int}

interactive natElimination  'H :
   sequent { <H>; x: int; v:'x>=0; <J['x]> >- 'C['x]}  -->
   sequent { <H>; x: nat; <J['x]> >- 'C['x]}

interactive natInduction {| elim [] |} 'H  :
   sequent { <H>; n: nat; <J['n]> >- 'C[0] }  -->
   sequent { <H>; n: nat; <J['n]>; m: nat;  z: 'C['m] >- 'C['m +@ 1] }  -->
   sequent { <H>; n: nat; <J['n]> >- 'C['n] }

interactive natBackInduction 'n bind{x.'C['x]}  :
   [wf] sequent { <H> >- 'n in nat }  -->
   sequent { <H> >- 'C['n] }  -->
   sequent { <H>; m: nat;  z: 'C['m +@ 1] >- 'C['m] }  -->
   sequent { <H>  >- 'C[0] }

interactive well_ordering_principle bind{i.'P['i]} 'i :
   [wf] sequent { <H>; n: nat >- "type"{'P['n]} } -->
   [wf] sequent { <H> >- 'i in nat } -->
   sequent{ <H> >-
      all n:nat. ("not"{'P['n]} or "not"{.all n2:nat. ('P['n2] => 'n < 'n2)})} -->
   sequent{ <H> >- "not"{'P['i]}}

interactive finiteNatType {| intro [] |} :
   sequent { <H> >- 'k in int} -->
   sequent { <H> >- "type"{nat{'k}} }

interactive finiteNatMemberEquality {| intro [] |} :
   sequent { <H> >- 'a = 'b in int_seg{0; 'k} } -->
   sequent { <H> >- 'a = 'b in nat{'k} }

interactive finiteNatElimination {| elim [] |} 'H :
   sequent { <H>; x: nat{'k}; <J['x]> >- 'k in int } -->
   sequent { <H>; x: int; v:'x >= 0; w: 'x < 'k; <J['x]> >- 'C['x] }  -->
   sequent { <H>; x: nat{'k}; <J['x]> >- 'C['x] }

doc <:doc< @docoff >>

let natBackInductionT =
   argfunT (fun n p -> natBackInduction n (get_bind_from_arg_or_concl_subst p <<0>>))

(*
 * Some applications
 *)

interactive int_div_rem {| intro [] |} :
   sequent { <H> >- 'm in int } -->
   sequent { <H> >- 'k in int } -->
   sequent { <H> >- 'k > 0 } -->
   sequent { <H> >- exst q: int. exst r: nat. (('m = 'k *@ 'q +@ 'r in int) & 'r < 'k) }

(*
 * If there is a positive number x such that P[x], then there is
 * a smallest positive number k such that P[k], as long as P[y]
 * is well-formed and decidable for any integer y.
 *)
interactive positive_rule1 {| intro [] |} :
   [wf] sequent { <H>; a: int >- "type"{'P['a]} } -->
   [wf] sequent { <H> >- 'n in int } -->
   [wf] sequent { <H> >- 'n > 0 } -->
   [decidable] sequent { <H>; a: int >- decidable{'P['a]} } -->
   sequent { <H> >- (all b: int. ('b > 0 & 'b <= 'n => not{'P['b]})) or (exst u: int. ('u > 0 & 'u <= 'n & 'P['u] & all b: int. (('b > 0 & 'P['b]) => 'b >= 'u))) }

let positiveRule1T = positive_rule1

interactive smallest_positive {| intro [] |} :
   [wf] sequent { <H>; a: int >- "type"{'P['a]} } -->
   [decidable] sequent { <H>; a: int >- decidable{'P['a]} } -->
   [main] sequent { <H> >- exst a: int. ('a > 0 & 'P['a]) } -->
   sequent { <H> >- exst u: int. ('u > 0 & 'P['u] & all b: int. (('b > 0 & 'P['b]) => 'b >= 'u)) }

let positiveRule2T = smallest_positive

(*interactive smallest_positive_elim {| elim [] |} 'H :
   sequent { <H>; x: exst a: int. ('a > 0 & 'P['a]); <J['x]>; y: exst u: int. ('u > 0 & 'P['u] & all b: int. (('b > 0 & 'P['b]) => 'b < 'u)) >- 'C['x] } -->
   sequent { <H>; x: exst a: int. ('a > 0 & 'P['a]); <J['x]> >- 'C['x] }
*)
