(*!
 * @begin[doc]
 * @module[Itt_cyclic_group]
 *
 * This theory defines cyclic groups.
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
 * Author: Xin Yu
 * @email{xiny@cs.caltech.edu}
 * @end[license]
 *)

(*! @doc{@parents} *)
extends Itt_group
extends Itt_int_base
(*! @docoff *)
extends Itt_int_ext
extends Itt_int_arith

open Printf
open Mp_debug
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
open Tactic_type.Conversionals
open Mptop
open Var

open Base_dtactic
open Base_auto_tactic

open Itt_struct
open Itt_group

let _ =
   show_loading "Loading Itt_cyclic_group%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*! @doc{@terms} *)
declare group_power{'g; 'a; 'n}
declare cycGroup{'g}
declare cycSubg[i:l]{'s; 'g; 'a}
(*! @docoff *)

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 *
 * @end[doc]
 *)
prim_rw unfold_group_power : group_power{'g; 'a; 'n} <-->
   ind{'n; i, j. ('g^inv 'a) *['g] group_power{'g; 'a; ('n +@ 1)}; .'g^"1"; k, l. 'a *['g] group_power{'g; 'a; ('n -@ 1)}}

prim_rw unfold_cycGroup : cycGroup{'g} <-->
   (exst a: 'g^car. all x: 'g^car. exst n: int. ('x = group_power{'g; 'a; 'n} in 'g^car))

prim_rw unfold_cycSubg : cycSubg[i:l]{'s; 'g; 'a} <-->
   ('s^car = {x: 'g^car| exst n: int. 'x = group_power{'g; 'a; 'n} in 'g^car} in univ[i:l] & 's^"*" = 'g^"*" in 's^car -> 's^car -> 's^car)
(*! @docoff *)

let fold_group_power = makeFoldC << group_power{'g; 'a; 'n} >> unfold_group_power
let fold_cycGroup = makeFoldC << cycGroup{'g} >> unfold_cycGroup
let fold_cycSubg = makeFoldC << cycSubg[i:l]{'s; 'g; 'a} >> unfold_cycSubg

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform group_power_df1 : except_mode[src] :: parens :: "prec"[prec_inv] :: group_power{'g; 'a; 'n} =
   math_group_power{'g; 'a; 'n}

dform cycGroup_df : except_mode[src] :: cycGroup{'g} =
   math_cycGroup{'g}

dform cycSubg_df : except_mode[src] :: cycSubg[i:l]{'s; 'g; 'a} =
   math_cycSubg{slot[i:l]; 's; 'g; 'a}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @modsubsection{Group power operation}
 *
 * Well-formedness.
 * @end[doc]
 *)
interactive group_power_wf {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] { 'H >- 'g in group[i:l] } -->
   sequent [squash] { 'H >- 'a in 'g^car } -->
   sequent [squash] { 'H >- 'n in int } -->
   sequent ['ext] { 'H >- group_power{'g; 'a; 'n} in 'g^car }
(*! @docoff *)

(* a ^ 0 = e *)
interactive group_power_0 {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] { 'H >- 'g in group[i:l] } -->
   sequent [squash] { 'H >- 'a in 'g^car } -->
   sequent ['ext] { 'H >- group_power{'g; 'a; 0} = 'g^"1" in 'g^car }

(* a ^ 1 = a *)
interactive group_power_1 {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] { 'H >- 'g in group[i:l] } -->
   sequent [squash] { 'H >- 'a in 'g^car } -->
   sequent ['ext] { 'H >- group_power{'g; 'a; 1} = 'a in 'g^car }

(* a ^ (n + 1) * a ^ (-1) = a ^ n *)
interactive group_power_less {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] { 'H >- 'g in group[i:l] } -->
   sequent [squash] { 'H >- 'a in 'g^car } -->
   sequent [squash] { 'H >- 'n in int } -->
   sequent ['ext] { 'H >- group_power{'g; 'a; ('n +@ 1)} *['g] ('g^inv 'a) = group_power{'g; 'a; 'n} in 'g^car }

(* a ^ n * x = a ^ (n + 1) *)
interactive group_power_more {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] { 'H >- 'g in group[i:l] } -->
   sequent [squash] { 'H >- 'a in 'g^car } -->
   sequent [squash] { 'H >- 'n in int } -->
   sequent ['ext] { 'H >- group_power{'g; 'a; 'n} *['g] 'a = group_power{'g; 'a; ('n +@ 1)} in 'g^car }

(*!
 * @begin[doc]
 *
 * Power reduction 1: $a^m * a^n = a^{m + n}$
 * @end[doc]
 *)
interactive group_power_reduce {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] { 'H >- 'g in group[i:l] } -->
   sequent [squash] { 'H >- 'a in 'g^car } -->
   sequent [squash] { 'H >- 'm in int } -->
   sequent [squash] { 'H >- 'n in int } -->
   sequent ['ext] { 'H >- group_power{'g; 'a; 'm} *['g] group_power{'g; 'a; 'n} = group_power{'g; 'a; ('m +@ 'n)} in 'g^car }
(*! @docoff *)

interactive group_power_inv_reduce {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] { 'H >- 'g in group[i:l] } -->
   sequent [squash] { 'H >- 'a in 'g^car } -->
   sequent [squash] { 'H >- 'n in int } -->
   sequent ['ext] { 'H >- 'g^inv group_power{'g; 'a; 'n} = group_power{'g; 'a; (-'n)} in 'g^car }

(*!
 * @begin[doc]
 *
 * Power reduction 2: $(a^m)^n = a^{m * n}$
 * @end[doc]
 *)
interactive group_power_power_reduce {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] { 'H >- 'g in group[i:l] } -->
   sequent [squash] { 'H >- 'a in 'g^car } -->
   sequent [squash] { 'H >- 'm in int } -->
   sequent [squash] { 'H >- 'n in int } -->
   sequent ['ext] { 'H >- group_power{'g; group_power{'g; 'a; 'm}; 'n} = group_power{'g; 'a; ('m *@ 'n)} in 'g^car }

(*!
 * @begin[doc]
 *
 * If $s$ is a subgroup of $g$, the power operation on $s$ is the same as
 * that on $g$.
 * @end[doc]
 *)
interactive subgroup_power {| intro [AutoMustComplete; intro_typeinf <<'g>>] |} 'H group[i:l] :
   [wf] sequent [squash] { 'H >- 's in group[i:l] } -->
   [wf] sequent [squash] { 'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   [wf] sequent [squash] { 'H >- 'a in 's^car } -->
   [wf] sequent [squash] { 'H >- 'n in int } -->
   sequent ['ext] { 'H >- group_power{'s; 'a; 'n} = group_power{'g; 'a; 'n} in 's^car }

(*!
 * @begin[doc]
 * @modsubsection{Cyclic group}
 *
 * @end[doc]
 *)
interactive cycGroup_type {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] { 'H >- 'g in group[i:l] } -->
   sequent ['ext] { 'H >- "type"{cycGroup{'g}} }

interactive cycGroup_intro {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] 'a :
   sequent [squash] { 'H >- 'g in group[i:l] } -->
   sequent [squash] { 'H >- 'a in 'g^car } -->
   sequent ['ext] { 'H; x: 'g^car >- exst n: int. 'x = group_power{'g; 'a; 'n} in 'g^car } -->
   sequent ['ext] { 'H >- cycGroup{'g} }

interactive cycGroup_elim {| elim [elim_typeinf <<'g>>] |} 'H 'J group[i:l] :
   [wf] sequent [squash] { 'H; x: cycGroup{'g}; 'J['x] >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H; x: cycGroup{'g}; 'J['x]; a: 'g^car; b: all x: 'g^car. exst n: int. ('x = group_power{'g; 'a; 'n} in 'g^car) >- 'C['x] } -->
   sequent ['ext] { 'H; x: cycGroup{'g}; 'J['x] >- 'C['x] }

(*!
 * @begin[doc]
 *
 * Every cyclic group is abelian.
 * @end[doc]
 *)
interactive cycGroup_commutative {| intro [AutoMustComplete; intro_typeinf <<'g>>] |} 'H group[i:l] :
   [wf] sequent [squash] { 'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- cycGroup{'g} } -->
   sequent ['ext] { 'H >- isCommutative{'g} }

interactive cycGroup_abelian {| intro [AutoMustComplete] |} 'H :
   [wf] sequent [squash] { 'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- cycGroup{'g} } -->
   sequent ['ext] { 'H >- 'g in abelg[i:l] }
(*! @docoff *)

(*interactive smallest_positive_elim {| elim [] |} 'H 'J :
   sequent ['ext] { 'H; x: exst a: int. ('a > 0 & 'P['a]); 'J['x]; y: exst u: int. ('u > 0 & 'P['u] & all b: int. (('b > 0 & 'P['b]) => 'b < 'u)) >- 'C['x] } -->
   sequent ['ext] { 'H; x: exst a: int. ('a > 0 & 'P['a]); 'J['x] >- 'C['x] }
*)

interactive positive_rule1 {| intro [] |} 'H :
   [wf] sequent [squash] { 'H; a: int >- "type"{'P['a]} } -->
   [wf] sequent [squash] { 'H >- 'n in int } -->
   [wf] sequent ['ext] { 'H >- 'n > 0 } -->
   [decidable] sequent ['ext] { 'H; a: int >- decidable{'P['a]} } -->
   sequent ['ext] { 'H >- (all b: int. ('b > 0 & 'b <= 'n => not{'P['b]})) or (exst u: int. ('u > 0 & 'u <= 'n & 'P['u] & all b: int. (('b > 0 & 'P['b]) => 'b >= 'u))) }

let positiveRule1T p =
   positive_rule1 (hyp_count_addr p) p

interactive smallest_positive {| intro [] |} 'H :
   [wf] sequent [squash] { 'H; a: int >- "type"{'P['a]} } -->
   [decidable] sequent ['ext] { 'H; a: int >- decidable{'P['a]} } -->
   [main] sequent ['ext] { 'H >- exst a: int. ('a > 0 & 'P['a]) } -->
   sequent ['ext] { 'H >- exst u: int. ('u > 0 & 'P['u] & all b: int. (('b > 0 & 'P['b]) => 'b >= 'u)) }

let positiveRule2T p =
   smallest_positive (hyp_count_addr p) p

interactive int_div_rem {| intro [] |} 'H :
   sequent [squash] { 'H >- 'm in int } -->
   sequent [squash] { 'H >- 'k in int } -->
   sequent ['ext] { 'H >- 'k > 0 } -->
   sequent ['ext] { 'H >- exst q: int. exst r: nat. (('m = 'k *@ 'q +@ 'r in int) & 'r < 'k) }

(*!
 * @begin[doc]
 *
 * Every non-trivial subgroup of a cyclic group is cyclic.
 * @end[doc]
 *)
interactive subg_cycGroup 'H group[i:l] 'g :
   [wf] sequent [squash] { 'H >- 's in group[i:l] } -->
   [wf] sequent [squash] { 'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- cycGroup{'g} } -->
   [main] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   [main] sequent ['ext] { 'H >- exst x: 's^car. not {('x = 's^"1" in 's^car)} } -->
   [decidable] sequent ['ext] { 'H; a: int; x: 'g^car >- decidable{(group_power{'g; 'x; 'a} in 's^car)} } -->
   sequent ['ext] { 'H >- cycGroup{'s} }

(*!
 * @begin[doc]
 * @modsubsection{Cyclic subgroup}
 *
 * @end[doc]
 *)
interactive cycSubg_intro {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 's in group[i:l] } -->
   [wf] sequent [squash] { 'H >- 'g in group[i:l] } -->
   [wf] sequent [squash] { 'H >- 'a in 'g^car } -->
   [main] sequent ['ext] { 'H >- 's^car = {x: 'g^car| exst n: int. 'x = group_power{'g; 'a; 'n} in 'g^car} in univ[i:l] } -->
   [main] sequent ['ext] { 'H >- 's^"*" = 'g^"*" in 's^car -> 's^car -> 's^car } -->
   sequent ['ext] { 'H >- cycSubg[i:l]{'s; 'g; 'a} }

interactive cycSubg_elim {| elim [] |} 'H 'J :
   [wf] sequent [squash] { 'H; u: cycSubg[i:l]{'s; 'g; 'a}; 'J['u] >- 's in group[i:l] } -->
   [wf] sequent [squash] { 'H; u: cycSubg[i:l]{'s; 'g; 'a}; 'J['u] >- 'g in group[i:l] } -->
   [wf] sequent [squash] { 'H; u: cycSubg[i:l]{'s; 'g; 'a}; 'J['u] >- 'a in 'g^car } -->
   [main] sequent ['ext] { 'H; u: cycSubg[i:l]{'s; 'g; 'a}; 'J['u]; v: 's^car = {x: 'g^car| exst n: int. 'x = group_power{'g; 'a; 'n} in 'g^car} in univ[i:l]; w: 's^"*" = 'g^"*" in 's^car -> 's^car -> 's^car >- 'C['u] } -->
   sequent ['ext] { 'H; u: cycSubg[i:l]{'s; 'g; 'a}; 'J['u] >- 'C['u] }

(*!
 * @begin[doc]
 *
 * A cyclic subgroup is a subgroup.
 * @end[doc]
 *)
interactive cycsubg_subgroup {| intro [AutoMustComplete; intro_typeinf <<'g>>] |} 'H group[i:l] 'a :
   [wf] sequent [squash] { 'H >- 's in group[i:l] } -->
   [wf] sequent [squash] { 'H >- 'g in group[i:l] } -->
   [wf] sequent [squash] { 'H >- 'a in 'g^car } -->
   [main] sequent ['ext] { 'H >- cycSubg[i:l]{'s; 'g; 'a} } -->
   sequent ['ext] { 'H >- subStructure{'s; 'g} }

(*! @docoff *)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
