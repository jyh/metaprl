doc <:doc< 
   @begin[doc]
   @module[Itt_cyclic_group]
  
   This theory defines cyclic groups.
   @end[doc]
  
   ----------------------------------------------------------------
  
   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.
  
   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.
  
   Copyright (C) 1998 Jason Hickey, Cornell University
  
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
  
   Author: Xin Yu
   @email{xiny@cs.caltech.edu}
   @end[license]
>>

doc <:doc< @doc{@parents} >>
extends Itt_group
extends Itt_int_base
doc <:doc< @docoff >>
extends Itt_int_ext
extends Itt_int_arith
extends Itt_subset

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

doc <:doc< @doc{@terms} >>
declare group_power{'g; 'a; 'n}
declare cycGroup{'g}
declare cycSubg{'g; 'a}
doc <:doc< @docoff >>

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @rewrites
  
   @end[doc]
>>
prim_rw unfold_group_power : group_power{'g; 'a; 'n} <-->
   ind{'n; i, j. ('g^inv 'a) *['g] group_power{'g; 'a; ('n +@ 1)}; .'g^"1"; k, l. 'a *['g] group_power{'g; 'a; ('n -@ 1)}}

prim_rw unfold_cycGroup : cycGroup{'g} <-->
   (exst a: 'g^car. all x: 'g^car. exst n: int. ('x = group_power{'g; 'a; 'n} in 'g^car))

prim_rw unfold_cycSubg : cycSubg{'g; 'a} <-->
   {car={x: 'g^car| exst n: int. 'x = group_power{'g; 'a; 'n} in 'g^car}; "*"='g^"*"; "1"='g^"1"; inv='g^inv}
doc <:doc< @docoff >>

let fold_group_power = makeFoldC << group_power{'g; 'a; 'n} >> unfold_group_power
let fold_cycGroup = makeFoldC << cycGroup{'g} >> unfold_cycGroup
let fold_cycSubg = makeFoldC << cycSubg{'g; 'a} >> unfold_cycSubg

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform group_power_df1 : except_mode[src] :: parens :: "prec"[prec_inv] :: group_power{'g; 'a; 'n} =
   math_group_power{'g; 'a; 'n}

dform cycGroup_df : except_mode[src] :: cycGroup{'g} =
   math_cycGroup{'g}

dform cycSubg_df : except_mode[src] :: cycSubg{'g; 'a} =
   math_cycSubg{'g; 'a}

(************************************************************************
 * REDUCTIONS                                                           *
 ************************************************************************)

interactive_rw reduce_group_power_0 : group_power{'g; 'a; 0} <--> ('g^"1")

let resource reduce +=
   [<< group_power{'g; 'a; 0} >>, reduce_group_power_0;
    << group_power{'g; 'a; number[n:n]} >>, unfold_group_power]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @modsubsection{Group power operation}
  
   Well-formedness.
   @end[doc]
>>
interactive group_power_wf {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   sequent [squash] { 'H >- 'g in group[i:l] } -->
   sequent [squash] { 'H >- 'a in 'g^car } -->
   sequent [squash] { 'H >- 'n in int } -->
   sequent ['ext] { 'H >- group_power{'g; 'a; 'n} in 'g^car }
doc <:doc< @docoff >>

(* a ^ 0 = e *)
interactive group_power_0 {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   sequent [squash] { 'H >- 'g in group[i:l] } -->
   sequent [squash] { 'H >- 'a in 'g^car } -->
   sequent ['ext] { 'H >- group_power{'g; 'a; 0} = 'g^"1" in 'g^car }

(* a ^ 1 = a *)
interactive group_power_1 {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   sequent [squash] { 'H >- 'g in group[i:l] } -->
   sequent [squash] { 'H >- 'a in 'g^car } -->
   sequent ['ext] { 'H >- group_power{'g; 'a; 1} = 'a in 'g^car }

(* a ^ (n + 1) * a ^ (-1) = a ^ n *)
interactive group_power_less {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   sequent [squash] { 'H >- 'g in group[i:l] } -->
   sequent [squash] { 'H >- 'a in 'g^car } -->
   sequent [squash] { 'H >- 'n in int } -->
   sequent ['ext] { 'H >- group_power{'g; 'a; ('n +@ 1)} *['g] ('g^inv 'a) = group_power{'g; 'a; 'n} in 'g^car }

(* a ^ n * x = a ^ (n + 1) *)
interactive group_power_more {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   sequent [squash] { 'H >- 'g in group[i:l] } -->
   sequent [squash] { 'H >- 'a in 'g^car } -->
   sequent [squash] { 'H >- 'n in int } -->
   sequent ['ext] { 'H >- group_power{'g; 'a; 'n} *['g] 'a = group_power{'g; 'a; ('n +@ 1)} in 'g^car }

doc <:doc< 
   @begin[doc]
  
   Power reduction 1: $a^m * a^n = a^{m + n}$
   @end[doc]
>>
interactive group_power_reduce {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   sequent [squash] { 'H >- 'g in group[i:l] } -->
   sequent [squash] { 'H >- 'a in 'g^car } -->
   sequent [squash] { 'H >- 'm in int } -->
   sequent [squash] { 'H >- 'n in int } -->
   sequent ['ext] { 'H >- group_power{'g; 'a; 'm} *['g] group_power{'g; 'a; 'n} = group_power{'g; 'a; ('m +@ 'n)} in 'g^car }
doc <:doc< @docoff >>

interactive group_power_inv_reduce {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   sequent [squash] { 'H >- 'g in group[i:l] } -->
   sequent [squash] { 'H >- 'a in 'g^car } -->
   sequent [squash] { 'H >- 'n in int } -->
   sequent ['ext] { 'H >- 'g^inv group_power{'g; 'a; 'n} = group_power{'g; 'a; (-'n)} in 'g^car }

doc <:doc< 
   @begin[doc]
  
   Power reduction 2: $(a^m)^n = a^{m * n}$
   @end[doc]
>>
interactive group_power_power_reduce {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   sequent [squash] { 'H >- 'g in group[i:l] } -->
   sequent [squash] { 'H >- 'a in 'g^car } -->
   sequent [squash] { 'H >- 'm in int } -->
   sequent [squash] { 'H >- 'n in int } -->
   sequent ['ext] { 'H >- group_power{'g; group_power{'g; 'a; 'm}; 'n} = group_power{'g; 'a; ('m *@ 'n)} in 'g^car }

doc <:doc< 
   @begin[doc]
  
   If $s$ is a subgroup of $g$, the power operation on $s$ is the same as
   that on $g$.
   @end[doc]
>>
interactive subgroup_power {| intro [AutoMustComplete; intro_typeinf <<'g>>] |} group[i:l] :
   [main] sequent [squash] { 'H >- subgroup[i:l]{'s; 'g} } -->
   [wf] sequent [squash] { 'H >- 'a in 's^car } -->
   [wf] sequent [squash] { 'H >- 'n in int } -->
   sequent ['ext] { 'H >- group_power{'g; 'a; 'n} = group_power{'s; 'a; 'n} in 's^car }

doc <:doc< 
   @begin[doc]
   @modsubsection{Cyclic group}
  
   @end[doc]
>>
interactive cycGroup_type {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   sequent [squash] { 'H >- 'g in group[i:l] } -->
   sequent ['ext] { 'H >- "type"{cycGroup{'g}} }

interactive cycGroup_intro {| intro [intro_typeinf <<'g>>] |} group[i:l] 'a :
   sequent [squash] { 'H >- 'g in group[i:l] } -->
   sequent [squash] { 'H >- 'a in 'g^car } -->
   sequent ['ext] { 'H; x: 'g^car >- exst n: int. 'x = group_power{'g; 'a; 'n} in 'g^car } -->
   sequent ['ext] { 'H >- cycGroup{'g} }

interactive cycGroup_elim {| elim [elim_typeinf <<'g>>] |} 'H group[i:l] :
   [wf] sequent [squash] { 'H; x: cycGroup{'g}; 'J['x] >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H; x: cycGroup{'g}; 'J['x]; a: 'g^car; b: all x: 'g^car. exst n: int. ('x = group_power{'g; 'a; 'n} in 'g^car) >- 'C['x] } -->
   sequent ['ext] { 'H; x: cycGroup{'g}; 'J['x] >- 'C['x] }

doc <:doc< 
   @begin[doc]
  
   Every cyclic group is abelian.
   @end[doc]
>>
interactive cycGroup_commutative {| intro [AutoMustComplete; intro_typeinf <<'g>>] |} group[i:l] :
   [wf] sequent [squash] { 'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- cycGroup{'g} } -->
   sequent ['ext] { 'H >- isCommutative{'g} }

interactive cycGroup_abelian {| intro [AutoMustComplete] |} :
   [wf] sequent [squash] { 'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- cycGroup{'g} } -->
   sequent ['ext] { 'H >- 'g in abelg[i:l] }
doc <:doc< @docoff >>

doc <:doc< 
   @begin[doc]
  
   Every non-trivial subgroup of a cyclic group is cyclic.
   @end[doc]
>>
interactive subg_cycGroup group[i:l] 'g :
   [main] sequent ['ext] { 'H >- cycGroup{'g} } -->
   [main] sequent [squash] { 'H >- subgroup[i:l]{'s; 'g} } -->
   [main] sequent ['ext] { 'H >- exst x: 's^car. not {('x = 's^"1" in 's^car)} } -->
   [decidable] sequent ['ext] { 'H; a: int; x: 'g^car >- decidable{(group_power{'g; 'x; 'a} in 's^car subset 'g^car)} } -->
   sequent ['ext] { 'H >- cycGroup{'s} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Cyclic subgroup}
  
   @end[doc]
>>
interactive cycSubg_intro {| intro [] |} :
   [wf] sequent [squash] { 'H >- 'g in group[i:l] } -->
   [wf] sequent [squash] { 'H >- 'a in 'g^car } -->
   sequent ['ext] { 'H >- cycSubg{'g; 'a} in group[i:l] }

interactive cycSubg_car {| intro [AutoMustComplete] |} :
   [wf] sequent [squash] { 'H >- 'g in group[i:l] } -->
   [wf] sequent [squash] { 'H >- 'a in 'g^car } -->
   sequent ['ext] { 'H >- cycSubg{'g; 'a}^car = {x: 'g^car| exst n: int. 'x = group_power{'g; 'a; 'n} in 'g^car} in univ[i:l] }

interactive cycSubg_op {| intro [AutoMustComplete; intro_typeinf <<'g>>] |} group[i:l] :
   [wf] sequent [squash] { 'H >- 'g in group[i:l] } -->
   [wf] sequent [squash] { 'H >- 'a in 'g^car } -->
   sequent ['ext] { 'H >- cycSubg{'g; 'a}^"*" = 'g^"*" in cycSubg{'g; 'a}^car -> cycSubg{'g; 'a}^car -> cycSubg{'g; 'a}^car }

interactive cycSubg_id {| intro [AutoMustComplete; intro_typeinf <<'g>>] |} group[i:l] :
   [wf] sequent [squash] { 'H >- 'g in group[i:l] } -->
   [wf] sequent [squash] { 'H >- 'a in 'g^car } -->
   sequent ['ext] { 'H >- cycSubg{'g; 'a}^"1" = 'g^"1" in cycSubg{'g; 'a}^car }

interactive cycSubg_inv {| intro [AutoMustComplete; intro_typeinf <<'g>>] |} group[i:l] :
   [wf] sequent [squash] { 'H >- 'g in group[i:l] } -->
   [wf] sequent [squash] { 'H >- 'a in 'g^car } -->
   sequent ['ext] { 'H >- cycSubg{'g; 'a}^inv = 'g^inv in cycSubg{'g; 'a}^car -> cycSubg{'g; 'a}^car }

doc <:doc< 
   @begin[doc]
  
   A cyclic subgroup is a subgroup.
   @end[doc]
>>
interactive cycsubg_subgroup {| intro [AutoMustComplete] |} :
   [wf] sequent [squash] { 'H >- 'g in group[i:l] } -->
   [wf] sequent [squash] { 'H >- 'a in 'g^car } -->
   sequent ['ext] { 'H >- subgroup[i:l]{cycSubg{'g; 'a}; 'g} }
doc <:doc< @docoff >>

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
