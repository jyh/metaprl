doc <:doc< 
   @spelling{group}
  
   @begin[doc]
   @module[Itt_group]
  
   This theory defines groups.
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
extends Itt_grouplikeobj
doc <:doc< @docoff >>
extends Itt_subset
extends Itt_subset2
extends Itt_bisect

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
open Itt_record
open Itt_grouplikeobj
open Itt_squash
open Itt_fun
open Itt_int_ext
open Itt_bisect

let _ =
   show_loading "Loading Itt_group%t"

(************************************************************************
 * GROUP                                                                *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @modsection{Group}
   @modsubsection{Rewrites}
  
   @end[doc]
>>
define unfold_pregroup1 : pregroup[i:l] <-->
   record["inv":t]{r. 'r^car -> 'r^car; premonoid[i:l]}

define unfold_isGroup1 : isGroup{'g} <-->
   isSemigroup{'g} & all x: 'g^car. 'g^"1" *['g] 'x = 'x in 'g^car & all x: 'g^car. ('g^inv 'x) *['g] 'x = 'g^"1" in 'g^car

define unfold_group1 : group[i:l] <-->
   {g: pregroup[i:l] | isGroup{'g}}
doc <:doc< @docoff >>

let unfold_pregroup = unfold_pregroup1 thenC addrC [1] unfold_premonoid
let unfold_isGroup = unfold_isGroup1 thenC addrC [0] unfold_isSemigroup
let unfold_group = unfold_group1 thenC addrC [0] unfold_pregroup thenC addrC [1] unfold_isGroup

let fold_pregroup1 = makeFoldC << pregroup[i:l] >> unfold_pregroup1
let fold_pregroup = makeFoldC << pregroup[i:l] >> unfold_pregroup
let fold_isGroup1 = makeFoldC << isGroup{'g} >> unfold_isGroup1
let fold_isGroup = makeFoldC << isGroup{'g} >> unfold_isGroup
let fold_group1 = makeFoldC << group[i:l] >> unfold_group1
let fold_group = makeFoldC << group[i:l] >> unfold_group

let groupDT n = rw unfold_group n thenT dT n

let resource elim +=
   [<<group[i:l]>>, groupDT]

doc <:doc< 
   @begin[doc]
   @modsubsection{Well-formedness}
  
   @end[doc]
>>
interactive pregroup_wf {| intro [] |} :
   sequent ['ext] { 'H >- "type"{pregroup[i:l]} }

interactive isGroup_wf {| intro [intro_typeinf <<'g>>] |} pregroup[i:l] :
   sequent [squash] { 'H >- 'g in pregroup[i:l] } -->
   sequent ['ext] {'H >- "type"{isGroup{'g}} }

interactive group_wf {| intro [] |} :
   sequent ['ext] { 'H >- "type"{group[i:l]} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction and Elimination}
  
   @end[doc]
>>
interactive pregroup_intro {| intro [AutoMustComplete] |} :
   sequent [squash] { 'H >- 'g in {car: univ[i:l]; "*": ^car -> ^car -> ^car; "1": ^car; inv: ^car -> ^car} } -->
   sequent ['ext] { 'H >- 'g in pregroup[i:l] }

interactive pregroup_elim {| elim [] |} 'H :
   sequent ['ext] { 'H; g: {car: univ[i:l]; "*": ^car -> ^car -> ^car; "1": ^car; inv: ^car -> ^car}; 'J['g] >- 'C['g] } -->
   sequent ['ext] { 'H; g: pregroup[i:l]; 'J['g] >- 'C['g] }

interactive isGroup_intro {| intro [AutoMustComplete] |} :
   [wf] sequent [squash] { 'H >- "type"{.'g^car} } -->
   [main] sequent ['ext] { 'H >- isSemigroup{'g} } -->
   [main] sequent ['ext] { 'H; x: 'g^car >- 'g^"1" *['g] 'x = 'x in 'g^car } -->
   [main] sequent ['ext] { 'H; x: 'g^car >- ('g^inv 'x) *['g] 'x = 'g^"1" in 'g^car } -->
   sequent ['ext] { 'H >- isGroup{'g} }

interactive isGroup_elim {| elim [] |} 'H :
   sequent ['ext] { 'H; u: isGroup{'g}; v: all x: 'g^car. all y: 'g^car. all z: 'g^car. (('x *['g] 'y) *['g] 'z = 'x *['g] ('y *['g] 'z) in 'g^car); w: all x: 'g^car. ('g^"1" *['g] 'x = 'x in 'g^car); x: all x: 'g^car. ('g^inv 'x) *['g] 'x = 'g^"1" in 'g^car; 'J['u] >- 'C['u] } -->
   sequent ['ext] { 'H; u: isGroup{'g}; 'J['u] >- 'C['u] }

interactive group_intro {| intro [AutoMustComplete] |} :
   [wf] sequent [squash] { 'H >- 'g in pregroup[i:l] } -->
   [main] sequent ['ext] { 'H >- isGroup{'g} } -->
   sequent ['ext] { 'H >- 'g in group[i:l] }

interactive group_elim {| elim [] |} 'H :
   sequent ['ext] { 'H; g: {car: univ[i:l]; "*": ^car -> ^car -> ^car; "1": ^car; inv: ^car -> ^car}; u: squash{.all x: 'g^car. all y: 'g^car. all z: 'g^car. (('x *['g] 'y) *['g] 'z = 'x *['g] ('y *['g] 'z) in 'g^car)}; v: squash{.all x: 'g^car. 'g^"1" *['g] 'x = 'x in 'g^car}; w: squash{.all x: 'g^car. ('g^inv 'x) *['g] 'x = 'g^"1" in 'g^car}; 'J['g] >- 'C['g] } -->
   sequent ['ext] { 'H; g: group[i:l]; 'J['g] >- 'C['g] }

interactive car_wf {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent ['ext] {'H >- "type"{('g^car)} }

interactive car_wf2 {| intro [] |} :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent ['ext] {'H >- 'g^car in univ[i:l] }

interactive op_wf {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent ['ext] {'H >- 'g^"*" in 'g^car -> 'g^car -> 'g^car }

interactive inv_wf {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent ['ext] {'H >- 'g^inv in 'g^car -> 'g^car }

interactive op_in_G {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent [squash] {'H >- 'b in 'g^car } -->
   sequent ['ext] {'H >- 'a *['g] 'b in 'g^car }

interactive id_in_G {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent ['ext] {'H >- 'g^"1" in 'g^car }

interactive inv_in_G {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent ['ext] {'H >- 'g^inv 'a in 'g^car }

interactive group_assoc {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent [squash] {'H >- 'b in 'g^car } -->
   sequent [squash] {'H >- 'c in 'g^car } -->
   sequent ['ext] {'H >- ('a *['g] 'b) *['g] 'c = 'a *['g] ('b *['g] 'c) in 'g^car }

interactive group_left_id {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent ['ext] {'H >- 'g^"1" *['g] 'a = 'a in 'g^car }

interactive group_left_inv {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent ['ext] {'H >- ('g^inv 'a) *['g] 'a = 'g^"1" in 'g^car }

interactive op_eq1 {| intro [AutoMustComplete; intro_typeinf <<'g>>] |} group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a = 'b in 'g^car } -->
   sequent [squash] {'H >- 'c in 'g^car } -->
   sequent ['ext] {'H >- 'a *['g] 'c = 'b *['g] 'c in 'g^car }

interactive op_eq2 {| intro [AutoMustComplete; intro_typeinf <<'g>>] |} group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a = 'b in 'g^car } -->
   sequent [squash] {'H >- 'c in 'g^car } -->
   sequent ['ext] {'H >- 'c *['g] 'a = 'c *['g] 'b in 'g^car }

doc <:doc< 
   @begin[doc]
   @modsubsection{Lemmas}
  
     @begin[enumerate]
     @item{$u * u = u$ implies $u$ is the identity.}
     @item{The left inverse is also the right inverse.}
     @item{The left identity is also the right identity.}
     @end[enumerate]
   @end[doc]
>>
interactive id_judge {| elim [elim_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H; x: 'u *['g] 'u = 'u in 'g^car; 'J['x] >- 'g in group[i:l] } -->
   sequent ['ext] {'H; x: 'u *['g] 'u = 'u in 'g^car; 'J['x]; y: 'u = 'g^"1" in 'g^car >- 'C['x] } -->
   sequent ['ext] {'H; x: 'u *['g] 'u = 'u in 'g^car; 'J['x] >- 'C['x] }

interactive right_inv {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent ['ext] {'H >- 'a *['g] ('g^inv 'a) = 'g^"1" in 'g^car }

interactive right_id {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent ['ext] {'H >- 'a *['g] 'g^"1" = 'a in 'g^car }

doc <:doc< 
   @begin[doc]
   @modsubsection{Hierarchy}
  
   A group is also a monoid.
   @end[doc]
>>
interactive group_is_monoid :
   sequent [squash] { 'H >- 'g in group[i:l] } -->
   sequent ['ext] { 'H >- 'g in monoid[i:l] }

doc <:doc< 
   @begin[doc]
   @modsubsection{Theorems}
  
   The left and right cancellation laws.
   @end[doc]
>>
(* Cancellation: a * b = a * c => b = c *)
interactive cancel_left {| elim [elim_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] { 'H; x: 'u *['g] 'v = 'u *['g] 'w in 'g^car; 'J['x] >- 'g in group[i:l] } -->
   sequent [squash] { 'H; x: 'u *['g] 'v = 'u *['g] 'w in 'g^car; 'J['x] >- 'u in 'g^car } -->
   sequent [squash] { 'H; x: 'u *['g] 'v = 'u *['g] 'w in 'g^car; 'J['x] >- 'v in 'g^car } -->
   sequent [squash] { 'H; x: 'u *['g] 'v = 'u *['g] 'w in 'g^car; 'J['x] >- 'w in 'g^car } -->
   sequent ['ext] { 'H; x: 'u *['g] 'v = 'u *['g] 'w in 'g^car; 'J['x] >- 'v = 'w in 'g^car }

(* Cancellation: b * a = c * a => b = c *)
interactive cancel_right {| elim [elim_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] { 'H; x: 'v *['g] 'u = 'w *['g] 'u in 'g^car; 'J['x] >- 'g in group[i:l] } -->
   sequent [squash] { 'H; x: 'v *['g] 'u = 'w *['g] 'u in 'g^car; 'J['x] >- 'u in 'g^car } -->
   sequent [squash] { 'H; x: 'v *['g] 'u = 'w *['g] 'u in 'g^car; 'J['x] >- 'v in 'g^car } -->
   sequent [squash] { 'H; x: 'v *['g] 'u = 'w *['g] 'u in 'g^car; 'J['x] >- 'w in 'g^car } -->
   sequent ['ext] { 'H; x: 'v *['g] 'u = 'w *['g] 'u in 'g^car; 'J['x] >- 'v = 'w in 'g^car }

doc <:doc< 
   @begin[doc]
  
   Unique identity (left and right).
   @end[doc]
>>
interactive unique_id_left group[i:l] :
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'e2 in 'g^car } -->
   [main] sequent ['ext] {'H >- all a: 'g^car. 'e2 *['g] 'a = 'a in 'g^car } -->
   sequent ['ext] {'H >- 'e2 = 'g^"1" in 'g^car }

interactive unique_id_right group[i:l] :
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'e2 in 'g^car } -->
   [main] sequent ['ext] {'H >- all a: 'g^car. 'a *['g] 'e2 = 'a in 'g^car } -->
   sequent ['ext] {'H >- 'e2 = 'g^"1" in 'g^car }

doc <:doc< 
   @begin[doc]
  
   Unique inverse (left and right).
   @end[doc]
>>
interactive unique_inv_left {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'a in 'g^car } -->
   [wf] sequent [squash] {'H >- 'a2 in 'g^car } -->
   [main] sequent ['ext] {'H >- 'a2 *['g] 'a = 'g^"1" in 'g^car } -->
   sequent ['ext] {'H >- 'a2 = 'g^inv 'a in 'g^car }

interactive unique_inv_right {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'a in 'g^car } -->
   [wf] sequent [squash] {'H >- 'a2 in 'g^car } -->
   [main] sequent ['ext] {'H >- 'a *['g] 'a2 = 'g^"1" in 'g^car } -->
   sequent ['ext] {'H >- 'a2 = 'g^inv 'a in 'g^car }

doc <:doc< 
   @begin[doc]
  
   Unique solution.
   @end[doc]
>>
(* The unique solution for a * x = b is x = a' * b *)
interactive unique_sol1 {| intro [AutoMustComplete; intro_typeinf <<'g>>] |} group[i:l] :
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'a in 'g^car } -->
   [wf] sequent [squash] {'H >- 'b in 'g^car } -->
   [wf] sequent [squash] {'H >- 'x in 'g^car } -->
   [main] sequent ['ext] {'H >- 'a *['g] 'x = 'b in 'g^car } -->
   sequent ['ext] {'H >- 'x = ('g^inv 'a) *['g] 'b in 'g^car }

(* The unique solution for y * a = b is y = b * a' *)
interactive unique_sol2 {| intro [AutoMustComplete; intro_typeinf <<'g>>] |} group[i:l] :
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'a in 'g^car } -->
   [wf] sequent [squash] {'H >- 'b in 'g^car } -->
   [wf] sequent [squash] {'H >- 'y in 'g^car } -->
   [main] sequent ['ext] {'H >- 'y *['g] 'a = 'b in 'g^car } -->
   sequent ['ext] {'H >- 'y = 'b *['g] ('g^inv 'a) in 'g^car }

doc <:doc< 
   @begin[doc]
  
   Inverse simplification.
   @end[doc]
>>
(* (a * b)' = b' * a'  *)
interactive inv_simplify {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent [squash] {'H >- 'b in 'g^car } -->
   sequent ['ext] {'H >- 'g^inv ('a *['g] 'b)  = ('g^inv 'b) *['g] ('g^inv 'a) in 'g^car }
doc <:doc< @docoff >>

(* Inverse of id *)
interactive inv_of_id {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent ['ext] {'H >- 'g^inv 'g^"1" = 'g^"1" in 'g^car }

(* e * a = a * e *)
interactive id_commut1 {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent ['ext] {'H >- 'g^"1" *['g] 'a = 'a *['g] 'g^"1" in 'g^car }

(* a * e = e * a *)
interactive id_commut2 {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent ['ext] {'H >- 'a *['g] 'g^"1" = 'g^"1" *['g] 'a in 'g^car }

(************************************************************************
 * ABELIAN GROUP                                                        *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @modsection{Abelian group}
   @modsubsection{Rewrites}
  
   @end[doc]
>>
define unfold_abelg : abelg[i:l] <-->
   {g: group[i:l] | isCommutative{'g}}
doc <:doc< @docoff >>

let fold_abelg = makeFoldC << abelg[i:l] >> unfold_abelg

let abelgDT n = rw unfold_abelg n thenT dT n

let resource elim +=
   [<<abelg[i:l]>>, abelgDT]

doc <:doc< 
   @begin[doc]
   @modsubsection{Well-formedness}
  
   @end[doc]
>>
interactive abelg_wf {| intro [] |} :
   sequent ['ext] { 'H >- "type"{abelg[i:l]} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction and Elimination}
  
   @end[doc]
>>
interactive abelg_intro {| intro [] |} :
   [wf] sequent [squash] { 'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- isCommutative{'g} } -->
   sequent ['ext] { 'H >- 'g in abelg[i:l] }

interactive abelg_elim {| elim [] |} 'H :
   sequent ['ext] { 'H; g: group[i:l]; x: isCommutative{'g}; 'J['g] >- 'C['g] } -->
   sequent ['ext] { 'H; g: abelg[i:l]; 'J['g] >- 'C['g] }

doc <:doc< 
   @begin[doc]
   @modsubsection{Hierarchy}
  
   @end[doc]
>>
interactive abelg_is_group :
   sequent [squash] { 'H >- 'g in abelg[i:l] } -->
   sequent ['ext] { 'H >- 'g in group[i:l] }

doc <:doc< 
   @begin[doc]
   @modsubsection{Rules}
  
   @end[doc]
>>

(************************************************************************
 * SUBGROUP                                                             *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @modsection{Subgroup}
   @modsubsection{Rewrites}
  
   @end[doc]
>>
define unfold_subgroup1 : subgroup[i:l]{'S; 'G} <-->
   ((('S in group[i:l]) & ('G in group[i:l])) & subStructure{'S; 'G})
doc <:doc< @docoff >>

let unfold_subgroup = unfold_subgroup1 thenC addrC [1] unfold_subStructure

let fold_subgroup1 = makeFoldC << subgroup[i:l]{'S; 'G} >> unfold_subgroup1
let fold_subgroup = makeFoldC << subgroup[i:l]{'S; 'G} >> unfold_subgroup

let subgroupDT n = rw unfold_subgroup n thenT dT n

let resource elim +=
   [<<subgroup[i:l]{'S; 'G}>>, subgroupDT]

doc <:doc< 
   @begin[doc]
   @modsubsection{Well-formedness}
  
   @end[doc]
>>
(*interactive subgroup_wf {| intro [] |} :
   [wf] sequent [squash] { 'H >- 'S in group[i:l] } -->
   [wf] sequent [squash] { 'H >- 'G in group[i:l] } -->
   sequent ['ext] { 'H >- "type"{subgroup[i:l]{'S; 'G}} }
*)

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction and Elimination}
  
   @end[doc]
>>
interactive subgroup_intro {| intro [] |} :
   [wf] sequent [squash] { 'H >- 'S in group[i:l] } -->
   [wf] sequent [squash] { 'H >- 'G in group[i:l] } -->
   [main] sequent ['ext] { 'H >- subStructure{'S; 'G} } -->
   sequent ['ext] { 'H >- subgroup[i:l]{'S; 'G} }

interactive subgroup_elim {| elim [] |} 'H 'S 'G :
(*   [wf] sequent [squash] { 'H; x: subgroup[i:l]{'S; 'G}; 'J['x] >- 'S in group[i:l] } -->
   [wf] sequent [squash] { 'H; x: subgroup[i:l]{'S; 'G}; 'J['x] >- 'G in group[i:l] } -->
   [main] sequent ['ext] { 'H; x: subgroup[i:l]{'S; 'G}; y: 'S^car subtype 'G^car; z: all a: 'S^car. all b: 'S^car. (('a = 'b in 'G^car) => ('a = 'b in 'G^car)); u: {b: 'G^car | exst a: 'S^car. 'b = 'a in 'G^car} subtype 'S^car; v: 'S^"*" = 'G^"*" in 'S^car -> 'S^car -> 'S^car; 'J['x] >- 'C['x] } -->
*)
(*   [main] sequent ['ext] { 'H; S: group[i:l]; G: group[i:l]; x: subStructure{'S; 'G}; y: 'S^car subtype 'G^car; z: all a: 'S^car. all b: 'S^car. (('a = 'b in 'G^car) => ('a = 'b in 'G^car)); u: {b: 'G^car | exst a: 'S^car. 'b = 'a in 'G^car} subtype 'S^car; v: 'S^"*" = 'G^"*" in 'S^car -> 'S^car -> 'S^car; 'J['x] >- 'C['x] } -->*)
   [main] sequent ['ext] { 'H; S: group[i:l]; G: group[i:l]; y: 'S^car subtype 'G^car; z: all a: 'S^car. all b: 'S^car. (('a = 'b in 'G^car) => ('a = 'b in 'G^car)); u: {b: 'G^car | exst a: 'S^car. 'b = 'a in 'G^car} subtype 'S^car; v: 'S^"*" = 'G^"*" in 'S^car -> 'S^car -> 'S^car; 'J['S, 'G] >- 'C['S, 'G] } -->
   sequent ['ext] { 'H; x: subgroup[i:l]{'S; 'G}; 'J['x] >- 'C['x] }

doc <:doc< 
   @begin[doc]
   @modsubsection{Rules}
  
   Subgroup is squash-stable.
   @end[doc]
>>
interactive subgroup_squashStable {| squash |} :
   [wf] sequent [squash] { 'H >- squash{subgroup[i:l]{'S; 'G}} } -->
   sequent ['ext] { 'H >- subgroup[i:l]{'S; 'G} }
doc <:doc< @docoff >>

interactive subgroup_ref {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent ['ext] {'H >- subgroup[i:l]{'g; 'g} }

doc <:doc< 
   @begin[doc]
  
     If $s$ is a subgroup of $g$, then
     @begin[enumerate]
     @item{$s$ is closed under the binary operation of $g$.}
     @item{the identity of $s$ is the identity of $g$.}
     @item{the inverse of $a @in @car{s}$ is also the inverse of $a$ in $g$.}
     @end[enumerate]
   @end[doc]
>>
interactive subgroup_op {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   [wf] sequent [squash] {'H >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   [wf] sequent [squash] {'H >- 'a in 's^car } -->
   [wf] sequent [squash] {'H >- 'b in 's^car } -->
   sequent ['ext] { 'H >- 'a *['g] 'b = 'a *['s] 'b in 's^car }

interactive subgroup_op1 {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   [wf] sequent [squash] {'H >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   [wf] sequent [squash] {'H >- 'a in 's^car } -->
   [wf] sequent [squash] {'H >- 'b in 's^car } -->
   sequent ['ext] { 'H >- 'a *['g] 'b in 's^car }

(* interactive subgroup_op1 {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   [main] sequent ['ext] { 'H >- subgroup[i:l]{'s; 'g} } -->
   [wf] sequent [squash] {'H >- 'a in 's^car } -->
   [wf] sequent [squash] {'H >- 'b in 's^car } -->
   sequent ['ext] { 'H >- 'a *['g] 'b in 's^car }
*)

interactive subgroup_id {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   [wf] sequent [squash] {'H >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   sequent ['ext] {'H >- 'g^"1" = 's^"1" in 's^car }

interactive subgroup_inv {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   [wf] sequent [squash] {'H >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   [wf] sequent [squash] {'H >- 'a in 's^car } -->
   sequent ['ext] {'H >- 'g^inv 'a = 's^inv 'a in 's^car }

doc <:doc< 
   @begin[doc]
  
     A non-empty subset $S$ is a subgroup of $G$ only if
     for all $a, b @in H$, $@mul{g; a; @inv{g; b}} @in @car{h}$
   @end[doc]
>>
interactive subgroup_thm1 group[i:l] :
   [wf] sequent [squash] {'H >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   sequent ['ext] { 'H >- all a: 's^car. all b: 's^car. ('a *['g] ('g^inv 'b) in 's^car) }

doc <:doc< 
   @begin[doc]
  
     The intersection group of subgroups $s_1$ and $s_2$ of
     a group $g$ is again a subgroup of $g$.
   @end[doc]
>>
interactive subgroup_isect group[i:l] :
   sequent [squash] {'H >- 's1 in group[i:l] } -->
   sequent [squash] {'H >- 's2 in group[i:l] } -->
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent ['ext] { 'H >- subStructure{'s1; 'g} } -->
   sequent ['ext] { 'H >- subStructure{'s2; 'g} } -->
   sequent ['ext] { 'H >- (            {car=bisect{.'s1^car;.'s2^car}; "*"='g^"*"; "1"='g^"1"; inv='g^inv} in group[i:l]) &
                          subStructure{{car=bisect{.'s1^car;.'s2^car}; "*"='g^"*"; "1"='g^"1"; inv='g^inv}; 'g} }

(************************************************************************
 * COSET                                                                *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @modsection{Coset}
   @modsubsection{Rewrites}
  
   @end[doc]
>>
define unfold_lcoset : lcoset{'s; 'g; 'b} <-->
   {x: 'g^car | exst a: 's^car. 'x = 'b *['g] 'a in 'g^car}

define unfold_rcoset : rcoset{'s; 'g; 'b} <-->
   {x: 'g^car | exst a: 's^car. 'x = 'a *['g] 'b in 'g^car}
doc <:doc< @docoff >>

let fold_lcoset = makeFoldC << lcoset{'s; 'g; 'b} >> unfold_lcoset
let fold_rcoset = makeFoldC << rcoset{'s; 'g; 'b} >> unfold_rcoset

doc <:doc< 
   @begin[doc]
   @modsubsection{Well-formedness}
  
   @end[doc]
>>
interactive lcoset_wf {| intro [] |} :
   [wf] sequent [squash] { 'H >- "type"{.'g^car} } -->
   [wf] sequent [squash] { 'H >- "type"{.'s^car} } -->
   [wf] sequent [squash] { 'H; a: 's^car >- 'b *['g] 'a in 'g^car } -->
   sequent ['ext] { 'H >- "type"{lcoset{'s; 'g; 'b}} }

interactive rcoset_wf {| intro [] |} :
   [wf] sequent [squash] { 'H >- "type"{.'g^car} } -->
   [wf] sequent [squash] { 'H >- "type"{.'s^car} } -->
   [wf] sequent [squash] { 'H; a: 's^car >- 'a *['g] 'b in 'g^car } -->
   sequent ['ext] { 'H >- "type"{rcoset{'s; 'g; 'b}} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction and Elimination}
  
   @end[doc]
>>
interactive lcoset_intro {| intro [intro_typeinf <<'g>>] |} group[i:l] 'x :
   [wf] sequent [squash] {'H >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   [wf] sequent [squash] {'H >- 'b in 'g^car } -->
   [wf] sequent [squash] {'H >- 'x in 'g^car } -->
   [main] sequent [squash] {'H >- exst a: 's^car. 'x = 'b *['g] 'a in 'g^car } -->
   sequent ['ext] { 'H >- lcoset{'s; 'g; 'b} }

interactive rcoset_intro {| intro [intro_typeinf <<'g>>] |} group[i:l] 'x :
   [wf] sequent [squash] {'H >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   [wf] sequent [squash] {'H >- 'b in 'g^car } -->
   [wf] sequent [squash] {'H >- 'x in 'g^car } -->
   [main] sequent [squash] {'H >- exst a: 's^car. 'x = 'a *['g] 'b in 'g^car } -->
   sequent ['ext] { 'H >- rcoset{'s; 'g; 'b} }

interactive lcoset_member_intro {| intro [intro_typeinf <<'g>>] |} group[i:l] 'a :
   [wf] sequent [squash] {'H >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [wf] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   [wf] sequent [squash] {'H >- 'b in 'g^car } -->
   [wf] sequent [squash] {'H >- 'x1 = 'x2 in 'g^car } -->
   [wf] sequent [squash] {'H >- 'a in 's^car } -->
   [main] sequent [squash] {'H >- 'x1 = 'b *['g] 'a in 'g^car } -->
   sequent ['ext] { 'H >- 'x1 = 'x2 in lcoset{'s; 'g; 'b} }

interactive rcoset_member_intro {| intro [intro_typeinf <<'g>>] |} group[i:l] 'a :
   [wf] sequent [squash] {'H >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [wf] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   [wf] sequent [squash] {'H >- 'b in 'g^car } -->
   [wf] sequent [squash] {'H >- 'x1 = 'x2 in 'g^car } -->
   [wf] sequent [squash] {'H >- 'a in 's^car } -->
   [main] sequent ['ext] {'H >- 'x1 = 'a *['g] 'b in 'g^car } -->
   sequent ['ext] { 'H >- 'x1 = 'x2 in rcoset{'s; 'g; 'b} }

interactive lcoset_elim {| elim [elim_typeinf <<'g>>] |} 'H group[i:l] :
   [wf] sequent [squash] {'H; u: lcoset{'s; 'g; 'b}; 'J['u] >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H; u: lcoset{'s; 'g; 'b}; 'J['u] >- 'g in group[i:l] } -->
   [wf] sequent ['ext] { 'H; u: lcoset{'s; 'g; 'b}; 'J['u] >- subStructure{'s; 'g} } -->
   [wf] sequent [squash] {'H; u: lcoset{'s; 'g; 'b}; 'J['u] >- 'b in 'g^car } -->
   [main] sequent ['ext] {'H; u: 'g^car; v: squash{.exst a: 's^car. 'u = 'b *['g] 'a in 'g^car}; 'J['u] >- 'C['u] } -->
   sequent ['ext] { 'H; u: lcoset{'s; 'g; 'b}; 'J['u] >- 'C['u] }

interactive rcoset_elim {| elim [elim_typeinf <<'g>>] |} 'H group[i:l] :
   [wf] sequent [squash] {'H; u: rcoset{'s; 'g; 'b}; 'J['u] >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H; u: rcoset{'s; 'g; 'b}; 'J['u] >- 'g in group[i:l] } -->
   [wf] sequent [squash] { 'H; u: rcoset{'s; 'g; 'b}; 'J['u] >- subStructure{'s; 'g} } -->
   [wf] sequent [squash] {'H; u: rcoset{'s; 'g; 'b}; 'J['u] >- 'b in 'g^car } -->
   [main] sequent ['ext] {'H; u: 'g^car; v: squash{.exst a: 's^car. 'u = 'a *['g] 'b in 'g^car}; 'J['u] >- 'C['u] } -->
   sequent ['ext] { 'H; u: rcoset{'s; 'g; 'b}; 'J['u] >- 'C['u] }

doc <:doc< 
   @begin[doc]
   @modsubsection{Rules}
  
     If $s$ is a subgroup of group $g$, both the left and right
     cosets of $s$ containing $b$ are subsets of the carrier of
     $g$.
   @end[doc]
>>
interactive lcoset_subset {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   [wf] sequent [squash] {'H >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   [wf] sequent [squash] {'H >- 'b in 'g^car } -->
   sequent ['ext] { 'H >- \subset{lcoset{'s; 'g; 'b}; .'g^car} }

interactive rcoset_subset {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   [wf] sequent [squash] {'H >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   [wf] sequent [squash] {'H >- 'b in 'g^car } -->
   sequent ['ext] { 'H >- \subset{rcoset{'s; 'g; 'b}; .'g^car} }

(************************************************************************
 * NORMAL SUBGROUP                                                      *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @modsection{Normal subgroup}
   @modsubsection{Rewrites}
  
   @end[doc]
>>
define unfold_normalSubg : normalSubg[i:l]{'s; 'g} <-->
   subStructure{'s; 'g} & all x: 'g^car. lcoset{'s; 'g; 'x} = rcoset{'s; 'g; 'x} in univ[i:l]
doc <:doc< @docoff >>

let fold_normalSubg = makeFoldC << normalSubg[i:l]{'s; 'g} >> unfold_normalSubg

doc <:doc< 
   @begin[doc]
   @modsubsection{Well-formedness}
  
   @end[doc]
>>
(*
interactive normalSubg_wf {| intro [] |} :
   [wf] sequent [squash] {'H >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   sequent ['ext] { 'H >- "type"{normalSubg[i:l]{'s; 'g}} }
*)

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction and Elimination}
  
   @end[doc]
>>
interactive normalSubg_intro {| intro [] |} :
   [wf] sequent [squash] {'H >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   [main] sequent ['ext] { 'H; x: 'g^car >- lcoset{'s; 'g; 'x} = rcoset{'s; 'g; 'x} in univ[i:l] } -->
   sequent ['ext] { 'H >- normalSubg[i:l]{'s; 'g} }

interactive normalSubg_elim {| elim [] |} 'H 'b :
   [wf] sequent [squash] {'H; x: normalSubg[i:l]{'s; 'g}; 'J['x] >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H; x: normalSubg[i:l]{'s; 'g}; 'J['x] >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H; x: normalSubg[i:l]{'s; 'g}; 'J['x] >- subStructure{'s; 'g} } -->
   [wf] sequent [squash] {'H; x: normalSubg[i:l]{'s; 'g}; 'J['x] >- 'b in 'g^car } -->
   [main] sequent ['ext] { 'H; x: normalSubg[i:l]{'s; 'g}; 'J['x]; y: lcoset{'s; 'g; 'b} = rcoset{'s; 'g; 'b} in univ[i:l] >- 'C['x] } -->
   sequent ['ext] { 'H; x: normalSubg[i:l]{'s; 'g}; 'J['x] >- 'C['x] }

doc <:doc< 
   @begin[doc]
   @modsubsection{Rules}
  
   All subgroups of abelian groups are normal.
   @end[doc]
>>
interactive abel_subg_normal :
   [wf] sequent [squash] {'H >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- isCommutative{'g} } -->
   [main] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   sequent ['ext] { 'H >- normalSubg[i:l]{'s; 'g} }

(************************************************************************
 * GROUP HOMOMORPHISM                                                   *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @modsection{Group homomorphism}
   @modsubsection{Rewrites}
  
   @end[doc]
>>
define unfold_groupHom : groupHom{'A; 'B} <-->
   { f: 'A^car -> 'B^car | all x: 'A^car. all y: 'A^car. ('f ('x *['A] 'y)) = ('f 'x) *['B] ('f 'y) in 'B^car }
doc <:doc< @docoff >>

let fold_groupHom = makeFoldC <<groupHom{'A; 'B}  >> unfold_groupHom

doc <:doc< 
   @begin[doc]
   @modsubsection{Well-formedness}
  
   @end[doc]
>>
interactive groupHom_type {| intro [intro_typeinf <<'A>>] |} group[i:l] :
   [wf] sequent [squash] {'H >- 'A in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'B in group[i:l] } -->
    sequent ['ext] { 'H >- "type"{groupHom{'A; 'B}} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction and Elimination}
  
   @end[doc]
>>
interactive groupHom_intro {| intro [intro_typeinf <<'A>>] |} group[i:l] :
   [wf] sequent [squash] {'H >- 'A in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'B in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'f in 'A^car -> 'B^car } -->
   [main] sequent ['ext] { 'H; x: 'A^car; y: 'A^car >- ('f ('x *['A] 'y)) = ('f 'x) *['B] ('f 'y) in 'B^car } -->
    sequent ['ext] { 'H >- 'f in groupHom{'A; 'B} }

interactive groupHom_elim {| elim [elim_typeinf <<'B>>] |} 'H group[i:l] :
   [wf] sequent [squash] {'H; f: groupHom{'A; 'B}; 'J['f] >- 'A in group[i:l] } -->
   [wf] sequent [squash] {'H; f: groupHom{'A; 'B}; 'J['f] >- 'B in group[i:l] } -->
   [main] sequent ['ext] { 'H; f: 'A^car -> 'B^car; u: all x: 'A^car. all y: 'A^car. ('f ('x *['A] 'y)) = ('f 'x) *['B] ('f 'y) in 'B^car; 'J['f] >- 'C['f] } -->
   sequent ['ext] { 'H; f: groupHom{'A; 'B}; 'J['f] >- 'C['f] }

doc <:doc< 
   @begin[doc]
   @modsubsection{Rules}
  
     For any groups $G_1$ and $G_2$, there is always at least
     one homomorphism $f@colon G_1 @rightarrow G_2$ which
     maps all elements of $@car{G_1}$ into $@id{G_2}$. This
     is called the Trivial Homomorphism.
   @end[doc]
>>
interactive trivial_hom {| intro [AutoMustComplete; intro_typeinf <<'A>>] |} group[i:l] :
   [wf] sequent [squash] {'H >- 'A in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'B in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'f in 'A^car -> 'B^car } -->
   [main] sequent ['ext] { 'H; x: 'A^car >- 'f 'x = 'B^"1" in 'B^car } -->
   sequent ['ext] { 'H >- 'f in groupHom{'A; 'B} }

doc <:doc< 
   @begin[doc]
   Let $f@colon g_1 @rightarrow g_2$ be a group
   homomorphism of $g_1$ into $g_2$.
  
   $@space @space$
  
     $f$ maps the identity of $G_1$ into the identity of $G_2$.
   @end[doc]
>>
interactive groupHom_id {| intro [AutoMustComplete; intro_typeinf <<'A>>] |} group[i:l] :
   [wf] sequent [squash] {'H >- 'A in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'B in group[i:l] } -->
   [main] sequent ['ext] { 'H >- 'f in groupHom{'A; 'B} } -->
   sequent ['ext] { 'H >- 'f 'A^"1" = 'B^"1" in 'B^car }

interactive hom_id {| intro [AutoMustComplete; intro_typeinf <<'A>>] |} group[i:l] :
   [wf] sequent [squash] {'H >- 'A in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'B in group[i:l] } -->
   [main] sequent ['ext] { 'H >- 'f in groupHom{'A; 'B} } -->
   sequent ['ext] { 'H >- 'f 'A^"1" = 'B^"1" in 'B^car }

doc <:doc< 
   @begin[doc]
  
     $f$ maps the inverse of an element $a$ in $@car{G_1}$ into
     the inverse of $f[a]$ in $@car{G_2}$.
   @end[doc]
>>
interactive groupHom_inv {| intro [AutoMustComplete; intro_typeinf <<'A>>] |} group[i:l] :
   [wf] sequent [squash] {'H >- 'A in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'B in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'a in 'A^car } -->
   [wf] sequent [squash] { 'H >- 'f in groupHom{'A; 'B} } -->
   sequent ['ext] { 'H >- 'f ('A^inv 'a) = 'B^inv ('f 'a) in 'B^car }

doc <:doc< 
   @begin[doc]
  
   If $f$ is @emph{onto}, then $G_1$ is abelian
   implies $G_2$ is abelian.
   @end[doc]
>>
interactive groupHom_abel 'A 'f :
   [wf] sequent [squash] { 'H >- 'A in abelg[i:l] } -->
   [wf] sequent [squash] {'H >- 'B in group[i:l] } -->
   [wf] sequent [squash] { 'H >- 'f in groupHom{'A; 'B} } -->
   [main] sequent ['ext] { 'H; x: 'B^car >- exst y: 'A^car. 'x = 'f 'y in 'B^car } -->
   sequent ['ext] { 'H >- 'B in abelg[i:l] }

doc <:doc< 
   @begin[doc]
  
     If $S$ is a subgroup of $G_1$, then the image of $S$ under
     $f$ is a subgroup of $G_2$.
   @end[doc]
>>
interactive groupHom_subg1 group[i:l] 'f 'A 'S :
   [wf] sequent [squash] {'H >- 'A in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'B in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'S in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'T in group[i:l] } -->
   [wf] sequent [squash] { 'H >- 'f in groupHom{'A; 'B} } -->
   [main] sequent ['ext] { 'H >- subStructure{'S; 'A} } -->
   [main] sequent ['ext] { 'H >- 'T^car = {x: 'B^car | exst y: 'S^car. 'x = 'f 'y in 'B^car} in univ[i:l] } -->
   [main] sequent ['ext] { 'H >- 'T^"*" = 'B^"*" in 'T^car -> 'T^car -> 'T^car } -->
   sequent ['ext] { 'H >- subStructure{'T; 'B} }

doc <:doc< 
   @begin[doc]
  
     If $T$ is a subgroup of $G_2$, then the inverse image of
     $T$ under $f$ is a subgroup of $G_1$.
   @end[doc]
>>
interactive groupHom_subg2 group[i:l] 'f 'B 'T :
   [wf] sequent [squash] {'H >- 'A in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'B in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'S in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'T in group[i:l] } -->
   [wf] sequent [squash] { 'H >- 'f in groupHom{'A; 'B} } -->
   [main] sequent ['ext] { 'H >- subStructure{'T; 'B} } -->
   [main] sequent ['ext] { 'H >- 'S^car = {x: 'A^car | 'f 'x in 'T^car} in univ[i:l] } -->
   [main] sequent ['ext] { 'H >- 'S^"*" = 'A^"*" in 'S^car -> 'S^car -> 'S^car } -->
   sequent ['ext] { 'H >- subStructure{'S; 'A} }

doc <:doc< @docoff >>

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_inv
prec prec_mul < prec_inv

dform group_df : except_mode[src] :: group[i:l] =
   math_group{slot[i:l]}

dform pregroup_df : except_mode[src] :: pregroup[i:l] =
   math_pregroup{slot[i:l]}

dform isGroup_df : except_mode[src] :: isGroup{'g} =
   `"isGroup(" slot{'g} `")"

dform inv_df1 : except_mode[src] :: parens :: "prec"[prec_inv] :: ('g^inv 'a) =
   math_inv{'g; 'a}

dform abelg_df : except_mode[src] :: abelg[i:l] =
   math_abelg{slot[i:l]}

dform lcoset_df : except_mode[src] :: lcoset{'h; 'g; 'a} =
   math_lcoset{'h; 'g; 'a}

dform rcoset_df : except_mode[src] :: rcoset{'h; 'g; 'a} =
   math_rcoset{'h; 'g; 'a}

dform normalSubg_df : except_mode[src] :: normalSubg[i:l]{'s; 'g} =
   math_normalSubg{slot[i:l]; 's; 'g}

dform groupHom_df : except_mode[src] :: groupHom{'A; 'B} =
   math_groupHom{'A; 'B}

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
