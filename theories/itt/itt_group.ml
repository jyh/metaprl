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
open Itt_equal

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

define unfold_isGroup1 : isGroup{'G} <-->
   isSemigroup{'G} & all x: 'G^car. 'G^"1" *['G] 'x = 'x in 'G^car & all x: 'G^car. ('G^inv 'x) *['G] 'x = 'G^"1" in 'G^car

define unfold_group1 : group[i:l] <-->
   {G: pregroup[i:l] | isGroup{'G}}
doc <:doc< @docoff >>

let unfold_pregroup = unfold_pregroup1 thenC addrC [1] unfold_premonoid
let unfold_isGroup = unfold_isGroup1 thenC addrC [0] unfold_isSemigroup
let unfold_group = unfold_group1 thenC addrC [0] unfold_pregroup thenC addrC [1] unfold_isGroup

let fold_pregroup1 = makeFoldC << pregroup[i:l] >> unfold_pregroup1
let fold_pregroup = makeFoldC << pregroup[i:l] >> unfold_pregroup
let fold_isGroup1 = makeFoldC << isGroup{'G} >> unfold_isGroup1
let fold_isGroup = makeFoldC << isGroup{'G} >> unfold_isGroup
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
   sequent ['ext] { <H> >- "type"{pregroup[i:l]} }

interactive isGroup_wf {| intro [] |} :
   sequent [squash] { <H> >- "type"{'G^car} } -->
   sequent [squash] { <H>; x: 'G^car; y: 'G^car >- 'x *['G] 'y in 'G^car} -->
   sequent [squash] { <H> >- 'G^"1" in 'G^car} -->
   sequent [squash] { <H>; x: 'G^car >- 'G^inv 'x in 'G^car} -->
   sequent ['ext] { <H> >- "type"{isGroup{'G}} }

interactive group_wf {| intro [] |} :
   sequent ['ext] { <H> >- "type"{group[i:l]} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction and Elimination}
  
   @end[doc]
>>
interactive pregroup_intro {| intro [AutoMustComplete] |} :
   sequent [squash] { <H> >- 'G in {car: univ[i:l]; "*": ^car -> ^car -> ^car; "1": ^car; inv: ^car -> ^car} } -->
   sequent ['ext] { <H> >- 'G in pregroup[i:l] }

interactive pregroup_elim {| elim [] |} 'H :
   sequent ['ext] { <H>; G: {car: univ[i:l]; "*": ^car -> ^car -> ^car; "1": ^car; inv: ^car -> ^car}; <J['G]> >- 'C['G] } -->
   sequent ['ext] { <H>; G: pregroup[i:l]; <J['G]> >- 'C['G] }

interactive isGroup_intro {| intro [AutoMustComplete] |} :
   [wf] sequent [squash] { <H> >- "type"{.'G^car} } -->
   [main] sequent ['ext] { <H> >- isSemigroup{'G} } -->
   [main] sequent ['ext] { <H>; x: 'G^car >- 'G^"1" *['G] 'x = 'x in 'G^car } -->
   [main] sequent ['ext] { <H>; x: 'G^car >- ('G^inv 'x) *['G] 'x = 'G^"1" in 'G^car } -->
   sequent ['ext] { <H> >- isGroup{'G} }

interactive isGroup_elim {| elim [] |} 'H :
   sequent ['ext] { <H>; u: isGroup{'G}; v: all x: 'G^car. all y: 'G^car. all z: 'G^car. (('x *['G] 'y) *['G] 'z = 'x *['G] ('y *['G] 'z) in 'G^car); w: all x: 'G^car. ('G^"1" *['G] 'x = 'x in 'G^car); x: all x: 'G^car. ('G^inv 'x) *['G] 'x = 'G^"1" in 'G^car; <J['u]> >- 'C['u] } -->
   sequent ['ext] { <H>; u: isGroup{'G}; <J['u]> >- 'C['u] }

interactive group_intro {| intro [AutoMustComplete] |} :
   [wf] sequent [squash] { <H> >- 'G in pregroup[i:l] } -->
   [main] sequent ['ext] { <H> >- isGroup{'G} } -->
   sequent ['ext] { <H> >- 'G in group[i:l] }

interactive group_elim {| elim [] |} 'H :
   sequent ['ext] { <H>; G: {car: univ[i:l]; "*": ^car -> ^car -> ^car; "1": ^car; inv: ^car -> ^car}; u: squash{.all x: 'G^car. all y: 'G^car. all z: 'G^car. (('x *['G] 'y) *['G] 'z = 'x *['G] ('y *['G] 'z) in 'G^car)}; v: squash{.all x: 'G^car. 'G^"1" *['G] 'x = 'x in 'G^car}; w: squash{.all x: 'G^car. ('G^inv 'x) *['G] 'x = 'G^"1" in 'G^car}; <J['G]> >- 'C['G] } -->
   sequent ['ext] { <H>; G: group[i:l]; <J['G]> >- 'C['G] }

interactive car_wf {| intro [AutoMustComplete; intro_typeinf <<'G>>] |} group[i:l] :
   sequent [squash] { <H> >- 'G in group[i:l] } -->
   sequent ['ext] { <H> >- "type"{('G^car)} }

interactive car_wf2 {| intro [AutoMustComplete] |} :
   sequent [squash] { <H> >- 'G in group[i:l] } -->
   sequent ['ext] { <H> >- 'G^car in univ[i:l] }

interactive op_wf {| intro [AutoMustComplete; intro_typeinf <<'G>>] |} group[i:l] :
   sequent [squash] { <H> >- 'G in group[i:l] } -->
   sequent ['ext] { <H> >- 'G^"*" in 'G^car -> 'G^car -> 'G^car }

interactive inv_wf {| intro [AutoMustComplete; intro_typeinf <<'G>>] |} group[i:l] :
   sequent [squash] { <H> >- 'G in group[i:l] } -->
   sequent ['ext] { <H> >- 'G^inv in 'G^car -> 'G^car }

interactive op_in_G {| intro [AutoMustComplete; intro_typeinf <<'G>>] |} group[i:l] :
   sequent [squash] { <H> >- 'G in group[i:l] } -->
   sequent [squash] { <H> >- 'a in 'G^car } -->
   sequent [squash] { <H> >- 'b in 'G^car } -->
   sequent ['ext] { <H> >- 'a *['G] 'b in 'G^car }

interactive id_in_G {| intro [AutoMustComplete; intro_typeinf <<'G>>] |} group[i:l] :
   sequent [squash] { <H> >- 'G in group[i:l] } -->
   sequent ['ext] { <H> >- 'G^"1" in 'G^car }

interactive inv_in_G {| intro [AutoMustComplete; intro_typeinf <<'G>>] |} group[i:l] :
   sequent [squash] { <H> >- 'G in group[i:l] } -->
   sequent [squash] { <H> >- 'a in 'G^car } -->
   sequent ['ext] { <H> >- 'G^inv 'a in 'G^car }

interactive group_assoc {| intro [AutoMustComplete; intro_typeinf <<'G>>] |} group[i:l] :
   sequent [squash] { <H> >- 'G in group[i:l] } -->
   sequent [squash] { <H> >- 'a in 'G^car } -->
   sequent [squash] { <H> >- 'b in 'G^car } -->
   sequent [squash] { <H> >- 'c in 'G^car } -->
   sequent ['ext] { <H> >- ('a *['G] 'b) *['G] 'c = 'a *['G] ('b *['G] 'c) in 'G^car }

interactive group_left_id {| intro [AutoMustComplete; intro_typeinf <<'G>>] |} group[i:l] :
   sequent [squash] { <H> >- 'G in group[i:l] } -->
   sequent [squash] { <H> >- 'a in 'G^car } -->
   sequent ['ext] { <H> >- 'G^"1" *['G] 'a = 'a in 'G^car }

interactive group_left_inv {| intro [AutoMustComplete; intro_typeinf <<'G>>] |} group[i:l] :
   sequent [squash] { <H> >- 'G in group[i:l] } -->
   sequent [squash] { <H> >- 'a in 'G^car } -->
   sequent ['ext] { <H> >- ('G^inv 'a) *['G] 'a = 'G^"1" in 'G^car }

interactive op_eq1 {| intro [AutoMustComplete; intro_typeinf <<'G>>] |} group[i:l] :
   sequent [squash] { <H> >- 'G in group[i:l] } -->
   sequent [squash] { <H> >- 'a = 'b in 'G^car } -->
   sequent [squash] { <H> >- 'c in 'G^car } -->
   sequent ['ext] { <H> >- 'a *['G] 'c = 'b *['G] 'c in 'G^car }

interactive op_eq2 {| intro [AutoMustComplete; intro_typeinf <<'G>>] |} group[i:l] :
   sequent [squash] { <H> >- 'G in group[i:l] } -->
   sequent [squash] { <H> >- 'a = 'b in 'G^car } -->
   sequent [squash] { <H> >- 'c in 'G^car } -->
   sequent ['ext] { <H> >- 'c *['G] 'a = 'c *['G] 'b in 'G^car }

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
interactive id_judge {| elim [elim_typeinf <<'G>>] |} 'H group[i:l] :
   sequent [squash] { <H>; x: 'u *['G] 'u = 'u in 'G^car; <J['x]> >- 'G in group[i:l] } -->
   sequent ['ext] { <H>; x: 'u *['G] 'u = 'u in 'G^car; <J['x]>; y: 'u = 'G^"1" in 'G^car >- 'C['x] } -->
   sequent ['ext] { <H>; x: 'u *['G] 'u = 'u in 'G^car; <J['x]> >- 'C['x] }

interactive right_inv {| intro [intro_typeinf <<'G>>] |} group[i:l] :
   sequent [squash] { <H> >- 'G in group[i:l] } -->
   sequent [squash] { <H> >- 'a in 'G^car } -->
   sequent ['ext] { <H> >- 'a *['G] ('G^inv 'a) = 'G^"1" in 'G^car }

interactive right_id {| intro [intro_typeinf <<'G>>] |} group[i:l] :
   sequent [squash] { <H> >- 'G in group[i:l] } -->
   sequent [squash] { <H> >- 'a in 'G^car } -->
   sequent ['ext] { <H> >- 'a *['G] 'G^"1" = 'a in 'G^car }

doc <:doc< 
   @begin[doc]
   @modsubsection{Hierarchy}
  
   A group is also a monoid.
   @end[doc]
>>
interactive group_is_monoid :
   sequent [squash] { <H> >- 'G in group[i:l] } -->
   sequent ['ext] { <H> >- 'G in monoid[i:l] }

doc <:doc< 
   @begin[doc]
   @modsubsection{Theorems}
  
   The left and right cancellation laws.
   @end[doc]
>>
(* Cancellation: a * b = a * c => b = c *)
interactive cancel_left {| elim [elim_typeinf <<'G>>] |} 'H group[i:l] :
   sequent [squash] { <H>; x: 'u *['G] 'v = 'u *['G] 'w in 'G^car; <J['x]> >- 'G in group[i:l] } -->
   sequent [squash] { <H>; x: 'u *['G] 'v = 'u *['G] 'w in 'G^car; <J['x]> >- 'u in 'G^car } -->
   sequent [squash] { <H>; x: 'u *['G] 'v = 'u *['G] 'w in 'G^car; <J['x]> >- 'v in 'G^car } -->
   sequent [squash] { <H>; x: 'u *['G] 'v = 'u *['G] 'w in 'G^car; <J['x]> >- 'w in 'G^car } -->
   sequent ['ext] { <H>; x: 'u *['G] 'v = 'u *['G] 'w in 'G^car; <J['x]> >- 'v = 'w in 'G^car }

(* Cancellation: b * a = c * a => b = c *)
interactive cancel_right {| elim [elim_typeinf <<'G>>] |} 'H group[i:l] :
   sequent [squash] { <H>; x: 'v *['G] 'u = 'w *['G] 'u in 'G^car; <J['x]> >- 'G in group[i:l] } -->
   sequent [squash] { <H>; x: 'v *['G] 'u = 'w *['G] 'u in 'G^car; <J['x]> >- 'u in 'G^car } -->
   sequent [squash] { <H>; x: 'v *['G] 'u = 'w *['G] 'u in 'G^car; <J['x]> >- 'v in 'G^car } -->
   sequent [squash] { <H>; x: 'v *['G] 'u = 'w *['G] 'u in 'G^car; <J['x]> >- 'w in 'G^car } -->
   sequent ['ext] { <H>; x: 'v *['G] 'u = 'w *['G] 'u in 'G^car; <J['x]> >- 'v = 'w in 'G^car }

doc <:doc< 
   @begin[doc]
  
   Unique identity (left and right).
   @end[doc]
>>
interactive unique_id_left group[i:l] :
   [wf] sequent [squash] { <H> >- 'G in group[i:l] } -->
   [wf] sequent [squash] { <H> >- 'e2 in 'G^car } -->
   [main] sequent ['ext] { <H> >- all a: 'G^car. 'e2 *['G] 'a = 'a in 'G^car } -->
   sequent ['ext] { <H> >- 'e2 = 'G^"1" in 'G^car }

interactive unique_id_right group[i:l] :
   [wf] sequent [squash] { <H> >- 'G in group[i:l] } -->
   [wf] sequent [squash] { <H> >- 'e2 in 'G^car } -->
   [main] sequent ['ext] { <H> >- all a: 'G^car. 'a *['G] 'e2 = 'a in 'G^car } -->
   sequent ['ext] { <H> >- 'e2 = 'G^"1" in 'G^car }

doc <:doc< 
   @begin[doc]
  
   Unique inverse (left and right).
   @end[doc]
>>
interactive unique_inv_left {| intro [intro_typeinf <<'G>>] |} group[i:l] :
   [wf] sequent [squash] { <H> >- 'G in group[i:l] } -->
   [wf] sequent [squash] { <H> >- 'a in 'G^car } -->
   [wf] sequent [squash] { <H> >- 'a2 in 'G^car } -->
   [main] sequent ['ext] { <H> >- 'a2 *['G] 'a = 'G^"1" in 'G^car } -->
   sequent ['ext] { <H> >- 'a2 = 'G^inv 'a in 'G^car }

interactive unique_inv_right {| intro [intro_typeinf <<'G>>] |} group[i:l] :
   [wf] sequent [squash] { <H> >- 'G in group[i:l] } -->
   [wf] sequent [squash] { <H> >- 'a in 'G^car } -->
   [wf] sequent [squash] { <H> >- 'a2 in 'G^car } -->
   [main] sequent ['ext] { <H> >- 'a *['G] 'a2 = 'G^"1" in 'G^car } -->
   sequent ['ext] { <H> >- 'a2 = 'G^inv 'a in 'G^car }

doc <:doc< 
   @begin[doc]
  
   Unique solution.
   @end[doc]
>>
(* The unique solution for a * x = b is x = a' * b *)
interactive unique_sol1 {| intro [AutoMustComplete; intro_typeinf <<'G>>] |} group[i:l] :
   [wf] sequent [squash] { <H> >- 'G in group[i:l] } -->
   [wf] sequent [squash] { <H> >- 'a in 'G^car } -->
   [wf] sequent [squash] { <H> >- 'b in 'G^car } -->
   [wf] sequent [squash] { <H> >- 'x in 'G^car } -->
   [main] sequent ['ext] { <H> >- 'a *['G] 'x = 'b in 'G^car } -->
   sequent ['ext] { <H> >- 'x = ('G^inv 'a) *['G] 'b in 'G^car }

(* The unique solution for y * a = b is y = b * a' *)
interactive unique_sol2 {| intro [AutoMustComplete; intro_typeinf <<'G>>] |} group[i:l] :
   [wf] sequent [squash] { <H> >- 'G in group[i:l] } -->
   [wf] sequent [squash] { <H> >- 'a in 'G^car } -->
   [wf] sequent [squash] { <H> >- 'b in 'G^car } -->
   [wf] sequent [squash] { <H> >- 'y in 'G^car } -->
   [main] sequent ['ext] { <H> >- 'y *['G] 'a = 'b in 'G^car } -->
   sequent ['ext] { <H> >- 'y = 'b *['G] ('G^inv 'a) in 'G^car }

doc <:doc< 
   @begin[doc]
  
   Inverse simplification.
   @end[doc]
>>
(* (a * b)' = b' * a'  *)
interactive inv_simplify {| intro [intro_typeinf <<'G>>] |} group[i:l] :
   sequent [squash] { <H> >- 'G in group[i:l] } -->
   sequent [squash] { <H> >- 'a in 'G^car } -->
   sequent [squash] { <H> >- 'b in 'G^car } -->
   sequent ['ext] { <H> >- 'G^inv ('a *['G] 'b)  = ('G^inv 'b) *['G] ('G^inv 'a) in 'G^car }
doc <:doc< @docoff >>

(* Inverse of id *)
interactive inv_of_id {| intro [intro_typeinf <<'G>>] |} group[i:l] :
   sequent [squash] { <H> >- 'G in group[i:l] } -->
   sequent ['ext] { <H> >- 'G^inv 'G^"1" = 'G^"1" in 'G^car }

(* e * a = a * e *)
interactive id_commut1 {| intro [intro_typeinf <<'G>>] |} group[i:l] :
   sequent [squash] { <H> >- 'G in group[i:l] } -->
   sequent [squash] { <H> >- 'a in 'G^car } -->
   sequent ['ext] { <H> >- 'G^"1" *['G] 'a = 'a *['G] 'G^"1" in 'G^car }

(* a * e = e * a *)
interactive id_commut2 {| intro [intro_typeinf <<'G>>] |} group[i:l] :
   sequent [squash] { <H> >- 'G in group[i:l] } -->
   sequent [squash] { <H> >- 'a in 'G^car } -->
   sequent ['ext] { <H> >- 'a *['G] 'G^"1" = 'G^"1" *['G] 'a in 'G^car }

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
   {G: group[i:l] | isCommutative{'G}}
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
   sequent ['ext] { <H> >- "type"{abelg[i:l]} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction and Elimination}
  
   @end[doc]
>>
interactive abelg_intro {| intro [] |} :
   [wf] sequent [squash] { <H> >- 'G in group[i:l] } -->
   [main] sequent ['ext] { <H> >- isCommutative{'G} } -->
   sequent ['ext] { <H> >- 'G in abelg[i:l] }

interactive abelg_elim {| elim [] |} 'H :
   sequent ['ext] { <H>; G: group[i:l]; x: isCommutative{'G}; <J['G]> >- 'C['G] } -->
   sequent ['ext] { <H>; G: abelg[i:l]; <J['G]> >- 'C['G] }

doc <:doc< 
   @begin[doc]
   @modsubsection{Hierarchy}
  
   @end[doc]
>>
interactive abelg_is_group :
   sequent [squash] { <H> >- 'G in abelg[i:l] } -->
   sequent ['ext] { <H> >- 'G in group[i:l] }

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
define unfold_subgroup : subgroup[i:l]{'S; 'G} <-->
   ((('S in group[i:l]) & ('G in group[i:l])) & subStructure{'S; 'G})
doc <:doc< @docoff >>

let fold_subgroup = makeFoldC << subgroup[i:l]{'S; 'G} >> unfold_subgroup

let subgroupDT n = copyHypT n (n+1) thenT rw unfold_subgroup (n+1) thenT dT (n+1) thenT dT (n+1)

let resource elim +=
   [<<subgroup[i:l]{'S; 'G}>>, subgroupDT]

doc <:doc< 
   @begin[doc]
   @modsubsection{Well-formedness}
  
   @end[doc]
>>
interactive subgroup_wf {| intro [] |} :
   sequent [squash] { <H> >- 'S in group[i:l] } -->
   sequent [squash] { <H> >- 'G in group[i:l] } -->
   sequent [squash] { <H> >- 'G^"*" = 'S^"*" in 'S^car -> 'S^car -> 'S^car } -->
   sequent ['ext] { <H> >- "type"{subgroup[i:l]{'S; 'G}} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction and Elimination}
  
   @end[doc]
>>
interactive subgroup_intro {| intro [] |} :
   [wf] sequent [squash] { <H> >- 'S in group[i:l] } -->
   [wf] sequent [squash] { <H> >- 'G in group[i:l] } -->
   [main] sequent ['ext] { <H> >- subStructure{'S; 'G} } -->
   sequent ['ext] { <H> >- subgroup[i:l]{'S; 'G} }

(*
interactive subgroup_elim {| elim [] |} 'H 'S 'G :
   [main] sequent ['ext] { <H>; S: group[i:l]; G: group[i:l]; x: subStructure{'S; 'G}; <J['S, 'G]> >- 'C['S, 'G] } -->
   sequent ['ext] { <H>; x: subgroup[i:l]{'S; 'G}; <J['x]> >- 'C['x] }
*)

doc <:doc< 
   @begin[doc]
   @modsubsection{Rules}
  
   Subgroup is squash-stable.
   @end[doc]
>>
interactive subgroup_sqStable {| squash |} :
   [wf] sequent [squash] { <H> >- squash{subgroup[i:l]{'S; 'G}} } -->
   sequent ['ext] { <H> >- subgroup[i:l]{'S; 'G} }
doc <:doc< @docoff >>

interactive subgroup_ref {| intro [] |} :
   sequent [squash] { <H> >- 'G in group[i:l] } -->
   sequent ['ext] { <H> >- subgroup[i:l]{'G; 'G} }

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
interactive subgroup_op {| intro [intro_typeinf <<'G>>] |} group[i:l] :
   [main] sequent [squash] { <H> >- subgroup[i:l]{'S; 'G} } -->
   [wf] sequent [squash] { <H> >- 'a in 'S^car } -->
   [wf] sequent [squash] { <H> >- 'b in 'S^car } -->
   sequent ['ext] { <H> >- 'a *['G] 'b = 'a *['S] 'b in 'S^car }

interactive subgroup_op1 {| intro [intro_typeinf <<'G>>] |} group[i:l] :
   [main] sequent [squash] { <H> >- subgroup[i:l]{'S; 'G} } -->
   [wf] sequent [squash] { <H> >- 'a in 'S^car } -->
   [wf] sequent [squash] { <H> >- 'b in 'S^car } -->
   sequent ['ext] { <H> >- 'a *['G] 'b in 'S^car }

interactive subgroup_id {| intro [intro_typeinf <<'G>>] |} group[i:l] :
   [main] sequent [squash] { <H> >- subgroup[i:l]{'S; 'G} } -->
   sequent ['ext] { <H> >- 'G^"1" = 'S^"1" in 'S^car }

interactive subgroup_id1 {| intro [AutoMustComplete; intro_typeinf <<'G>>] |} group[i:l] :
   [main] sequent [squash] { <H> >- subgroup[i:l]{'S; 'G} } -->
   sequent ['ext] { <H> >- 'G^"1" in 'S^car }

interactive subgroup_inv {| intro [intro_typeinf <<'G>>] |} group[i:l] :
   [main] sequent [squash] { <H> >- subgroup[i:l]{'S; 'G} } -->
   [wf] sequent [squash] { <H> >- 'a in 'S^car } -->
   sequent ['ext] { <H> >- 'G^inv 'a = 'S^inv 'a in 'S^car }

interactive subgroup_inv1 {| intro [AutoMustComplete; intro_typeinf <<'G>>] |} group[i:l] :
   [main] sequent [squash] { <H> >- subgroup[i:l]{'S; 'G} } -->
   [wf] sequent [squash] { <H> >- 'a in 'S^car } -->
   sequent ['ext] { <H> >- 'G^inv 'a in 'S^car }

doc <:doc< 
   @begin[doc]
  
     A non-empty subset $S$ is a subgroup of $G$ only if
     for all $a, b @in S$, $@mul{G; a; @inv{G; b}} @in @car{S}$
   @end[doc]
>>
interactive subgroup_thm1 group[i:l] :
   [main] sequent [squash] { <H> >- subgroup[i:l]{'S; 'G} } -->
   sequent ['ext] { <H> >- all a: 'S^car. all b: 'S^car. ('a *['G] ('G^inv 'b) in 'S^car) }

doc <:doc< 
   @begin[doc]
  
     The intersection of subgroups $S_1$ and $S_2$ of
     a group $G$ is again a subgroup of $G$.
   @end[doc]
>>
interactive subgroup_isect :
   sequent [squash] { <H> >- subgroup[i:l]{'S1; 'G} } -->
   sequent [squash] { <H> >- subgroup[i:l]{'S2; 'G} } -->
   sequent ['ext] { <H> >- subgroup[i:l]{{car=bisect{.'S1^car;.'S2^car}; "*"='G^"*"; "1"='G^"1"; inv='G^inv}; 'G} }

(************************************************************************
 * COSET                                                                *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @modsection{Coset}
   @modsubsection{Rewrites}
  
   @end[doc]
>>
define unfold_lcoset : lcoset{'S; 'G; 'b} <-->
   {x: 'G^car | exst a: 'S^car. 'x = 'b *['G] 'a in 'G^car}

define unfold_rcoset : rcoset{'S; 'G; 'b} <-->
   {x: 'G^car | exst a: 'S^car. 'x = 'a *['G] 'b in 'G^car}
doc <:doc< @docoff >>

let fold_lcoset = makeFoldC << lcoset{'S; 'G; 'b} >> unfold_lcoset
let fold_rcoset = makeFoldC << rcoset{'S; 'G; 'b} >> unfold_rcoset

doc <:doc< 
   @begin[doc]
   @modsubsection{Well-formedness}
  
   @end[doc]
>>
interactive lcoset_wf {| intro [] |} :
   [wf] sequent [squash] { <H> >- "type"{.'G^car} } -->
   [wf] sequent [squash] { <H> >- "type"{.'S^car} } -->
   [wf] sequent [squash] { <H>; a: 'S^car >- 'b *['G] 'a in 'G^car } -->
   sequent ['ext] { <H> >- "type"{lcoset{'S; 'G; 'b}} }

interactive rcoset_wf {| intro [] |} :
   [wf] sequent [squash] { <H> >- "type"{.'G^car} } -->
   [wf] sequent [squash] { <H> >- "type"{.'S^car} } -->
   [wf] sequent [squash] { <H>; a: 'S^car >- 'a *['G] 'b in 'G^car } -->
   sequent ['ext] { <H> >- "type"{rcoset{'S; 'G; 'b}} }

interactive lcoset_equality {| intro []; eqcd |} :
   [wf] sequent [squash] { <H> >- 'G^car in univ[i:l] } -->
   [wf] sequent [squash] { <H> >- 'S1^car = 'S2^car in univ[i:l] } -->
   [wf] sequent [squash] { <H>; a: 'S1^car >- 'b *['G] 'a in 'G^car } -->
   sequent ['ext] { <H> >- lcoset{'S1; 'G; 'b} = lcoset{'S2; 'G; 'b} in univ[i:l] }

interactive rcoset_equality {| intro []; eqcd |} :
   [wf] sequent [squash] { <H> >- 'G^car in univ[i:l] } -->
   [wf] sequent [squash] { <H> >- 'S1^car = 'S2^car in univ[i:l] } -->
   [wf] sequent [squash] { <H>; a: 'S1^car >- 'a *['G] 'b in 'G^car } -->
   sequent ['ext] { <H> >- rcoset{'S1; 'G; 'b} = rcoset{'S2; 'G; 'b} in univ[i:l] }

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction and Elimination}
  
   @end[doc]
>>
interactive lcoset_intro {| intro [intro_typeinf <<'G>>] |} group[i:l] 'x :
   [main] sequent [squash] { <H> >- subgroup[i:l]{'S; 'G} } -->
   [wf] sequent [squash] { <H> >- 'b in 'G^car } -->
   [wf] sequent [squash] { <H> >- 'x in 'G^car } -->
   [main] sequent ['ext] { <H> >- exst a: 'S^car. 'x = 'b *['G] 'a in 'G^car } -->
   sequent ['ext] { <H> >- lcoset{'S; 'G; 'b} }

interactive rcoset_intro {| intro [intro_typeinf <<'G>>] |} group[i:l] 'x :
   [main] sequent [squash] { <H> >- subgroup[i:l]{'S; 'G} } -->
   [wf] sequent [squash] { <H> >- 'b in 'G^car } -->
   [wf] sequent [squash] { <H> >- 'x in 'G^car } -->
   [main] sequent ['ext] { <H> >- exst a: 'S^car. 'x = 'a *['G] 'b in 'G^car } -->
   sequent ['ext] { <H> >- rcoset{'S; 'G; 'b} }

interactive lcoset_member_intro {| intro [intro_typeinf <<'G>>] |} group[i:l] 'a :
   [main] sequent [squash] { <H> >- subgroup[i:l]{'S; 'G} } -->
   [wf] sequent [squash] { <H> >- 'b in 'G^car } -->
   [wf] sequent [squash] { <H> >- 'x1 = 'x2 in 'G^car } -->
   [wf] sequent [squash] { <H> >- 'a in 'S^car } -->
   [main] sequent [squash] { <H> >- 'x1 = 'b *['G] 'a in 'G^car } -->
   sequent ['ext] { <H> >- 'x1 = 'x2 in lcoset{'S; 'G; 'b} }

interactive rcoset_member_intro {| intro [intro_typeinf <<'G>>] |} group[i:l] 'a :
   [main] sequent [squash] { <H> >- subgroup[i:l]{'S; 'G} } -->
   [wf] sequent [squash] { <H> >- 'b in 'G^car } -->
   [wf] sequent [squash] { <H> >- 'x1 = 'x2 in 'G^car } -->
   [wf] sequent [squash] { <H> >- 'a in 'S^car } -->
   [main] sequent ['ext] { <H> >- 'x1 = 'a *['G] 'b in 'G^car } -->
   sequent ['ext] { <H> >- 'x1 = 'x2 in rcoset{'S; 'G; 'b} }

interactive lcoset_elim {| elim [elim_typeinf <<'G>>] |} 'H group[i:l] :
   [wf] sequent [squash] { <H>; u: lcoset{'S; 'G; 'b}; <J['u]> >- subgroup[i:l]{'S; 'G} } -->
   [wf] sequent [squash] { <H>; u: lcoset{'S; 'G; 'b}; <J['u]> >- 'b in 'G^car } -->
   [main] sequent ['ext] { <H>; u: 'G^car; v: squash{.exst a: 'S^car. 'u = 'b *['G] 'a in 'G^car}; <J['u]> >- 'C['u] } -->
   sequent ['ext] { <H>; u: lcoset{'S; 'G; 'b}; <J['u]> >- 'C['u] }

interactive rcoset_elim {| elim [elim_typeinf <<'G>>] |} 'H group[i:l] :
   [wf] sequent [squash] { <H>; u: rcoset{'S; 'G; 'b}; <J['u]> >- subgroup[i:l]{'S; 'G} } -->
   [wf] sequent [squash] { <H>; u: rcoset{'S; 'G; 'b}; <J['u]> >- 'b in 'G^car } -->
   [main] sequent ['ext] { <H>; u: 'G^car; v: squash{.exst a: 'S^car. 'u = 'a *['G] 'b in 'G^car}; <J['u]> >- 'C['u] } -->
   sequent ['ext] { <H>; u: rcoset{'S; 'G; 'b}; <J['u]> >- 'C['u] }

doc <:doc< 
   @begin[doc]
   @modsubsection{Rules}
  
     If $s$ is a subgroup of group $g$, both the left and right
     cosets of $s$ containing $b$ are subsets of the carrier of
     $g$.
   @end[doc]
>>
interactive lcoset_subset {| intro [intro_typeinf <<'G>>] |} group[i:l] :
   [main] sequent [squash] { <H> >- subgroup[i:l]{'S; 'G} } -->
   [wf] sequent [squash] { <H> >- 'b in 'G^car } -->
   sequent ['ext] { <H> >- \subset{lcoset{'S; 'G; 'b}; .'G^car} }

interactive rcoset_subset {| intro [intro_typeinf <<'G>>] |} group[i:l] :
   [main] sequent [squash] { <H> >- subgroup[i:l]{'S; 'G} } -->
   [wf] sequent [squash] { <H> >- 'b in 'G^car } -->
   sequent ['ext] { <H> >- \subset{rcoset{'S; 'G; 'b}; .'G^car} }

(************************************************************************
 * NORMAL SUBGROUP                                                      *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @modsection{Normal subgroup}
   @modsubsection{Rewrites}
  
   @end[doc]
>>
define unfold_normalSubg : normalSubg[i:l]{'S; 'G} <-->
   subgroup[i:l]{'S; 'G} & all x: 'G^car. lcoset{'S; 'G; 'x} = rcoset{'S; 'G; 'x} in univ[i:l]
doc <:doc< @docoff >>

let fold_normalSubg = makeFoldC << normalSubg[i:l]{'S; 'G} >> unfold_normalSubg

doc <:doc< 
   @begin[doc]
   @modsubsection{Well-formedness}
  
   @end[doc]
>>
interactive normalSubg_wf {| intro [] |} :
   sequent [squash] { <H> >- 'S in group[i:l] } -->
   sequent [squash] { <H> >- 'G in group[i:l] } -->
   sequent [squash] { <H> >- 'G^"*" = 'S^"*" in 'S^car -> 'S^car -> 'S^car } -->
   sequent [squash] { <H>; x: 'G^car; a: 'S^car >- 'x *['G] 'a in 'G^car } -->
   sequent [squash] { <H>; x: 'G^car; a: 'S^car >- 'a *['G] 'x in 'G^car } -->
   sequent ['ext] { <H> >- "type"{normalSubg[i:l]{'S; 'G}} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction and Elimination}
  
   @end[doc]
>>
interactive normalSubg_intro {| intro [] |} :
   [main] sequent [squash] { <H> >- subgroup[i:l]{'S; 'G} } -->
   [main] sequent [squash] { <H>; x: 'G^car >- lcoset{'S; 'G; 'x} = rcoset{'S; 'G; 'x} in univ[i:l] } -->
   sequent ['ext] { <H> >- normalSubg[i:l]{'S; 'G} }

interactive normalSubg_elim {| elim [] |} 'H :
   [main] sequent ['ext] { <H>; x: normalSubg[i:l]{'S; 'G}; <J['x]>; y: subgroup[i:l]{'S; 'G}; z: all b: 'G^car. lcoset{'S; 'G; 'b} = rcoset{'S; 'G; 'b} in univ[i:l] >- 'C['x] } -->
   sequent ['ext] { <H>; x: normalSubg[i:l]{'S; 'G}; <J['x]> >- 'C['x] }

doc <:doc< 
   @begin[doc]
   @modsubsection{Rules}
  
   All subgroups of abelian groups are normal.
   @end[doc]
>>
interactive abel_subg_normal :
   [main] sequent [squash] { <H> >- subgroup[i:l]{'S; 'G} } -->
   [main] sequent ['ext] { <H> >- isCommutative{'G} } -->
   sequent ['ext] { <H> >- normalSubg[i:l]{'S; 'G} }

(************************************************************************
 * GROUP HOMOMORPHISM                                                   *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @modsection{Group homomorphism}
   @modsubsection{Rewrites}
  
   @end[doc]
>>
define unfold_isGroupHom : isGroupHom{'f; 'A; 'B} <-->
   all x: 'A^car. all y: 'A^car. ('f ('x *['A] 'y)) = ('f 'x) *['B] ('f 'y) in 'B^car

define unfold_groupHom1 : groupHom{'A; 'B} <-->
   { f: 'A^car -> 'B^car | isGroupHom{'f; 'A; 'B} }
doc <:doc< @docoff >>

let unfold_groupHom = unfold_groupHom1 thenC addrC [1] unfold_isGroupHom

let fold_isGroupHom = makeFoldC << isGroupHom{'f; 'A; 'B}  >> unfold_isGroupHom
let fold_groupHom1 = makeFoldC << groupHom{'A; 'B}  >> unfold_groupHom1
let fold_groupHom = makeFoldC << groupHom{'A; 'B}  >> unfold_groupHom

doc <:doc< 
   @begin[doc]
   @modsubsection{Well-formedness}
  
   @end[doc]
>>
interactive isGroupHom_wf {| intro [] |} :
   sequent [squash] { <H> >- "type"{'A^car} } -->
   sequent [squash] { <H> >- "type"{'B^car} } -->
   sequent [squash] { <H> >- 'f in 'A^car -> 'B^car } -->
   sequent [squash] { <H>; x: 'A^car; y: 'A^car >- 'x *['A] 'y in 'A^car} -->
   sequent [squash] { <H>; x: 'B^car; y: 'B^car >- 'x *['B] 'y in 'B^car} -->
   sequent ['ext] { <H> >- "type"{isGroupHom{'f; 'A; 'B}} }

interactive groupHom_wf {| intro [] |} :
   sequent [squash] { <H> >- "type"{'A^car} } -->
   sequent [squash] { <H> >- "type"{'B^car} } -->
   sequent [squash] { <H>; x: 'A^car; y: 'A^car >- 'x *['A] 'y in 'A^car} -->
   sequent [squash] { <H>; x: 'B^car; y: 'B^car >- 'x *['B] 'y in 'B^car} -->
   sequent ['ext] { <H> >- "type"{groupHom{'A; 'B}} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction and Elimination}
  
   @end[doc]
>>
interactive isGroupHom_intro {| intro [] |} :
   [wf] sequent [squash] { <H> >- "type"{'A^car}} -->
   [main] sequent ['ext] { <H>; x: 'A^car; y: 'A^car >- ('f ('x *['A] 'y)) = ('f 'x) *['B] ('f 'y) in 'B^car } -->
   sequent ['ext] { <H> >- isGroupHom{'f; 'A; 'B} }

interactive isGroupHom_elim {| elim [] |} 'H :
   [main] sequent ['ext] { <H>; x: isGroupHom{'f; 'A; 'B}; y: all u: 'A^car. all v: 'A^car. ('f ('u *['A] 'v)) = ('f 'u) *['B] ('f 'v) in 'B^car; <J['x]> >- 'C['x] } -->
   sequent ['ext] { <H>; x: isGroupHom{'f; 'A; 'B}; <J['x]> >- 'C['x] }

interactive groupHom_intro {| intro [intro_typeinf <<'A>>] |} group[i:l] :
   [wf] sequent [squash] { <H> >- 'A in group[i:l] } -->
   [wf] sequent [squash] { <H> >- 'B in group[i:l] } -->
   sequent [squash] { <H> >- 'f in 'A^car -> 'B^car } -->
   [main] sequent ['ext] { <H> >- isGroupHom{'f; 'A; 'B} } -->
   sequent ['ext] { <H> >- 'f in groupHom{'A; 'B} }

interactive groupHom_elim {| elim [elim_typeinf <<'B>>] |} 'H group[i:l] :
   [wf] sequent [squash] { <H>; f: groupHom{'A; 'B}; <J['f]> >- 'A in group[i:l] } -->
   [wf] sequent [squash] { <H>; f: groupHom{'A; 'B}; <J['f]> >- 'B in group[i:l] } -->
   [main] sequent ['ext] { <H>; f: 'A^car -> 'B^car; u: all x: 'A^car. all y: 'A^car. ('f ('x *['A] 'y)) = ('f 'x) *['B] ('f 'y) in 'B^car; <J['f]> >- 'C['f] } -->
   sequent ['ext] { <H>; f: groupHom{'A; 'B}; <J['f]> >- 'C['f] }

doc <:doc< 
   @begin[doc]
   @modsubsection{Rules}
  
     For any groups $G_1$ and $G_2$, there is always at least
     one homomorphism $f@colon G_1 @rightarrow G_2$ which
     maps all elements of $@car{G_1}$ into $@id{G_2}$. This
     is called the Trivial Homomorphism.
   @end[doc]
>>
interactive trivial_hom group[i:l] :
   [wf] sequent [squash] { <H> >- 'A in group[i:l] } -->
   [wf] sequent [squash] { <H> >- 'B in group[i:l] } -->
   [wf] sequent [squash] { <H> >- 'f in 'A^car -> 'B^car } -->
   [main] sequent ['ext] { <H>; x: 'A^car >- 'f 'x = 'B^"1" in 'B^car } -->
   sequent ['ext] { <H> >- 'f in groupHom{'A; 'B} }

doc <:doc< 
   @begin[doc]
   Let $f@colon A @rightarrow B$ be a group
   homomorphism of $A$ into $B$.
  
   $@space @space$
  
     $f$ maps the identity of $A$ into the identity of $B$.
   @end[doc]
>>
interactive groupHom_id {| intro [AutoMustComplete; intro_typeinf <<'A>>] |} group[i:l] :
   [wf] sequent [squash] { <H> >- 'A in group[i:l] } -->
   [wf] sequent [squash] { <H> >- 'B in group[i:l] } -->
   [main] sequent ['ext] { <H> >- 'f in groupHom{'A; 'B} } -->
   sequent ['ext] { <H> >- 'f 'A^"1" = 'B^"1" in 'B^car }

doc <:doc< 
   @begin[doc]
  
     $f$ maps the inverse of an element $a$ in $@car{A}$ into
     the inverse of $f[a]$ in $@car{B}$.
   @end[doc]
>>
interactive groupHom_inv {| intro [AutoMustComplete; intro_typeinf <<'A>>] |} group[i:l] :
   [wf] sequent [squash] { <H> >- 'A in group[i:l] } -->
   [wf] sequent [squash] { <H> >- 'B in group[i:l] } -->
   [wf] sequent [squash] { <H> >- 'a in 'A^car } -->
   [wf] sequent [squash] { <H> >- 'f in groupHom{'A; 'B} } -->
   sequent ['ext] { <H> >- 'f ('A^inv 'a) = 'B^inv ('f 'a) in 'B^car }

doc <:doc< 
   @begin[doc]
  
   If $f$ is @emph{onto}, then $A$ is abelian
   implies $B$ is abelian.
   @end[doc]
>>
interactive groupHom_abel 'A 'f :
   [wf] sequent [squash] { <H> >- 'A in abelg[i:l] } -->
   [wf] sequent [squash] { <H> >- 'B in group[i:l] } -->
   [wf] sequent [squash] { <H> >- 'f in groupHom{'A; 'B} } -->
   [main] sequent ['ext] { <H>; x: 'B^car >- exst y: 'A^car. 'x = 'f 'y in 'B^car } -->
   sequent ['ext] { <H> >- 'B in abelg[i:l] }

doc <:doc< 
   @begin[doc]
  
     If $S$ is a subgroup of $A$, then the image of $S$ under
     $f$ is a subgroup of $B$.
   @end[doc]
>>
interactive groupHom_subg1 'f 'A 'S :
   [wf] sequent [squash] { <H> >- 'B in group[i:l] } -->
   [main] sequent [squash] { <H> >- 'f in groupHom{'A; 'B} } -->
   [main] sequent [squash] { <H> >- subgroup[i:l]{'S; 'A} } -->
   sequent ['ext] { <H> >- subgroup[i:l]{{car={x: 'B^car | exst y: 'S^car. 'x = 'f 'y in 'B^car}; "*"='B^"*"; "1"='B^"1"; inv='B^inv}; 'B} }

doc <:doc< 
   @begin[doc]
  
     If $T$ is a subgroup of $B$, then the inverse image of
     $T$ under $f$ is a subgroup of $A$.
   @end[doc]
>>
interactive groupHom_subg2 'f 'B 'T :
   [wf] sequent [squash] { <H> >- 'A in group[i:l] } -->
   [main] sequent [squash] { <H> >- 'f in groupHom{'A; 'B} } -->
   [main] sequent [squash] { <H> >- subgroup[i:l]{'T; 'B} } -->
   [wf] sequent [squash] { <H>; x: 'A^car >- "type"{'f 'x in 'T^car} } -->
   sequent ['ext] { <H> >- subgroup[i:l]{{car={x: 'A^car | 'f 'x in 'T^car subset 'B^car}; "*"='A^"*"; "1"='A^"1"; inv='A^inv}; 'A} }

doc <:doc< @docoff >>

(************************************************************************
 * GROUP ISOMORPHISM                                                    *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @modsection{Group isomorphism}
   @modsubsection{Rewrites}
   An isomorphism is a homomorphism that is one-to-one and onto.
  
   @end[doc]
>>
define unfold_isBijective : isBijective{'f; 'A; 'B} <-->
   (all x: 'A^car. all y: 'A^car. ('f 'x = 'f 'y in 'B^car => 'x = 'y in 'A^car)) & (all z: 'B^car. exst u: 'A^car. ('z = 'f 'u in 'B^car))

define unfold_groupIso : groupIso{'A; 'B} <-->
   { f: groupHom{'A; 'B} | isBijective{'f; 'A; 'B} }
doc <:doc< @docoff >>

let fold_isBijective = makeFoldC << isBijective{'f; 'A; 'B}  >> unfold_isBijective
let fold_groupIso = makeFoldC << groupIso{'A; 'B}  >> unfold_groupIso

doc <:doc< 
   @begin[doc]
   @modsubsection{Well-formedness}
  
   @end[doc]
>>
interactive isBijective_wf {| intro [] |} :
   sequent [squash] { <H> >- "type"{'A^car} } -->
   sequent [squash] { <H> >- "type"{'B^car} } -->
   sequent [squash] { <H> >- 'f in 'A^car -> 'B^car } -->
   sequent ['ext] { <H> >- "type"{isBijective{'f; 'A; 'B}} }

interactive groupIso_wf {| intro [] |} :
   sequent [squash] { <H> >- "type"{'A^car} } -->
   sequent [squash] { <H> >- "type"{'B^car} } -->
   sequent [squash] { <H>; x: 'A^car; y: 'A^car >- 'x *['A] 'y in 'A^car} -->
   sequent [squash] { <H>; x: 'B^car; y: 'B^car >- 'x *['B] 'y in 'B^car} -->
   sequent ['ext] { <H> >- "type"{groupIso{'A; 'B}} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction and Elimination}
  
   @end[doc]
>>
interactive isBijective_intro {| intro [AutoMustComplete] |} :
   [wf] sequent [squash] { <H> >- "type"{'A^car}} -->
   [wf] sequent [squash] { <H> >- "type"{'B^car}} -->
   [wf] sequent [squash] { <H> >- 'f in 'A^car -> 'B^car } -->
   [main] sequent ['ext] { <H>; x: 'A^car; y: 'A^car; u: 'f 'x = 'f 'y in 'B^car >- 'x = 'y in 'A^car } -->
   [main] sequent ['ext] { <H>; z: 'B^car >- exst u: 'A^car. 'z = 'f 'u in 'B^car } -->
   sequent ['ext] { <H> >- isBijective{'f; 'A; 'B} }

interactive isBijective_elim {| elim [] |} 'H :
   [main] sequent ['ext] { <H>; p: isBijective{'f; 'A; 'B}; v: all x: 'A^car. all y: 'A^car. ('f 'x = 'f 'y in 'B^car => 'x = 'y in 'A^car); w: all z: 'B^car. exst u: 'A^car. ('z = 'f 'u in 'B^car); <J['p]> >- 'C['p] } -->
   sequent ['ext] { <H>; p: isBijective{'f; 'A; 'B}; <J['p]> >- 'C['p] }


interactive groupIso_intro {| intro [intro_typeinf <<'A>>] |} group[i:l] :
   [wf] sequent [squash] { <H> >- 'A in group[i:l] } -->
   [wf] sequent [squash] { <H> >- 'B in group[i:l] } -->
   [wf] sequent [squash] { <H> >- 'f in groupHom{'A; 'B} } -->
   [main] sequent ['ext] { <H> >- isBijective{'f; 'A; 'B} } -->
   sequent ['ext] { <H> >- 'f in groupIso{'A; 'B} }

interactive groupIso_elim {| elim [elim_typeinf <<'B>>] |} 'H group[i:l] :
   [wf] sequent [squash] { <H>; f: groupIso{'A; 'B}; <J['f]> >- 'A in group[i:l] } -->
   [wf] sequent [squash] { <H>; f: groupIso{'A; 'B}; <J['f]> >- 'B in group[i:l] } -->
   [main] sequent ['ext] { <H>; f: groupHom{'A; 'B}; u: squash{isBijective{'f; 'A; ' B}}; <J['f]> >- 'C['f] } -->
   sequent ['ext] { <H>; f: groupIso{'A; 'B}; <J['f]> >- 'C['f] }

doc <:doc< @docoff >>

(************************************************************************
 * GROUP KERNEL                                                         *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @modsection{Group kernel}
   @modsubsection{Rewrites}
  
   @end[doc]
>>
define unfold_groupKer : groupKer{'f; 'A; 'B} <-->
   { x: 'A^car | 'f 'x = 'B^"1" in 'B^car }

doc <:doc< @docoff >>

let fold_groupKer = makeFoldC << groupKer{'f; 'A; 'B}  >> unfold_groupKer

doc <:doc< 
   @begin[doc]
   @modsubsection{Well-formedness}
  
   @end[doc]
>>
interactive groupKer_Equality {| intro []; eqcd |} :
   [wf] sequent [squash] { <H> >- 'A1^car = 'A2^car in univ[i:l] } -->
   [wf] sequent [squash] { <H> >- 'B1^car = 'B2^car in univ[i:l] } -->
   [wf] sequent [squash] { <H>; x: 'A1^car >- 'f1 'x = 'f2 'x in 'B1^car } -->
   [wf] sequent [squash] { <H> >- 'B1^"1" = 'B2^"1" in 'B2^car } -->
   sequent ['ext] { <H> >- groupKer{'f1; 'A1; 'B1} = groupKer{'f2; 'A2; 'B2} in univ[i:l] }

interactive groupKer_wf {| intro [] |} :
   sequent [squash] { <H> >- "type"{'A^car} } -->
   sequent [squash] { <H> >- 'f in 'A^car -> 'B^car } -->
   sequent [squash] { <H> >- 'B^"1" in 'B^car } -->
   sequent ['ext] { <H> >- "type"{groupKer{'f; 'A; 'B}} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction and Elimination}
  
   @end[doc]
>>
interactive groupKer_intro {| intro [intro_typeinf <<'A>>] |} group[i:l] 'x :
   sequent [squash] { <H> >- 'A in group[i:l] } -->
   sequent [squash] { <H> >- 'B in group[i:l] } -->
   sequent [squash] { <H> >- 'f in groupHom{'A; 'B} } -->
   sequent [squash] { <H> >- 'x in 'A^car } -->
   sequent [squash] { <H> >- 'f 'x = 'B^"1" in 'B^car } -->
   sequent ['ext] { <H> >- groupKer{'f; 'A; 'B} }

interactive groupKer_member_intro {| intro [intro_typeinf <<'A>>] |} group[i:l] :
   sequent [squash] { <H> >- 'A in group[i:l] } -->
   sequent [squash] { <H> >- 'B in group[i:l] } -->
   sequent [squash] { <H> >- 'f in groupHom{'A; 'B} } -->
   sequent [squash] { <H> >- 'x1 = 'x2 in 'A^car } -->
   sequent [squash] { <H> >- 'f 'x1 = 'B^"1" in 'B^car } -->
   sequent ['ext] { <H> >- 'x1 = 'x2 in groupKer{'f; 'A; 'B} }

interactive groupKer_elim {| elim [elim_typeinf <<'B>>] |} 'H group[i:l] :
   [wf] sequent [squash] { <H>; x: groupKer{'f; 'A; 'B}; <J['x]> >- 'A in group[i:l] } -->
   [wf] sequent [squash] { <H>; x: groupKer{'f; 'A; 'B}; <J['x]> >- 'B in group[i:l] } -->
   [main] sequent ['ext] { <H>; x: 'A^car; u: 'f 'x = 'B^"1" in 'B^car; <J['x]> >- 'C['x] } -->
   sequent ['ext] { <H>; x: groupKer{'f; 'A; 'B}; <J['x]> >- 'C['x] }

doc <:doc< 
   @begin[doc]
   @modsubsection{Rules}
  
   The kernel of a group homomorphism from $A$ into $B$ is a subgroup
   of $A$.
   @end[doc]
>>
interactive groupKer_subg {| intro [] |} :
   [wf] sequent [squash] { <H> >- 'A in group[i:l] } -->
   [wf] sequent [squash] { <H> >- 'B in group[i:l] } -->
   [wf] sequent [squash] { <H> >- 'f in groupHom{'A; 'B} } -->
   sequent ['ext] { <H> >- subgroup[i:l]{{car=groupKer{'f; 'A; 'B}; "*"='A^"*"; "1"='A^"1"; inv='A^inv}; 'A} }

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

dform isGroup_df : except_mode[src] :: isGroup{'G} =
   `"isGroup(" slot{'G} `")"

dform inv_df1 : except_mode[src] :: parens :: "prec"[prec_inv] :: ('G^inv 'a) =
   math_inv{'G; 'a}

dform abelg_df : except_mode[src] :: abelg[i:l] =
   math_abelg{slot[i:l]}

dform subgroup_df : except_mode[src] :: subgroup[i:l]{'S; 'G} =
   math_subgroup{slot[i:l]; 'S; 'G}

dform lcoset_df : except_mode[src] :: lcoset{'H; 'G; 'a} =
   math_lcoset{'H; 'G; 'a}

dform rcoset_df : except_mode[src] :: rcoset{'H; 'G; 'a} =
   math_rcoset{'H; 'G; 'a}

dform normalSubg_df : except_mode[src] :: normalSubg[i:l]{'S; 'G} =
   math_normalSubg{slot[i:l]; 'S; 'G}

dform isGroupHom_df : except_mode[src] :: isGroupHom{'f; 'A; 'B} =
   `"isGroupHom(" slot{'f} `"; " slot{'A} `"; " slot{'B}  `")"

dform groupHom_df : except_mode[src] :: groupHom{'A; 'B} =
   math_groupHom{'A; 'B}

dform isBijective_df : except_mode[src] :: isBijective{'f; 'A; 'B} =
   math_isBijective{'f; 'A; 'B}

dform groupIso_df : except_mode[src] :: groupIso{'A; 'B} =
   math_groupIso{'A; 'B}

dform groupKer_df : except_mode[src] :: groupKer{'f; 'A; 'B} =
   math_groupKer{'f; 'A; 'B}

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
