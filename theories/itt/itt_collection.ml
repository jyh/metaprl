(*
 * Collection.
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
 * Author: Alexei Kopylov
 * kopylov@cs.cornell.edu
 *
 *)

include Itt_theory

open Itt_equal

open Printf
open Dag
open Imp_dag

open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError
open Mp_resource
open Mptop

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Tactic_type.Sequent

open Var

open Top_conversionals

open Base_auto_tactic
open Base_dtactic

open Itt_logic
open Itt_struct
open Itt_tunion
open Itt_int

(*===--- unsquash ---===*)

prim unsquash_with_type 'H 'J :
 sequent[squash] { 'H; x:'A; 'J >- "type"{'T}} -->
 sequent['ext] { 'H; x:squash{'A}; 'J >- "type"{'T}} =
 it

prim unsquash_with_equal 'H 'J :
 sequent[squash] { 'H; x:'A; 'J >- 'a='b in 'T} -->
 sequent['ext] { 'H; x:squash{'A}; 'J >- 'a='b in 'T} =
 it

let unsquash_with_typeT i p =
    let i', j = hyp_indices p i in
         unsquash_with_type i' j p
let unsquash_with_equalT i p =
    let i', j = hyp_indices p i in
         unsquash_with_equal i' j p
let unsquashT i = unsquash_with_typeT i orelseT unsquash_with_equalT i

(*===--- auto... ---===*)

let univTypeComplT  = completeT ((function p -> univTypeT (get_univ_arg p) p) thenT autoT)


let resource auto += {
   auto_name = "univTypeT";
   auto_prec = logic_prec;
   auto_tac = auto_wrap univTypeComplT
}

let memberTypeT a = equalTypeT a a thenT tryT (completeT autoT)

let equalRef2T a = equalRefT a thenT equalSymT

let equalRefComplT a =  completeT (equalRefT a thenT autoT) orelseT  completeT (equalRef2T a thenT autoT)

let autoRT = repeatT (autoT thenT onAllClausesT (rwh reduceC))


interactive reverse 'H :
   sequent ['ext] { 'H >- all u:'J.'T['u] } -->
   sequent ['ext] { 'H; u:'J >- 'T['u] }
let reverseT p =
      let j,_ = Sequent.hyp_indices p ((Sequent.hyp_count p)) in
                reverse j p


(*===--- subst ---===*)

interactive substitution 'H ('t1 = 't2 in 'T2) bind{x. 'T1['x]} :
   sequent [squash] { 'H >- 't1 = 't2 in 'T2 } -->
   sequent ['ext] { 'H >- 'T1['t2] } -->
   sequent [squash] { 'H; x: 'T2; u:'x='t1 in 'T2; v:'x='t2 in 'T2 >- "type"{'T1['x]} } -->
   sequent ['ext] { 'H >- 'T1['t1] }

interactive hypSubstitution 'H 'J ('t1 = 't2 in 'T2) bind{y. 'A['y]} 'z :
   sequent [squash] { 'H; x: 'A['t1]; 'J['x] >- 't1 = 't2 in 'T2 } -->
   sequent ['ext] { 'H; x: 'A['t2];'J['x] >- 'T1['x] }  -->
   sequent [squash] { 'H; x: 'A['t1]; 'J['x]; z: 'T2;  u:'z='t1 in 'T2; v:'z='t2 in 'T2  >- "type"{'A['z]} } -->
   sequent ['ext] { 'H; x: 'A['t1]; 'J['x] >- 'T1['x] }



(*
 * Substitution.
 * The binding term may be optionally supplied.
 *)
let substConclT t p =
   let _, a, _ = dest_equal t in
   let bind =
      try
         let t1 = get_with_arg p in
            if is_xbind_term t1 then
               t1
            else
               raise (RefineError ("substT", StringTermError ("need a \"bind\" term: ", t1)))
      with
         RefineError _ ->
            let x = get_opt_var_arg "z" p in
               mk_xbind_term x (var_subst (concl p) a x)
   in
      (substitution (hyp_count_addr p) t bind
       thenLT [addHiddenLabelT "equality";
               addHiddenLabelT "main";
               addHiddenLabelT "aux"]) p

(*
 * Hyp substitution requires a replacement.
 *)
let substHypT i t p =
   let _, a, _ = dest_equal t in
   let _, t1 = Sequent.nth_hyp p i in
   let z = get_opt_var_arg "z" p in
   let bind =
      try
         let b = get_with_arg p in
            if is_xbind_term b then
               b
            else
               raise (RefineError ("substT", StringTermError ("need a \"bind\" term: ", b)))
      with
         RefineError _ ->
            mk_xbind_term z (var_subst t1 a z)
   in
   let i, j = hyp_indices p i in
      (hypSubstitution i j t bind z
       thenLT [addHiddenLabelT "equality";
               addHiddenLabelT "main";
               addHiddenLabelT "aux"]) p

(*
 * General substition.
 *)
let substT t i =
   if i = 0 then
      substConclT t
   else
      substHypT i t

(*
 * Derived versions.
 *)
let hypSubstT i j p =
   let _, h = Sequent.nth_hyp p i in
      (substT h j thenET nthHypT i) p

let revHypSubstT i j p =
   let t, a, b = dest_equal (snd (Sequent.nth_hyp p i)) in
   let h' = mk_equal_term t b a in
      (substT h' j thenET (equalSymT thenT nthHypT i)) p


(*===--- CutMember ---===*)

interactive cutMember0 'H ('s IN 'S) 'z bind{x.'T['x]}:
   sequent [squash] { 'H >- 's IN 'S } -->
   sequent ['ext] { 'H; z: 'S >- 'T['z] } -->
   sequent ['ext] { 'H >- 'T['s] }

let cutMemberT ss  p =
   let _, s, _ = dest_equal ss in
   let x=  get_opt_var_arg (if is_var_term s then dest_var s else  "z") p in
   let bind =
      try
         let b = get_with_arg p in
            if is_xbind_term b then
               b
            else
               raise (RefineError ("cutMemberT", StringTermError ("need a \"bind\" term: ", b)))
      with
         RefineError _ ->
            mk_xbind_term x (var_subst (concl p) s x)
   in
   let i=(Sequent.hyp_count_addr p) in
      cutMember0 i ss  x bind p

let useAssumptionT n  p =
   let _, assums = dest_msequent (Sequent.msequent p) in
   let a = List.nth assums n in
   let g = TermMan.nth_concl  a 0 in
      cutMemberT g p


let cutMember1T ss  = reverseT thenT cutMemberT ss thenLT [idT;dT 0]


(*********************************************************)
(*                                                       *)
(*                      COLLECTIONS                      *)
(*                                                       *)
(*********************************************************)


(********************** Definitions **********************)


(***===--- Basic definitions  ---===***)


(*--- col ---*)

declare col[l:l]{'T}

prim_rw unfold_col :  col[l:l]{'T} <--> (I:univ[l:l] * ('I -> 'T))

(* collection[l](T) ЯЭЭЮ (I:”[l] г (I ЭЮ T))
 *)

interactive col_wf {| intro [] |} 'H :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent['ext]{'H >- "type"{col[l:l]{'T}}}

(* [М] H џ T Type ЭЭЮ
 * [ext] H џ collection[l](T) Type
 *)
interactive col_wf2 'H :
   sequent[squash]{'H >- 'T IN univ[l ':l] } -->
   sequent['ext]{'H >- col[l:l]{'T} IN univ[l ':l] }

(* [М] H џ T С ”[{l'}] ЭЭЮ
 * [ext] H џ collection[l](T) С ”[{l'}]
 *)
interactive col_elim 'H 'J 'I 'phi:
   sequent['ext]  {'H; I:univ[l:l]; phi:'I->'T; 'J[('I,'phi)] >- 'Z[('I,'phi)]} -->
   sequent['ext]  {'H; C:col[l:l]{'T}; 'J['C] >- 'Z['C]}

let d_colT i p =
   if i=0
    then (rwh unfold_col 0 thenT dT 0) p
    else
       let a,b = maybe_new_vars2 p "I" "phi" in
       let i', j = hyp_indices p i in
          col_elim i' j a b p

let cutColT c = cutMemberT  (mk_equal_term <<col[l:l]{'T}>> c c) thenLT [tryT (completeT autoT);  d_colT (-1) thenT rwh reduceC 0]

let cutColS c = cutMemberT  (mk_equal_term <<col[l:l]{'S}>> c c) thenLT [tryT (completeT autoT);  d_colT (-1) thenT rwh reduceC 0]

(*--- col_member ---*)

declare col_member{'T;'C;'x}

prim_rw unfold_col_member : col_member{'T;'C;'x} <-->
             (exst i:fst{'C} . (snd{'C} 'i = 'x in 'T))
(*  (x С <I,phi>) in collection(T) ЯЭЭЮ
 *  (Щi:I. (phi i = x in T))
 *)
interactive_rw reduce_member : col_member{'T;('I,'phi);'x} <-->
     (exst i:'I . ('phi 'i = 'x in 'T))

let resource reduce += << col_member{'T;('I,'phi);'x} >>, reduce_member

(*      [М] H џ T С ”[l] ЭЭЮ
 *      [М] H џ x С T ЭЭЮ
 *      [М] H џ C С collection[l](T) ЭЭЮ
 *      [ext] H џ (x С C) in collection(T) С ”[l]
 *)
interactive col_member_univ {| intro [] |} 'H:
   sequent[squash]{'H >- 'T IN univ[l:l] } -->
   sequent[squash]{'H >- 'x IN 'T } -->
   sequent[squash]{'H >- 'C IN col[l:l]{'T} } -->
   sequent['ext]{'H >- col_member{'T;'C;'x} IN univ[l:l] }

(*      [М] H џ x С T ЭЭЮ
 *      [М] H џ C С collection[l](T) ЭЭЮ
 *      [ext] H џ (x С C) in collection(T) Type
*)
interactive col_member_wf {| intro [intro_univ_arg] |} 'H univ[l:l]:
   sequent[squash]{'H >- 'x IN 'T } -->
   sequent[squash]{'H >- 'C IN col[l:l]{'T} } -->
   sequent['ext]{'H >- "type"{col_member{'T;'C;'x}}}

(*      [М] H џ x С C in collection(T) ЭЭЮ
 *      [ext] H џ x С T
 *)
interactive mem_col_mem 'H 'C:
   sequent[squash] {'H >- col_member{'T;'C;'x}} -->
   sequent['ext]   {'H >- 'x IN 'T }

let mem_col_memT cc p = mem_col_mem  (Sequent.hyp_count_addr p) cc p


(*--- col_equal ---*)

declare col_equal{'T;'C_1;'C_2}

(*       (C_1 = C_2 in collection(T)) ЯЭЭЮ
 *       (Шx:T. (x С C_1) in collection(T) ЬЭЮ (x С C_2) in collection(T))
 *)
prim_rw unfold_col_equal : col_equal{'T;'C_1;'C_2} <-->
   (all x:'T. iff{col_member{'T;'C_1;'x};col_member{'T;'C_2;'x}})

(*
 *       [М] H џ T С ”[l] ЭЭЮ
 *       [М] H џ C_1 С collection[l](T) ЭЭЮ
 *       [М] H џ C_2 С collection[l](T) ЭЭЮ
 *       [ext] H џ (C_1 = C_2 in collection(T)) С ”[l]
 *)
interactive col_equal_univ {| intro [] |} 'H :
   sequent[squash]{'H >- 'T IN univ[l:l] } -->
   sequent[squash]{'H >- 'C_1 IN col[l:l]{'T} } -->
   sequent[squash]{'H >- 'C_2 IN col[l:l]{'T} } -->
   sequent['ext]{'H >- col_equal{'T;'C_1;'C_2} IN univ[l:l] }

(*        [М] H џ T Type ЭЭЮ
 *        [М] H џ C_1 С collection[l](T) ЭЭЮ
 *        [М] H џ C_2 С collection[l](T) ЭЭЮ
 *        [ext] H џ (C_1 = C_2 in collection(T)) Type
 *)
interactive col_equal_wf {| intro [intro_univ_arg] |} 'H univ[l:l] :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H >- 'C_1 IN col[l:l]{'T} } -->
   sequent[squash]{'H >- 'C_2 IN col[l:l]{'T} } -->
   sequent['ext]{'H >- "type"{ col_equal{'T;'C_1;'C_2} }}

(*       [М] H џ T Type ЭЭЮ
 *       [М] H џ C С collection[l](T) ЭЭЮ
 *       [ext] H џ C = C in collection(T)
 *)
interactive col_equal_reflexivity {| intro [intro_univ_arg] |} 'H univ[l:l] :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]  {'H >- 'C IN col[l:l]{'T} } -->
   sequent['ext]  {'H >-  col_equal{'T;'C;'C} }

(*
 *       [М] H џ T Type ЭЭЮ
 *       [М] H џ A С collection[l](T) ЭЭЮ
 *       [М] H џ C С collection[l](T) ЭЭЮ
 *       [ext] H џ A = B in collection(T) ЭЭЮ
 *       [ext] H џ B = C in collection(T) ЭЭЮ
 *       [ext] H џ A = C in collection(T)
 *)
interactive col_equal_trans  'H univ[l:l] 'B:
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]  {'H >- 'A IN col[l:l]{'T} } -->
   sequent[squash]  {'H >- 'C IN col[l:l]{'T} } -->
   sequent['ext]    {'H >-  col_equal{'T;'A;'B} }  -->
   sequent['ext]    {'H >-  col_equal{'T;'B;'C} }  -->
   sequent['ext]    {'H >-  col_equal{'T;'A;'C} }

(*
 *       [М] H џ T Type ЭЭЮ
 *       [М] H џ A С collection[l](T) ЭЭЮ
 *       [М] H џ B С collection[l](T) ЭЭЮ
 *       [ext] H џ A = B in collection(T) ЭЭЮ
 *       [ext] H џ B = A in collection(T)
 *)
interactive col_equal_sym  'H univ[l:l] :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]  {'H >- 'A IN col[l:l]{'T} } -->
   sequent[squash]  {'H >- 'B IN col[l:l]{'T} } -->
   sequent['ext]    {'H >-  col_equal{'T;'A;'B} }  -->
   sequent['ext]    {'H >-  col_equal{'T;'B;'A} }


(*--- Col --*)

declare Col[l:l]{'T}


prim_rw unfold_Col :  Col[l:l]{'T} <--> (quot x,y: col[l:l]{'T} // col_equal{'T;'x;'y})
let fold_Col = makeFoldC <<Col[l:l]{'T}>> unfold_Col

interactive _Col_wf {| intro [] |} 'H :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent['ext]{'H >- "type"{Col[l:l]{'T}}}
(* rwh unfold_Col 0 thenT atT <<univ[l:l]>> autoT*)

interactive _Col_wf2 'H :
   sequent[squash]{'H >- 'T IN univ[l ':l] } -->
   sequent['ext]{'H >- Col[l:l]{'T} IN univ[l ':l] }

interactive member_Col 'H :
  sequent[squash]{'H >- "type"{'T}} -->
  sequent[squash]{'H >- 'C IN col[l:l]{'T} } -->
  sequent['ext]{'H >- 'C IN Col[l:l]{'T} }

let member_ColT p =  member_Col (Sequent.hyp_count_addr p) p

(*--- Col_member ---*)

declare Col_member[l:l]{'T;'C;'x}

prim_rw unfold_Col_member : Col_member[l:l]{'T;'C;'x} <-->
   (exst c:col[l:l]{'T} . (('c='C in Col[l:l]{'T}) and col_member{'T;'c;'x}))

interactive _Col_member_wf {| intro [intro_univ_arg] |} 'H univ[l:l] :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H >- 'x IN 'T } -->
   sequent[squash]{'H >- 'C IN Col[l:l]{'T} } -->
   sequent['ext]{'H >- "type"{Col_member[l:l]{'T;'C;'x}}}

(***===--- connection with types ---===***)

(*--- type_col ---*)

declare type_col{'T}

prim_rw unfold_type_col : type_col{'T} <--> (('T,lambda{x.'x}))

(*  НT ЯЭЭЮ <T,(«x.x)>
 *)
interactive type_col_wf {| intro [] |} 'H :
   sequent[squash] {'H >- 'T IN univ[l:l] } -->
   sequent['ext]   {'H >- type_col{'T} IN col[l:l]{'T} }

(*
 *       x С T <--> x С НT in collection(T)
 *
 *)
interactive member_type_col {| intro [] |} 'H :
   sequent[squash] {'H >- 'x IN 'T} -->
   sequent['ext]  {'H >- col_member{'T;type_col{'T};'x}}

interactive member_type_col_elim {| elim [] |} 'H 'J :
   sequent['ext]   {'H; 'J; w: 'x IN 'T >- 'Z } -->
   sequent['ext]   {'H; u:col_member{'T;type_col{'T};'x}; 'J >- 'Z }

(*--- col_type ---*)
declare col_type{'C;'T}

(* ОC ЯЭЭЮ { x:T | (x С C) in collection(T)}
 *)
prim_rw unfold_col_type : col_type{'C;'T} <--> ({ x:'T | col_member{'T;'C;'x} })

(*       [М] H џ T Type ЭЭЮ
 *       [ext] H џ C С collection[l](T) ЭЭЮ
 *       [ext] H џ ОC Type
 *)
interactive col_type_wf {| intro [intro_univ_arg] |} 'H univ[l:l] :
   sequent[squash] {'H >- "type"{'T}} -->
   sequent['ext]   {'H >- 'C IN col[l:l]{'T} } -->
   sequent['ext]   {'H >-"type"{col_type{'C;'T}}}


(***===--- basic operations ---===***)

(*--- singleton ---*)

declare singlenton{'x}

(* <x> ЯЭЭЮ <Unit,(«i.x)> *)
prim_rw unfold_singlenton :  singlenton{'x} <--> ((unit, lambda{i.'x}))

(*       [М] H џ x С T ЭЭЮ
 *       [ext] H џ <x> С collection[l](T)
 *)
interactive singlenton_wf {| intro [] |} 'H :
   sequent[squash]{'H >- 'x IN 'T } -->
   sequent['ext]  {'H >- singlenton{'x} IN col[l:l]{'T} }

(*       y С <x> in collection(T)  <==>  x = y in T
 *)
interactive member_singlenton {| intro [] |} 'H :
   sequent[squash]{'H >- equal{'T;'x;'y}} -->
   sequent['ext]  {'H >- col_member{'T; singlenton{'x}; 'y}}

interactive member_singlenton_elim {| elim [] |} 'H 'J :
   sequent['ext]{'H; 'J; v:equal{'T;'x;'y} >- 'Z} -->
   sequent['ext]  {'H; u:col_member{'T; singlenton{'x}; 'y}; 'J >- 'Z}


(*--- union ---*)

declare union{'X;x.'Y['y]}

prim_rw unfold_union : union{'X;x.'Y['x]} <-->
   (( i:fst{'X} * fst{'Y[snd{'X} 'i]},
      lambda{ij. snd{'Y[snd{'X} fst{'ij}]} snd{'ij}}
   ))

(*
 *    (ЧxС<I,phi>.<J[x],psi[x]>) ЯЭЭЮ
 *     <(i:I г J[(phi i)]),
 *     («ij.psi[(phi ij.1)] ij.2)>
 *)

interactive_rw reduce_union : union{('I,'phi); x.('J['x],'psi['x])} <-->
   (( i:'I * 'J['phi 'i],
      lambda{ij. 'psi['phi fst{'ij}] snd{'ij}}
   ))

let resource reduce += << union{('I,'phi); x.('J['x],'psi['x])} >>, reduce_union

(*        [М] H џ T Type ЭЭЮ
 *        [М] H џ S Type ЭЭЮ
 *        [М] H џ X С collection[l](T) ЭЭЮ
 *        [М] H; x: T; u: x С X in collection(T) џ Y[x] С collection[l](S) ЭЭЮ
 *        [ext] H џ ЧxСX.Y[x] С collection[l](S)
 *)
interactive union_wf {| intro [] |} 'H 'T:
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H >- "type"{'S}} -->
   sequent[squash]{'H >- 'X IN col[l:l]{'T} } -->
   sequent[squash]{'H; x:'T; u:col_member{'T;'X;'x} >- 'Y['x] IN col[l:l]{'S} } -->
   sequent['ext]  {'H >- union{'X;x.'Y['x]} IN col[l:l]{'S} }

(* y С ЧxСX.Y[x] in collection(S) <==>
 * Щx:T. (x С X) in collection(T) П (y С Y[x]) in collection(S)
 *)

let univ_with_args_fun p _ = [get_univ_arg p; get_with_arg p]
let intro_univ_with_args = IntroArgsOption (univ_with_args_fun, None)
let elim_univ_with_args = ElimArgsOption (univ_with_args_fun, None)

interactive member_union {| intro [intro_univ_with_args] |} 'H univ[l:l] ('x IN 'T) :
   sequent[squash]{'H >- 'X IN col[l:l]{'T} } -->
   sequent[squash]{'H; x:'T; u:col_member{'T;'X;'x} >- 'Y['x] IN col[l:l]{'S} } -->
   sequent['ext] {'H >- col_member{'T;'X;'x} } -->
   sequent['ext] {'H >- col_member{'S;'Y['x];'y}} -->
   sequent['ext] {'H >- col_member{'S;union{'X;x.'Y['x]};'y}}

interactive member_union_elim {| elim [elim_univ_with_args] |} 'H 'J univ[l:l] 'T:
   sequent[squash]{'H; 'J >- 'X IN col[l:l]{'T} } -->
   sequent[squash]{'H; 'J; x:'T; u:col_member{'T;'X;'x} >- 'Y['x] IN col[l:l]{'S} } -->
   sequent['ext]   {'H; 'J; x:'T; v:col_member{'T;'X;'x}; u: col_member{'S;'Y['x];'y} >- 'Z } -->
   sequent['ext]   {'H; u:col_member{'S;union{'X;x.'Y['x]};'y}; 'J >- 'Z }

interactive union_functionality 'H univ[l:l] 'T:
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H >- 'X_1 IN col[l:l]{'T} } -->
   sequent[squash]{'H >- 'X_2 IN col[l:l]{'T} } -->
   sequent[squash]{'H; x:'T; u:col_member{'T;'X_1;'x} >- 'Y_1['x] IN col[l:l]{'S} } -->
   sequent[squash]{'H; x:'T; u:col_member{'T;'X_2;'x} >- 'Y_2['x] IN col[l:l]{'S} } -->
   sequent['ext]{'H >- col_equal{'T;'X_1;'X_2}} -->
   sequent['ext]{'H; x:'T; u:col_member{'T;'X_1;'x} >- col_equal{'S;'Y_1['x];'Y_2['x]}} -->
   sequent['ext]  {'H >- col_equal{'S; union{'X_1;x.'Y_1['x]}; union{'X_2;x.'Y_2['x]}}}


(***===--- other operations ---===***)

(*--- col_union ---*)

declare col_union{'X;x.'C['x]}

prim_rw unfold_col_union : col_union{'X;x.'C['x]} <-->
   ((x: 'X * fst{'C['x]},
    lambda{i. snd{'C[fst{'i}]} snd{'i}}))

(*       [М] H џ X С ”[l] ЭЭЮ
 *       [М] H џ T Type ЭЭЮ
 *       [М] H; x: X џ C[x] С collection[l](T) ЭЭЮ
 *       [ext] H џ Чx:X.C[x] С collection[l](T)
 *)
interactive col_union_wf {| intro [] |} 'H :
   sequent[squash]{'H >- 'X IN univ[l:l] } -->
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H; x:'X >- 'C['x] IN col[l:l]{'T} } -->
   sequent['ext]  {'H >- col_union{'X;x.'C['x]} IN col[l:l]{'T} }

(*           x С Чs:S.C[s] in collection(T)  <==>
 *           Щs:S. (x С C[s]) in collection(T)
 *)
interactive member_col_union {| intro [intro_univ_arg] |} 'H univ[l:l]:
   sequent[squash] {'H; s:'S >- 'C['s] IN col[l:l]{'T} } -->
   sequent['ext]{'H >- (exst s:'S. col_member{'T;'C['s];'x})} -->
   sequent['ext]  {'H >- col_member{'T;col_union{'S;s.'C['s]};'x}}

interactive member_col_union_elim {| elim [elim_univ_arg] |} 'H 'J univ[l:l] :
   sequent[squash] {'H; 'J; s:'S >- 'C['s] IN col[l:l]{'T} } -->
   sequent['ext]   {'H; 'J; w:(exst s:'S. col_member{'T;'C['s];'x}) >- 'Z } -->
   sequent['ext]   {'H; u:col_member{'T;col_union{'S;s.'C['s]};'x}; 'J >- 'Z }

(*       [М] H џ S С ”[l] ЭЭЮ
 *       [М] H џ T Type ЭЭЮ
 *       [М] H; s: S џ C_1[s] С collection[l](T) ЭЭЮ
 *       [М] H; s: S џ C_2[s] С collection[l](T) ЭЭЮ
 *       [ext] H; s: S џ C_1[s] = C_2[s] in collection(T) ЭЭЮ
 *       [ext] H џ Чs:S.C_1[s] = Чs:S.C_2[s] in collection(T)
 *)
interactive col_union_functionality 'H univ[l:l]:
   sequent[squash]{'H >- 'S IN univ[l:l] } -->
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H; s:'S >- 'C_1['s] IN col[l:l]{'T} } -->
   sequent[squash]{'H; s:'S >- 'C_2['s] IN col[l:l]{'T} } -->
   sequent['ext]{'H; s : 'S >- col_equal{'T;'C_1['s];'C_2['s]}} -->
   sequent['ext]  {'H >- col_equal{'T; col_union{'S;s.'C_1['s]}; col_union{'S;s.'C_2['s]}}}



(*--- col_filter ---*)

declare col_filter{'C; x.'P['x]}


prim_rw unfold_col_filter :  col_filter{'C; x.'P['x]} <-->
            ((i:fst{'C} * 'P[snd{'C} 'i],
              lambda{j. snd{'C} fst{'j}}))
(* {x : <I,phi> | P[x]} ==
 *   < i:I * P[phi i],
 *     labbda j. phi j.1>
 *)
interactive_rw reduce_filter : col_filter{('I,'phi); x.'P['x]} <-->
            ((i:'I * 'P['phi 'i],
              lambda{j. 'phi fst{'j}}))

let resource reduce += << col_filter{('I,'phi); x.'P['x]}  >>, reduce_filter

(*      [М] H џ T Type ЭЭЮ
 *      [М] H; x: T џ P[x] С ”[l] ЭЭЮ
 *      [М] H џ C С collection[l](T) ЭЭЮ
 *      [ext] H џ < x:C | P[x]> С collection[l](T)
 *)
interactive col_filter_wf {| intro [] |} 'H :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H; x:'T >- 'P['x] IN univ[l:l] } -->
   sequent[squash]{'H >- 'C IN col[l:l]{'T} } -->
   sequent['ext]  {'H >- col_filter{'C; x.'P['x]} IN col[l:l]{'T} }

(*        x С < x:C | P[x]> <==>
 *        x С C in collection(T)  and P[x]
 *)
interactive member_col_filter {| intro [intro_univ_arg] |} 'H univ[l:l] :
   sequent[squash]{'H; x:'T >- "type"{'P['x]}} -->
   sequent[squash]{'H >- 'C IN col[l:l]{'T} } -->
   sequent['ext]{'H >- col_member{'T;'C;'x}} -->
   sequent['ext]{'H >- 'P['x]} -->
   sequent['ext]  {'H >- col_member{'T;col_filter{'C; x.'P['x]};'x}}

interactive member_col_filter_elim {| elim [elim_univ_arg] |} 'H 'J univ[l:l] :
   sequent[squash]{'H; 'J; x:'T >- "type"{'P['x]}} -->
   sequent[squash]{'H; 'J >- 'C IN col[l:l]{'T} } -->
   sequent['ext]  {'H; w:'P['x]; 'J; v:col_member{'T;'C;'x} >- 'Z } -->
   sequent['ext]  {'H; u:col_member{'T;col_filter{'C; x.'P['x]};'x}; 'J >- 'Z }

(*
 *       [М] H џ T Type ЭЭЮ
 *       [М] H; x: T џ P[x] С ”[l] ЭЭЮ
 *       [М] H џ C_1 С collection[l](T) ЭЭЮ
 *       [М] H џ C_2 С collection[l](T) ЭЭЮ
 *       [ext] H џ C_1 = C_2 in collection(T) ЭЭЮ
 *       [ext] H џ < x:C_1 | P[x]> = < x:C_2 | P[x]> in collection(T)
 *)
interactive col_filter_functionality 'H univ[l:l]:
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H; x:'T >- 'P['x] IN univ[l:l] } -->
   sequent[squash]{'H >- 'C_1 IN col[l:l]{'T} } -->
   sequent[squash]{'H >- 'C_2 IN col[l:l]{'T} } -->
   sequent['ext]{'H >- col_equal{'T;'C_1;'C_2}} -->
   sequent['ext]  {'H >- col_equal{'T; col_filter{'C_1; x.'P['x]}; col_filter{'C_2; x.'P['x]}}}

(*--- col_map ---*)

declare map{'C; x.'f['x]}

prim_rw unfold_map :  map{'C; x.'f['x]} <-->
            ((fst{'C},
              lambda{i. 'f[snd{'C} 'i] }))
(*   < f[x] | x:<I,phi>> ЯЭЭЮ
 *   <I,(«i.f[(phi i)])>
 *)
interactive_rw reduce_map : map{('I,'phi); x.'f['x]} <-->
            (('I,
              lambda{i. 'f['phi 'i]}))

let resource reduce += << map{('I,'phi); x.'f['x]} >>, reduce_map

(*       [М] H џ T Type ЭЭЮ
 *       [М] H џ S Type ЭЭЮ
 *       [М] H; x: T џ f[x] С S ЭЭЮ
 *       [М] H џ C С collection[l](T) ЭЭЮ
 *       [ext] H џ < f[x] | x:C> С collection[l](S)
 *)
interactive map_wf {| intro [] |} 'H 'T:
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H >- "type"{'S}} -->
   sequent[squash]{'H; x:'T >- 'f['x] IN 'S } -->
   sequent[squash]{'H >- 'C IN col[l:l]{'T} } -->
   sequent['ext]  {'H >- map{'C; x.'f['x]} IN col[l:l]{'S} }

(*            y С < f[x] | x:C> in collection(S)  <==>
 *            Щx:T. (x С C) in collection(T) П (y = f[x] in S)
 *)
interactive member_map {| intro [intro_univ_with_args] |} 'H univ[l:l] 'T:
   sequent[squash]{'H; x:'T >- 'f['x] IN 'S } -->
   sequent[squash]{'H >- 'C IN col[l:l]{'T} } -->
   sequent['ext]{'H >- exst x:'T. (col_member{'T;'C;'x} and ('y='f['x] in 'S)) } -->
   sequent['ext]  {'H >- col_member{'S;map{'C; x.'f['x]};'y}}

interactive member_map_elim {| elim [elim_univ_with_args] |} 'H 'J univ[l:l] 'T:
   sequent[squash]{'H; 'J; x:'T >- 'f['x] IN 'S } -->
   sequent[squash]{'H; 'J >- 'C IN col[l:l]{'T} } -->
   sequent['ext]  {'H; 'J;  x:'T; v: col_member{'T;'C;'x}; w: ('y='f['x] in 'S) >- 'Z } -->
   sequent['ext]  {'H; u:col_member{'S;map{'C; x.'f['x]};'y}; 'J >- 'Z }

(*       [М] H џ T Type ЭЭЮ
 *       [М] H; x: T џ f[x] С ”[l] ЭЭЮ
 *       [М] H џ C_1 С collection[l](T) ЭЭЮ
 *       [М] H џ C_2 С collection[l](T) ЭЭЮ
 *       [ext] H џ C_1 = C_2 in collection(T) ЭЭЮ
 *       [ext] H џ < f[x] | x:C_1> = < f[x] | x:C_2> in collection(T)
 *)
interactive map_functionality 'H univ[l:l]:
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H; x:'T >- 'f['x] IN univ[l:l] } -->
   sequent[squash]{'H >- 'C_1 IN col[l:l]{'T} } -->
   sequent[squash]{'H >- 'C_2 IN col[l:l]{'T} } -->
   sequent['ext]{'H >- col_equal{'T;'C_1;'C_2}} -->
   sequent['ext]  {'H >- col_equal{'T; map{'C_1; x.'f['x]}; map{'C_2; x.'f['x]}}}

(*--- isect ---*)

declare "isect"{'S;s.'C['s];'T}

(*  (Цs:S.C[s]) ЯЭЭЮ
 *  < x:НT | (Шs:S. (x С C[s]) in collection(T))>
 *)

prim_rw unfold_isect : "isect"{'S;s.'C['s];'T} <-->
   col_filter{type_col{'T}; x. (all s: 'S. col_member{'T;'C['s];'x})}

(*       [М] H џ T С ”[l] ЭЭЮ
 *       [М] H џ S С ”[l] ЭЭЮ
 *       [М] H; s: S џ C[s] С collection[l](T) ЭЭЮ
 *       [ext] H џ Цs:S.C[s] С collection[l](T)
 *)
interactive isect_wf {| intro [] |} 'H :
   sequent[squash]{'H >- 'T IN univ[l:l] } -->
   sequent[squash]{'H >- 'S IN univ[l:l] } -->
   sequent[squash]{'H; s:'S >- 'C['s] IN col[l:l]{'T} } -->
   sequent['ext]  {'H >- "isect"{'S;s.'C['s];'T} IN col[l:l]{'T} }

(*    x С Цs:S.C[s] in collection(T)  <==>
 *    x С T  and  Шs:S. (x С C[s]) in collection(T)
 *)

interactive member_isect {| intro [intro_univ_arg] |} 'H univ[l:l]:
   sequent[squash]{'H >- 'T IN univ[l:l] } -->
   sequent[squash]{'H >- 'S IN univ[l:l] } -->
   sequent[squash]{'H; s:'S >- 'C['s] IN col[l:l]{'T} } -->
   sequent['ext]  {'H; s:'S >-  col_member{'T;'C['s];'x}} -->
   sequent['ext]  {'H >-  'x IN 'T } -->
   sequent['ext]  {'H >- col_member{'T;."isect"{'S;s.'C['s];'T};'x}}

interactive member_isect_elim {| elim [elim_univ_arg] |} 'H 'J univ[l:l] :
   sequent[squash]{'H; 'J >- 'T IN univ[l:l] } -->
   sequent[squash]{'H; 'J >- 'S IN univ[l:l] } -->
   sequent[squash]{'H; 'J; s:'S >- 'C['s] IN col[l:l]{'T} } -->
   sequent['ext]   {'H; w:(all s:'S. col_member{'T;'C['s];'x}); 'J; v: 'x IN 'T >- 'Z } -->
   sequent['ext]   {'H; u:col_member{'T;."isect"{'S;s.'C['s];'T};'x}; 'J >- 'Z }

(*       [М] H џ T С ”[l] ЭЭЮ
 *       [М] H џ S С ”[l] ЭЭЮ
 *       [М] H; s: S џ C_1[s] С collection[l](T) ЭЭЮ
 *       [М] H; s: S џ C_2[s] С collection[l](T) ЭЭЮ
 *       [ext] H; s: S џ C_1[s] = C_2[s] in collection(T) ЭЭЮ
 *       [ext] H џ Цs:S.C_1[s] = Цs:S.C_2[s] in collection(T)
 *)
interactive isect_functionality 'H univ[l:l]:
   sequent[squash]{'H >- 'T IN univ[l:l] } -->
   sequent[squash]{'H >- 'S IN univ[l:l] } -->
   sequent[squash]{'H; s:'S >- 'C_1['s] IN col[l:l]{'T} } -->
   sequent[squash]{'H; s:'S >- 'C_2['s] IN col[l:l]{'T} } -->
   sequent['ext]{'H; s : 'S >- col_equal{'T;'C_1['s];'C_2['s]}} -->
   sequent['ext]  {'H >- col_equal{'T; ."isect"{'S;s.'C_1['s];'T}; ."isect"{'S;s.'C_2['s];'T}}}



(*--- none ---*)

declare none

(*       <> ЯЭЭЮ <Void,(«x.x)>
 *)
prim_rw unfold_none : none <--> ((void,lambda{x.'x}))

(*     [М] H џ T Type ЭЭЮ
       [ext] H џ <> С collection[l](T)
 *)
interactive none_wf {| intro [] |} 'H :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent['ext]  {'H >- none IN col[l:l]{'T} }

(*        y С <> in collection(T)   <==>   False
 *)

interactive member_none {| intro [] |} 'H :
   sequent[squash]{'H >- "false"} -->
   sequent['ext]  {'H >- col_member{'T; none; 'y}}

interactive member_none_elim {| elim [] |} 'H 'J :
   sequent['ext]  {'H; u:col_member{'T; none; 'y}; 'J >- 'Z}

(*--- add ---*)

declare add{'C_1;'C_2}

(*        unfold_add (C_1 + C_2) ЯЭЭЮ
 *        (Чb:Bool.(if b then C_1 else C_2))
 *)
prim_rw unfold_add : add{'C_1;'C_2} <--> col_union{bool; b. ifthenelse{'b;'C_1;'C_2}}

interactive add_wf {| intro [] |} 'H :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H >- 'C_1 IN col[l:l]{'T} } -->
   sequent[squash]{'H >- 'C_2 IN col[l:l]{'T} } -->
   sequent['ext]  {'H >- add{'C_1;'C_2} IN col[l:l]{'T} }

(*           x С (C_1 + C_2) in collection(T)  <==>
 *           x С C_1 in collection(T) or x С C_2 in collection(T)
 *)
interactive member_add1 {| intro [SelectOption 1; intro_univ_arg] |} 'H  univ[l:l] :
   sequent[squash] {'H >- 'C_1 IN col[l:l]{'T} } -->
   sequent[squash] {'H >- 'C_2 IN col[l:l]{'T} } -->
   sequent['ext]   {'H >- col_member{'T; 'C_1 ; 'x}} -->
   sequent['ext]   {'H >- col_member{'T; add{'C_1;'C_2} ; 'x}}

interactive member_add2 {| intro [SelectOption 2; intro_univ_arg] |} 'H  univ[l:l] :
   sequent[squash] {'H >- 'C_1 IN col[l:l]{'T} } -->
   sequent[squash] {'H >- 'C_2 IN col[l:l]{'T} } -->
   sequent['ext]   {'H >- col_member{'T; 'C_2 ; 'x}} -->
   sequent['ext]   {'H >- col_member{'T; add{'C_1;'C_2} ; 'x}}

interactive member_add_elim {| elim [elim_univ_arg] |} 'H 'J univ[l:l] :
   sequent[squash] {'H; 'J >- 'C_1 IN col[l:l]{'T} } -->
   sequent[squash] {'H; 'J >- 'C_2 IN col[l:l]{'T} } -->
   sequent['ext]   {'H; 'J; v: col_member{'T; 'C_1 ; 'x} >- 'Z} -->
   sequent['ext]   {'H; 'J; v: col_member{'T; 'C_2 ; 'x} >- 'Z} -->
   sequent['ext]   {'H; u:col_member{'T; add{'C_1;'C_2}; 'x}; 'J >- 'Z}


(********************** Simplification lemmas **********************)

(* < x:<> | P[x]> = <> in collection(T)  *)
interactive filter_none 'H univ[l:l] :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H; x:'T >- 'P['x] IN univ[l:l] } -->
   sequent ['ext] {'H >- col_equal{'T;col_filter{none;x.'P['x]};none}}

(*  < x:(if b then C else D) | P[x]> =
 *  (if b then < x:C | P[x]> else < x:D | P[x]>) in collection(T)
 *)
interactive filter_if 'H univ[l:l] :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H; x:'T >- 'P['x] IN univ[l:l] } -->
   sequent[squash]{'H >- 'C IN col[l:l]{'T} } -->
   sequent[squash]{'H >- 'D IN col[l:l]{'T} } -->
   sequent[squash]{'H >- 'b IN bool } -->
   sequent ['ext] {'H >- col_equal{'T; col_filter{ifthenelse{'b;'C;'D}; x.'P['x]};
                                       ifthenelse{'b; col_filter{'C;x.'P['x]}; col_filter{'D;x.'P['x]}} }}

(*   < x:(c + d) | P[x]> =
 *   (< x:c | P[x]> + < x:d | P[x]>) in collection(T)
 *)
interactive filter_add 'H univ[l:l] :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H; x:'T >- 'P['x] IN univ[l:l] } -->
   sequent[squash]{'H >- 'c IN col[l:l]{'T} } -->
   sequent[squash]{'H >- 'd IN col[l:l]{'T} } -->
   sequent ['ext] {'H >- col_equal{'T; col_filter{add{'c;'d}; x.'P['x]};
                                       add{ col_filter{'c;x.'P['x]}; col_filter{'d;x.'P['x]}} }}

(*   < x:(Чs:S.c[s]) | P[x]> =
 *   Чs:S.< x:c[s] | P[x]> in collection(T)
 *)
interactive filter_union 'H univ[l:l] :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H >- 'S IN univ[l:l] } -->
   sequent[squash]{'H; x:'T >- 'P['x] IN univ[l:l] } -->
   sequent[squash]{'H; s:'S >- 'c['s] IN col[l:l]{'T} } -->
   sequent ['ext] {'H >- col_equal{'T; col_filter{col_union{'S;s.'c['s]}; x.'P['x]};
                                       col_union{'S; s.col_filter{'c['s];x.'P['x]}} }}

(*   Чs:S.(c[s] + d[s]) =
 *    ((Чs:S.c[s]) + (Чs:S.d[s])) in collection(T)
 *)
interactive union_add  'H univ[l:l] :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H >- 'S IN univ[l:l] } -->
   sequent[squash]{'H; s:'S >- 'c['s] IN col[l:l]{'T} } -->
   sequent[squash]{'H; s:'S >- 'd['s] IN col[l:l]{'T} } -->
   sequent ['ext] {'H >- col_equal{'T; col_union{'S; s.add{'c['s];'d['s]}};
                                       add{ col_union{'S; s.'c['s]}; col_union{'S; s.'d['s]}}  }}

(*     Чs:S.c = c in collection(T)
 *)
interactive union_const  'H univ[l:l] :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H >- 'S IN univ[l:l] } -->
   sequent[squash]{'H >- 'c IN col[l:l]{'T} } -->
   sequent['ext]  {'H >- 'S} -->
   sequent['ext]  {'H >- col_equal{'T; col_union{'S; s.'c}; 'c}}

(*    Чs:S.(if b then C[s] else D[s]) =
 *    (if b then (Чs:S.C[s]) else (Чs:S.D[s])) in collection(T)
 *)
interactive union_if  'H univ[l:l] :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H >- 'S IN univ[l:l] } -->
   sequent[squash]{'H; s:'S >- 'C['s] IN col[l:l]{'T} } -->
   sequent[squash]{'H; s:'S >- 'D['s] IN col[l:l]{'T} } -->
   sequent[squash]{'H >- 'b IN bool } -->
   sequent['ext]  {'H >- col_equal{'T; col_union{'S; s. ifthenelse{'b; 'C['s]; 'D['s]}};
                                       ifthenelse{'b; col_union{'S; s. 'C['s]};  col_union{'S; s. 'D['s]}} }}

(*    (c + d) = (d + c) in collection(T)
 *)
interactive add_com 'H univ[l:l] :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H >- 'c IN col[l:l]{'T} } -->
   sequent[squash]{'H >- 'd IN col[l:l]{'T} } -->
   sequent ['ext] {'H >- col_equal{'T;add{'c;'d};add{'d;'c}}}

(*   (c + <>) = c in collection(T)
 *)
interactive add_none 'H univ[l:l]:
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H >- 'c IN col[l:l]{'T} } -->
   sequent ['ext] {'H >- col_equal{'T;add{'c;none};'c}}

(*   (c + <>) = c in collection(T)
 *)
interactive none_add 'H univ[l:l]:
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H >- 'c IN col[l:l]{'T} } -->
   sequent ['ext] {'H >- col_equal{'T;add{'c;none};'c}}

(*    (c + c) = c in collection(T)
 *)
interactive add_idempotent 'H univ[l:l] :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H >- 'c IN col[l:l]{'T} } -->
   sequent ['ext] {'H >- col_equal{'T;add{'c;'c};'c}}

(*  <(if b then x else y)> = (if b then <x> else <y>) in collection(T)
 *)
interactive singlenton_if  'H univ[l:l] :
   sequent[squash]{'H >- 'x IN 'T } -->
   sequent[squash]{'H >- 'y IN 'T } -->
   sequent[squash]{'H >- 'b IN bool } -->
   sequent['ext]  {'H >- col_equal{'T; singlenton{ ifthenelse{'b;'x;'y}};
                                       ifthenelse{'b; singlenton{'x}; singlenton{'y}} }}



(********************** dforms **********************)

declare display_col{'T}

dform col_df : except_mode[src] :: Col[l:l]{'T} =
   `"Collection[" slot[l:l] `"](" slot{'T} `")"

dform col_member_df : except_mode[src] :: Col_member[l:l]{'T;'C;'x} =
   ('x IN 'C) `" in " Col[l:l]{'T}

dform col_equal_df : except_mode[src] :: col_equal{'T;'c_1;'c_2} =
   equal{display_col{'T};'c_1;'c_2}

dform display_col_df : display_col{'T} =
   `"collection{" slot{'T} `"}"

dform type_col_df : except_mode[src] :: type_col{'T} = downarrow slot{'T}
dform col_type_df : except_mode[src] :: col_type{'C;'T} = uparrow slot{'C}

dform singlenton_df : except_mode[src] :: singlenton{'x} = `"<" slot{'x} `">"

dform union_df : except_mode[src] :: parens :: "prec"[prec_tunion] :: union{'X; x. 'Y} =
   cup slot{'x} Nuprl_font!member slot{'X} `"." slot{'Y}

dform col_union_df : except_mode[src] :: parens :: "prec"[prec_tunion] :: col_union{'X; x. 'C} =
   cup slot{'x} `":" slot{'X} `"." slot{'C}

dform map_df : except_mode[src] :: map{'C; x.'f} =
      pushm[3] `"< " slot{'f} `" | " bvar{'x} `":" slot{'C} `">" popm

dform col_filter_df : except_mode[src] :: col_filter{'C; x.'P} =
      pushm[3] `"< " bvar{'x} `":" slot{'C} `" | " slot{'P} `">" popm

dform isect_df : except_mode[src] :: parens :: "prec"[prec_tunion] :: "isect"{'S; s. 'C;'T} =
   cap slot{'s} `":" slot{'S} `"." slot{'C}

dform none_df : except_mode[src] :: none = `"<>"

dform add_df : except_mode[src] :: parens :: "prec"[prec_add] :: "add"{'a; 'b} =
   slot["le"]{'a} `" + " slot["lt"]{'b}

