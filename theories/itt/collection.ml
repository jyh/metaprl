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
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Var
open Tacticals
open Conversionals
open Sequent
open Base_auto_tactic
open Base_dtactic
open Itt_logic
open Itt_struct

open Itt_tunion
open Itt_int


open Tacticals
open Sequent


include Mptop

open Printf
open Mp_debug
open Dag
open Imp_dag

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError
open Mp_resource

open Tacticals
open Sequent
open Mptop


(*===--- unhide ---===*)

prim unhide_with_type 'H 'J :
 sequent[squash] { 'H; x:'A; 'J >- "type"{'T}} -->
 sequent['ext] { 'H; x:hide{'A}; 'J >- "type"{'T}} =
 it 

prim unhide_with_equal 'H 'J :
 sequent[squash] { 'H; x:'A; 'J >- 'a='b in 'T} -->
 sequent['ext] { 'H; x:hide{'A}; 'J >- 'a='b in 'T} =
 it 

let unhide_with_typeT i p =
    let i', j = hyp_indices p i in
         unhide_with_type i' j p
let unhide_with_equalT i p =
    let i', j = hyp_indices p i in
         unhide_with_equal i' j p                                                     
let unhideT i = unhide_with_typeT i orelseT unhide_with_equalT i
                                                       
(*===--- MemCD ---===*)

let memcdT = rw unfold_member 0 thenT dT 0 thenT tryT (rw fold_member 0) 
let mem_term = << member{'T;'t} >>
let d_resource = Mp_resource.improve d_resource (mem_term, wrap_intro (keepingLabelT memcdT))


(*===--- auto... ---===*)
                    
let univTypeT univ = univTypeT univ thenT rwh fold_member 0

let univTypeComplT  = completeT ((function p -> univTypeT (get_univ_arg p) p) thenT autoT)
                        
                        
let auto_resource =
   Mp_resource.improve auto_resource (**)
      { auto_name = "univTypeT";
        auto_prec = logic_prec;
        auto_tac = auto_wrap univTypeComplT
      }

                        
let memberTypeT a = equalTypeT a a thenT rwh fold_member 0 thenT  tryT (completeT autoT)

let equalRefT a =  rwh unfold_member 0 thenT equalRefT a
                       
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
            if is_bind_term t1 then
               t1
            else
               raise (RefineError ("substT", StringTermError ("need a \"bind\" term: ", t1)))
      with
         RefineError _ ->
            let x = get_opt_var_arg "z" p in
               mk_bind_term x (var_subst (concl p) a x)
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
            if is_bind_term b then
               b
            else
               raise (RefineError ("substT", StringTermError ("need a \"bind\" term: ", b)))
      with
         RefineError _ ->
            mk_bind_term z (var_subst t1 a z)
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
                    
interactive cutMember0 'H member{'S;'s} 'z bind{x.'T['x]}:
   sequent [squash] { 'H >- member{'S;'s} } --> 
   sequent ['ext] { 'H; z: 'S >- 'T['z] } -->
   sequent ['ext] { 'H >- 'T['s] } 
  

let cutMemberT ss  p =
   let _, s = dest_member ss in
   let x=  get_opt_var_arg (if is_var_term s then dest_var s else  "z") p in
   let bind =
      try
         let b = get_with_arg p in
            if is_bind_term b then
               b
            else
               raise (RefineError ("cutMemberT", StringTermError ("need a \"bind\" term: ", b)))
      with
         RefineError _ ->
            mk_bind_term x (var_subst (concl p) s x) 
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
      
interactive col_wf 'H :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent['ext]{'H >- "type"{col[l:l]{'T}}}

let tactic p =  col_wf (Sequent.hyp_count_addr p) p
let term = <<   "type"{col[l:l]{'T}}   >>
let d_resource = Mp_resource.improve d_resource (term, wrap_intro tactic)

(* [М] H џ T Type ЭЭЮ
 * [ext] H џ collection[l](T) Type
 *)  
interactive col_wf2 'H :
   sequent[squash]{'H >- member{univ[l ':l];'T}} -->
   sequent['ext]{'H >- member{univ[l ':l]; col[l:l]{'T}}}

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
let cutColT c = cutMemberT  (mk_member_term <<col[l:l]{'T}>> c) thenLT [tryT (completeT autoT);  d_colT (-1) thenT rwh reduceC 0]
       
let cutColS c = cutMemberT  (mk_member_term <<col[l:l]{'S}>> c) thenLT [tryT (completeT autoT);  d_colT (-1) thenT rwh reduceC 0]
       
(*--- col_member ---*) 

declare col_member{'T;'C;'x}

prim_rw unfold_col_member : col_member{'T;'C;'x} <-->
             exst i:fst{'C} . (snd{'C} 'i = 'x in 'T)
(*  (x С <I,phi>) in collection(T) ЯЭЭЮ
 *  (Щi:I. (phi i = x in T))
 *)  
interactive_rw reduce_member : col_member{'T;('I,'phi);'x} <-->
     (exst i:'I . ('phi 'i = 'x in 'T))

let reduce_info =
   [<<   col_member{'T;('I,'phi);'x} >>, reduce_member]
let reduce_resource = add_reduce_info reduce_resource reduce_info

(*      [М] H џ T С ”[l] ЭЭЮ
 *      [М] H џ x С T ЭЭЮ
 *      [М] H џ C С collection[l](T) ЭЭЮ
 *      [ext] H џ (x С C) in collection(T) С ”[l]
 *)                         
interactive col_member_univ 'H:
   sequent[squash]{'H >- member{univ[l:l];'T}} -->
   sequent[squash]{'H >- member{'T;'x}} -->
   sequent[squash]{'H >- member{col[l:l]{'T};'C}} -->
   sequent['ext]{'H >- member{univ[l:l];col_member{'T;'C;'x}}}

let tactic p =  col_member_univ (Sequent.hyp_count_addr p) p
let term = <<   member{univ[l:l];col_member{'T;'C;'x}}   >>
let d_resource = Mp_resource.improve d_resource (term, wrap_intro tactic)


(*      [М] H џ x С T ЭЭЮ
 *      [М] H џ C С collection[l](T) ЭЭЮ
 *      [ext] H џ (x С C) in collection(T) Type
*)                    
interactive col_member_wf 'H univ[l:l]:
   sequent[squash]{'H >- member{'T;'x}} -->
   sequent[squash]{'H >- member{col[l:l]{'T};'C}} -->
   sequent['ext]{'H >- "type"{col_member{'T;'C;'x}}}

let tactic p =  col_member_wf (Sequent.hyp_count_addr p) (get_univ_arg p) p
let term = <<   "type"{col_member{'T;'C;'x}}   >>
let d_resource = Mp_resource.improve d_resource (term, wrap_intro tactic)

(*      [М] H џ x С C in collection(T) ЭЭЮ
 *      [ext] H џ x С T
 *)
interactive mem_col_mem 'H 'C:
   sequent[squash] {'H >- col_member{'T;'C;'x}} -->
   sequent['ext]   {'H >- member{'T;'x}}

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
interactive col_equal_univ 'H :
   sequent[squash]{'H >- member{univ[l:l];'T}} -->
   sequent[squash]{'H >- member{col[l:l]{'T};'C_1}} -->
   sequent[squash]{'H >- member{col[l:l]{'T};'C_2}} -->
   sequent['ext]{'H >- member{univ[l:l]; col_equal{'T;'C_1;'C_2} }}

let tactic p =  col_equal_univ (Sequent.hyp_count_addr p) p
let term = << member{univ[l:l]; col_equal{'T;'C_1;'C_2} }     >>
let d_resource = Mp_resource.improve d_resource (term, wrap_intro tactic)

(*        [М] H џ T Type ЭЭЮ
 *        [М] H џ C_1 С collection[l](T) ЭЭЮ
 *        [М] H џ C_2 С collection[l](T) ЭЭЮ
 *        [ext] H џ (C_1 = C_2 in collection(T)) Type
 *)                   
interactive col_equal_wf 'H univ[l:l] :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H >- member{col[l:l]{'T};'C_1}} -->
   sequent[squash]{'H >- member{col[l:l]{'T};'C_2}} -->
   sequent['ext]{'H >- "type"{ col_equal{'T;'C_1;'C_2} }}

let tactic p =  col_equal_wf (Sequent.hyp_count_addr p) (get_univ_arg p) p
let term = <<   "type"{col_equal{'T;'C_1;'C_2}}   >>
let d_resource = Mp_resource.improve d_resource (term, wrap_intro tactic)
                    
(*       [М] H џ T Type ЭЭЮ
 *       [М] H џ C С collection[l](T) ЭЭЮ
 *       [ext] H џ C = C in collection(T)
 *)                   
interactive col_equal_reflexivity  'H univ[l:l] :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]  {'H >-  member{col[l:l]{'T};'C} } -->
   sequent['ext]  {'H >-  col_equal{'T;'C;'C} }

let tactic p =  col_equal_reflexivity (Sequent.hyp_count_addr p) (get_univ_arg p) p
let term = <<   col_equal{'T;'C;'C}   >>
let d_resource = Mp_resource.improve d_resource (term, wrap_intro tactic)

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
   sequent[squash]  {'H >-  member{col[l:l]{'T};'A} } -->
   sequent[squash]  {'H >-  member{col[l:l]{'T};'C} } -->
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
   sequent[squash]  {'H >-  member{col[l:l]{'T};'A} } -->
   sequent[squash]  {'H >-  member{col[l:l]{'T};'B} } -->
   sequent['ext]    {'H >-  col_equal{'T;'A;'B} }  -->
   sequent['ext]    {'H >-  col_equal{'T;'B;'A} }

                    
(*--- Col --*)

declare Col[l:l]{'T}


prim_rw unfold_Col :  Col[l:l]{'T} <--> (quot x,y: col[l:l]{'T} // col_equal{'T;'x;'y})
let fold_Col = makeFoldC <<Col[l:l]{'T}>> unfold_Col

interactive _Col_wf 'H :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent['ext]{'H >- "type"{Col[l:l]{'T}}}
(* rwh unfold_Col 0 thenT atT <<univ[l:l]>> autoT*)

let tactic p =  _Col_wf (Sequent.hyp_count_addr p) p
let term = <<   "type"{Col[l:l]{'T}}   >>
let d_resource = Mp_resource.improve d_resource (term, wrap_intro tactic)
      
interactive _Col_wf2 'H :
   sequent[squash]{'H >- member{univ[l ':l];'T}} -->
   sequent['ext]{'H >- member{univ[l ':l]; Col[l:l]{'T}}}

interactive member_Col 'H :
  sequent[squash]{'H >- "type"{'T}} -->
  sequent[squash]{'H >- member{col[l:l]{'T};'C}} -->
  sequent['ext]{'H >- member{Col[l:l]{'T};'C}}

let member_ColT p =  member_Col (Sequent.hyp_count_addr p) p
   
(*--- Col_member ---*)

declare Col_member[l:l]{'T;'C;'x}

prim_rw unfold_Col_member : Col_member[l:l]{'T;'C;'x} <-->
   (exst c:col[l:l]{'T} . (('c='C in Col[l:l]{'T}) and col_member{'T;'c;'x}))
 
interactive _Col_member_wf 'H univ[l:l] :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H >- member{'T;'x}} -->
   sequent[squash]{'H >- member{Col[l:l]{'T};'C}} -->
   sequent['ext]{'H >- "type"{Col_member[l:l]{'T;'C;'x}}}

let tactic p =  _Col_member_wf (Sequent.hyp_count_addr p) (get_univ_arg p) p
let term = <<   "type"{Col_member[l:l]{'T;'C;'x}}   >>
let d_resource = Mp_resource.improve d_resource (term, wrap_intro tactic)                    

(***===--- connection with types ---===***)

(*--- type_col ---*)

declare type_col{'T}

prim_rw unfold_type_col : type_col{'T} <--> (('T,lambda{x.'x}))

(*  НT ЯЭЭЮ <T,(«x.x)>
 *)
interactive type_col_wf 'H :
   sequent[squash] {'H >- member{univ[l:l];'T}} -->
   sequent['ext]   {'H >- member{col[l:l]{'T}; type_col{'T}}}
      
let tactic p =  type_col_wf (Sequent.hyp_count_addr p) p
let term = <<   member{col[l:l]{'T}; type_col{'T}}   >>
let d_resource = Mp_resource.improve d_resource (term, wrap_intro tactic)

(*
 *       x С T <--> x С НT in collection(T)
 *       
 *)
interactive member_type_col 'H :
   sequent[squash] {'H >- member{'T;'x}} -->
   sequent['ext]  {'H >- col_member{'T;type_col{'T};'x}}

interactive member_type_col_elim 'H 'J : 
   sequent['ext]   {'H; 'J; w:member{'T;'x} >- 'Z } -->
   sequent['ext]   {'H; u:col_member{'T;type_col{'T};'x}; 'J >- 'Z }

let tactic i p =
   if i = 0 then
      member_type_col  (Sequent.hyp_count_addr p) p
   else
      let i', j = hyp_indices p i in
         member_type_col_elim  i' j p
let term = << col_member{'T;type_col{'T};'x}  >>
let d_resource = Mp_resource.improve d_resource (term,  tactic)
                                          
(*--- col_type ---*)
declare col_type{'C;'T}

(* ОC ЯЭЭЮ { x:T | (x С C) in collection(T)}
 *)  
prim_rw unfold_col_type : col_type{'C;'T} <--> ({ x:'T | col_member{'T;'C;'x} })

(*       [М] H џ T Type ЭЭЮ
 *       [ext] H џ C С collection[l](T) ЭЭЮ
 *       [ext] H џ ОC Type
 *)      
interactive col_type_wf 'H univ[l:l] :
   sequent[squash] {'H >- "type"{'T}} -->
   sequent['ext]   {'H >- member{col[l:l]{'T}; 'C}} -->
   sequent['ext]   {'H >-"type"{col_type{'C;'T}}}
      
let tactic p =  col_type_wf (Sequent.hyp_count_addr p) (get_univ_arg p) p
let term = <<   member{col[l:l]{'T}; col_type{'C;'T}}   >>
let d_resource = Mp_resource.improve d_resource (term, wrap_intro tactic)

                    
(***===--- basic operations ---===***)
                    
(*--- singleton ---*)

declare singlenton{'x}

(* <x> ЯЭЭЮ <Unit,(«i.x)> *)      
prim_rw unfold_singlenton :  singlenton{'x} <--> ((unit, lambda{i.'x}))

(*       [М] H џ x С T ЭЭЮ
 *       [ext] H џ <x> С collection[l](T)
 *)
interactive  singlenton_wf 'H :
   sequent[squash]{'H >- member{'T;'x}} -->
   sequent['ext]  {'H >- member{col[l:l]{'T}; singlenton{'x}}}

let tactic p =  singlenton_wf (Sequent.hyp_count_addr p) p
let term = <<   member{col[l:l]{'T}; singlenton{'x}}    >>
let d_resource = Mp_resource.improve d_resource (term, wrap_intro tactic)

(*       y С <x> in collection(T)  <==>  x = y in T
 *)
interactive member_singlenton 'H :
   sequent[squash]{'H >- equal{'T;'x;'y}} -->
   sequent['ext]  {'H >- col_member{'T; singlenton{'x}; 'y}}
      
interactive member_singlenton_elim 'H 'J :
   sequent['ext]{'H; 'J; v:equal{'T;'x;'y} >- 'Z} -->
   sequent['ext]  {'H; u:col_member{'T; singlenton{'x}; 'y}; 'J >- 'Z}

let tactic i p =
   if i = 0 then
      member_singlenton (Sequent.hyp_count_addr p) p
   else
      let i', j = hyp_indices p i in
         member_singlenton_elim  i' j   p
let term = << col_member{'T;singlenton{'x};'y}   >>
let d_resource = Mp_resource.improve d_resource (term,  tactic)

                    
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

let reduce_info =
   [<<  union{('I,'phi); x.('J['x],'psi['x])} >>, reduce_union]
let reduce_resource = add_reduce_info reduce_resource reduce_info
   
(*        [М] H џ T Type ЭЭЮ
 *        [М] H џ S Type ЭЭЮ
 *        [М] H џ X С collection[l](T) ЭЭЮ
 *        [М] H; x: T; u: x С X in collection(T) џ Y[x] С collection[l](S) ЭЭЮ
 *        [ext] H џ ЧxСX.Y[x] С collection[l](S)
 *)         
interactive union_wf 'H 'T:
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H >- "type"{'S}} -->
   sequent[squash]{'H >- member{col[l:l]{'T};'X}} -->
   sequent[squash]{'H; x:'T; u:col_member{'T;'X;'x} >- member{col[l:l]{'S};'Y['x]}} -->
   sequent['ext]  {'H >- member{col[l:l]{'S};union{'X;x.'Y['x]}}}

let tactic p =  union_wf (Sequent.hyp_count_addr p) (get_with_arg p) p
let term = <<   member{col[l:l]{'T};union{'X;x.'Y['x]}}   >>
let d_resource = Mp_resource.improve d_resource (term, wrap_intro tactic)

(* y С ЧxСX.Y[x] in collection(S) <==>
 * Щx:T. (x С X) in collection(T) П (y С Y[x]) in collection(S)
 *)
                    
interactive member_union 'H univ[l:l] member{'T;'x} :
   sequent[squash]{'H >- member{col[l:l]{'T};'X}} -->
   sequent[squash]{'H; x:'T; u:col_member{'T;'X;'x} >- member{col[l:l]{'S};'Y['x]}} -->
   sequent['ext] {'H >- col_member{'T;'X;'x} } -->
   sequent['ext] {'H >- col_member{'S;'Y['x];'y}} -->
   sequent['ext] {'H >- col_member{'S;union{'X;x.'Y['x]};'y}}

interactive member_union_elim 'H 'J univ[l:l] 'T: 
   sequent[squash]{'H; 'J >- member{col[l:l]{'T};'X}} -->
   sequent[squash]{'H; 'J; x:'T; u:col_member{'T;'X;'x} >- member{col[l:l]{'S};'Y['x]}} -->
   sequent['ext]   {'H; 'J; x:'T; v:col_member{'T;'X;'x}; u: col_member{'S;'Y['x];'y} >- 'Z } -->
   sequent['ext]   {'H; u:col_member{'S;union{'X;x.'Y['x]};'y}; 'J >- 'Z }

let tactic i p =
   if i = 0 then
      member_union  (Sequent.hyp_count_addr p) (get_univ_arg p)  (get_with_arg p) p
   else
      let i', j = hyp_indices p i in
         member_union_elim  i' j  (get_univ_arg p)  (get_with_arg p)  p
let term = << col_member{'T;union{'X;s.'Y['x]};'y}  >>
let d_resource = Mp_resource.improve d_resource (term,  tactic)

                    
interactive union_functionality 'H univ[l:l] 'T:
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H >- member{col[l:l]{'T};'X_1}} -->
   sequent[squash]{'H >- member{col[l:l]{'T};'X_2}} -->
   sequent[squash]{'H; x:'T; u:col_member{'T;'X_1;'x} >- member{col[l:l]{'S};'Y_1['x]}} -->
   sequent[squash]{'H; x:'T; u:col_member{'T;'X_2;'x} >- member{col[l:l]{'S};'Y_2['x]}} -->
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
interactive col_union_wf 'H :
   sequent[squash]{'H >- member{univ[l:l];'X}} -->
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H; x:'X >- member{col[l:l]{'T};'C['x]}} -->
   sequent['ext]  {'H >- member{col[l:l]{'T};col_union{'X;x.'C['x]}}}

let tactic p =  col_union_wf (Sequent.hyp_count_addr p) p
let term = <<   member{col[l:l]{'T};col_union{'X;x.'C['x]}}   >>
let d_resource = Mp_resource.improve d_resource (term, wrap_intro tactic)

(*           x С Чs:S.C[s] in collection(T)  <==>
 *           Щs:S. (x С C[s]) in collection(T)
 *)             
interactive member_col_union 'H univ[l:l]:
   sequent[squash] {'H; s:'S >- member{col[l:l]{'T};'C['s]}} -->
   sequent['ext]{'H >- (exst s:'S. col_member{'T;'C['s];'x})} -->
   sequent['ext]  {'H >- col_member{'T;col_union{'S;s.'C['s]};'x}}

interactive member_col_union_elim 'H 'J univ[l:l] : 
   sequent[squash] {'H; 'J; s:'S >- member{col[l:l]{'T};'C['s]}} -->
   sequent['ext]   {'H; 'J; w:(exst s:'S. col_member{'T;'C['s];'x}) >- 'Z } -->
   sequent['ext]   {'H; u:col_member{'T;col_union{'S;s.'C['s]};'x}; 'J >- 'Z }

let tactic i p =
   if i = 0 then
      member_col_union  (Sequent.hyp_count_addr p) (get_univ_arg p) p
   else
      let i', j = hyp_indices p i in
         member_col_union_elim  i' j  (get_univ_arg p)  p
let term = << col_member{'T;col_union{'S;s.'C['s]};'x}  >>
let d_resource = Mp_resource.improve d_resource (term,  tactic)

(*       [М] H џ S С ”[l] ЭЭЮ
 *       [М] H џ T Type ЭЭЮ
 *       [М] H; s: S џ C_1[s] С collection[l](T) ЭЭЮ
 *       [М] H; s: S џ C_2[s] С collection[l](T) ЭЭЮ
 *       [ext] H; s: S џ C_1[s] = C_2[s] in collection(T) ЭЭЮ
 *       [ext] H џ Чs:S.C_1[s] = Чs:S.C_2[s] in collection(T)
 *)                   
interactive col_union_functionality 'H univ[l:l]:
   sequent[squash]{'H >- member{univ[l:l];'S}} -->
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H; s:'S >- member{col[l:l]{'T};'C_1['s]}} -->
   sequent[squash]{'H; s:'S >- member{col[l:l]{'T};'C_2['s]}} -->
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

let reduce_info =
   [<<    col_filter{('I,'phi); x.'P['x]}  >>, reduce_filter]
let reduce_resource = add_reduce_info reduce_resource reduce_info
  

(*      [М] H џ T Type ЭЭЮ
 *      [М] H; x: T џ P[x] С ”[l] ЭЭЮ
 *      [М] H џ C С collection[l](T) ЭЭЮ
 *      [ext] H џ < x:C | P[x]> С collection[l](T)
 *)     
interactive col_filter_wf 'H :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H; x:'T >- member{univ[l:l];'P['x]}} -->
   sequent[squash]{'H >- member{col[l:l]{'T};'C}} -->
   sequent['ext]  {'H >- member{col[l:l]{'T}; col_filter{'C; x.'P['x]}}}

let tactic p =  col_filter_wf (Sequent.hyp_count_addr p) p
let term = <<   member{col[l:l]{'T}; col_filter{'C; x.'P['x]}}    >>
let d_resource = Mp_resource.improve d_resource (term, wrap_intro tactic)

(*        x С < x:C | P[x]> <==>
 *        x С C in collection(T)  and P[x]
 *)       
interactive member_col_filter 'H univ[l:l] :
   sequent[squash]{'H; x:'T >- "type"{'P['x]}} -->
   sequent[squash]{'H >- member{col[l:l]{'T};'C}} -->
   sequent['ext]{'H >- col_member{'T;'C;'x}} -->
   sequent['ext]{'H >- 'P['x]} -->
   sequent['ext]  {'H >- col_member{'T;col_filter{'C; x.'P['x]};'x}}

interactive member_col_filter_elim 'H 'J univ[l:l] :
   sequent[squash]{'H; 'J; x:'T >- "type"{'P['x]}} -->
   sequent[squash]{'H; 'J >- member{col[l:l]{'T};'C}} -->
   sequent['ext]  {'H; w:'P['x]; 'J; v:col_member{'T;'C;'x} >- 'Z } -->
   sequent['ext]  {'H; u:col_member{'T;col_filter{'C; x.'P['x]};'x}; 'J >- 'Z }

let tactic i p =
   if i = 0 then
      member_col_filter  (Sequent.hyp_count_addr p) (get_univ_arg p) p
   else
      let i', j = hyp_indices p i in
         member_col_filter_elim  i' j  (get_univ_arg p)  p
let term = << col_member{'T;col_filter{'C; x.'P['x]};'x}   >>
let d_resource = Mp_resource.improve d_resource (term,  tactic)

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
   sequent[squash]{'H; x:'T >- member{univ[l:l];'P['x]}} -->
   sequent[squash]{'H >- member{col[l:l]{'T};'C_1}} -->
   sequent[squash]{'H >- member{col[l:l]{'T};'C_2}} -->
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

let reduce_info =
   [<<    map{('I,'phi); x.'f['x]}  >>, reduce_map]
let reduce_resource = add_reduce_info reduce_resource reduce_info
  
(*       [М] H џ T Type ЭЭЮ
 *       [М] H џ S Type ЭЭЮ
 *       [М] H; x: T џ f[x] С S ЭЭЮ
 *       [М] H џ C С collection[l](T) ЭЭЮ
 *       [ext] H џ < f[x] | x:C> С collection[l](S)
 *)
interactive map_wf 'H 'T:
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H >- "type"{'S}} -->
   sequent[squash]{'H; x:'T >- member{'S;'f['x]}} -->
   sequent[squash]{'H >- member{col[l:l]{'T};'C}} -->
   sequent['ext]  {'H >- member{col[l:l]{'S}; map{'C; x.'f['x]}}}

let tactic p =  map_wf (Sequent.hyp_count_addr p) (get_with_arg p) p
let term = <<   member{col[l:l]{'T}; map{'C; x.'f['x]}}    >>
let d_resource = Mp_resource.improve d_resource (term, wrap_intro tactic)

(*            y С < f[x] | x:C> in collection(S)  <==>
 *            Щx:T. (x С C) in collection(T) П (y = f[x] in S) 
 *)                   
interactive member_map 'H univ[l:l] 'T:
   sequent[squash]{'H; x:'T >- member{'S;'f['x]}} -->
   sequent[squash]{'H >- member{col[l:l]{'T};'C}} -->
   sequent['ext]{'H >- exst x:'T. (col_member{'T;'C;'x} and ('y='f['x] in 'S)) } -->
   sequent['ext]  {'H >- col_member{'S;map{'C; x.'f['x]};'y}}

interactive member_map_elim 'H 'J univ[l:l] 'T:
   sequent[squash]{'H; 'J; x:'T >- member{'S;'f['x]}} -->
   sequent[squash]{'H; 'J >- member{col[l:l]{'T};'C}} -->
   sequent['ext]  {'H; 'J;  x:'T; v: col_member{'T;'C;'x}; w: ('y='f['x] in 'S) >- 'Z } -->
   sequent['ext]  {'H; u:col_member{'S;map{'C; x.'f['x]};'y}; 'J >- 'Z }

let tactic i p =
   if i = 0 then
      member_map  (Sequent.hyp_count_addr p) (get_univ_arg p) (get_with_arg p) p
   else
      let i', j = hyp_indices p i in
         member_map_elim  i' j  (get_univ_arg p) (get_with_arg p) p
let term = << col_member{'T;map{'C; x.'f['x]};'x}   >>
let d_resource = Mp_resource.improve d_resource (term,  tactic)
      
(*       [М] H џ T Type ЭЭЮ
 *       [М] H; x: T џ f[x] С ”[l] ЭЭЮ
 *       [М] H џ C_1 С collection[l](T) ЭЭЮ
 *       [М] H џ C_2 С collection[l](T) ЭЭЮ
 *       [ext] H џ C_1 = C_2 in collection(T) ЭЭЮ
 *       [ext] H џ < f[x] | x:C_1> = < f[x] | x:C_2> in collection(T)
 *)         
interactive map_functionality 'H univ[l:l]:
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H; x:'T >- member{univ[l:l];'f['x]}} -->
   sequent[squash]{'H >- member{col[l:l]{'T};'C_1}} -->
   sequent[squash]{'H >- member{col[l:l]{'T};'C_2}} -->
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
interactive isect_wf 'H :
   sequent[squash]{'H >- member{univ[l:l];'T}} -->
   sequent[squash]{'H >- member{univ[l:l];'S}} -->
   sequent[squash]{'H; s:'S >- member{col[l:l]{'T};'C['s]}} -->
   sequent['ext]  {'H >- member{col[l:l]{'T}; ."isect"{'S;s.'C['s];'T}}}

let tactic p =  isect_wf (Sequent.hyp_count_addr p) p
let term = <<   member{col[l:l]{'T};."isect"{'X;x.'C['x];'T}}   >>
let d_resource = Mp_resource.improve d_resource (term, wrap_intro tactic)


(*    x С Цs:S.C[s] in collection(T)  <==>
 *    x С T  and  Шs:S. (x С C[s]) in collection(T)
 *)     
   
interactive member_isect 'H univ[l:l]:
   sequent[squash]{'H >- member{univ[l:l];'T}} -->
   sequent[squash]{'H >- member{univ[l:l];'S}} -->
   sequent[squash]{'H; s:'S >- member{col[l:l]{'T};'C['s]}} -->
   sequent['ext]  {'H; s:'S >-  col_member{'T;'C['s];'x}} -->
   sequent['ext]  {'H >-  member{'T;'x}} -->
   sequent['ext]  {'H >- col_member{'T;."isect"{'S;s.'C['s];'T};'x}}

interactive member_isect_elim 'H 'J univ[l:l] : 
   sequent[squash]{'H; 'J >- member{univ[l:l];'T}} -->
   sequent[squash]{'H; 'J >- member{univ[l:l];'S}} -->
   sequent[squash]{'H; 'J; s:'S >- member{col[l:l]{'T};'C['s]}} -->
   sequent['ext]   {'H; w:(all s:'S. col_member{'T;'C['s];'x}); 'J; v:member{'T;'x} >- 'Z } -->
   sequent['ext]   {'H; u:col_member{'T;."isect"{'S;s.'C['s];'T};'x}; 'J >- 'Z }

let tactic i p =
   if i = 0 then
      member_isect  (Sequent.hyp_count_addr p) (get_univ_arg p) p
   else
      let i', j = hyp_indices p i in
         member_isect_elim  i' j  (get_univ_arg p)  p
let term = << col_member{'T;."isect"{'S;s.'C['s]};'x}  >>
let d_resource = Mp_resource.improve d_resource (term,  tactic)

(*       [М] H џ T С ”[l] ЭЭЮ
 *       [М] H џ S С ”[l] ЭЭЮ
 *       [М] H; s: S џ C_1[s] С collection[l](T) ЭЭЮ
 *       [М] H; s: S џ C_2[s] С collection[l](T) ЭЭЮ
 *       [ext] H; s: S џ C_1[s] = C_2[s] in collection(T) ЭЭЮ
 *       [ext] H џ Цs:S.C_1[s] = Цs:S.C_2[s] in collection(T)
 *)                    
interactive isect_functionality 'H univ[l:l]:
   sequent[squash]{'H >- member{univ[l:l];'T}} -->
   sequent[squash]{'H >- member{univ[l:l];'S}} -->
   sequent[squash]{'H; s:'S >- member{col[l:l]{'T};'C_1['s]}} -->
   sequent[squash]{'H; s:'S >- member{col[l:l]{'T};'C_2['s]}} -->
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
interactive none_wf 'H :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent['ext]  {'H >- member{col[l:l]{'T}; none}}

let tactic p =  none_wf (Sequent.hyp_count_addr p) p
let term = <<   member{col[l:l]{'T}; none}    >>
let d_resource = Mp_resource.improve d_resource (term, wrap_intro tactic)

(*        y С <> in collection(T)   <==>   False
 *)
                    
interactive member_none 'H :
   sequent[squash]{'H >- "false"} -->
   sequent['ext]  {'H >- col_member{'T; none; 'y}}
      
interactive member_none_elim 'H 'J : :
   sequent['ext]  {'H; u:col_member{'T; none; 'y}; 'J >- 'Z}

let tactic i p =
   if i = 0 then
      member_none (Sequent.hyp_count_addr p) p
   else
      let i', j = hyp_indices p i in
         member_none_elim  i' j   p
let term = << col_member{'T;none;'y}   >>
let d_resource = Mp_resource.improve d_resource (term,  tactic)

(*--- add ---*)

declare add{'C_1;'C_2}

(*        unfold_add (C_1 + C_2) ЯЭЭЮ
 *        (Чb:Bool.(if b then C_1 else C_2))
 *)
prim_rw unfold_add : add{'C_1;'C_2} <--> col_union{bool; b. ifthenelse{'b;'C_1;'C_2}}
      
interactive add_wf 'H :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H >- member{col[l:l]{'T}; 'C_1}} -->
   sequent[squash]{'H >- member{col[l:l]{'T}; 'C_2}} -->
   sequent['ext]  {'H >- member{col[l:l]{'T}; add{'C_1;'C_2}}}

let tactic p =  add_wf (Sequent.hyp_count_addr p) p
let term = <<   member{col[l:l]{'T}; add{'C_1;'C_2}}    >>
let d_resource = Mp_resource.improve d_resource (term, wrap_intro tactic)

(*           x С (C_1 + C_2) in collection(T)  <==>
 *           x С C_1 in collection(T) or x С C_2 in collection(T)
 *)                   
interactive member_add1 'H  univ[l:l] :
   sequent[squash] {'H >- member{col[l:l]{'T};'C_1}} -->
   sequent[squash] {'H >- member{col[l:l]{'T};'C_2}} -->
   sequent['ext]   {'H >- col_member{'T; 'C_1 ; 'x}} -->
   sequent['ext]   {'H >- col_member{'T; add{'C_1;'C_2} ; 'x}}
      
interactive member_add2 'H  univ[l:l] :
   sequent[squash] {'H >- member{col[l:l]{'T};'C_1}} -->
   sequent[squash] {'H >- member{col[l:l]{'T};'C_2}} -->
   sequent['ext]   {'H >- col_member{'T; 'C_2 ; 'x}} -->
   sequent['ext]   {'H >- col_member{'T; add{'C_1;'C_2} ; 'x}}
      
interactive member_add_elim 'H 'J univ[l:l] :
   sequent[squash] {'H; 'J >- member{col[l:l]{'T};'C_1}} -->
   sequent[squash] {'H; 'J >- member{col[l:l]{'T};'C_2}} -->
   sequent['ext]   {'H; 'J; v: col_member{'T; 'C_1 ; 'x} >- 'Z} -->
   sequent['ext]   {'H; 'J; v: col_member{'T; 'C_2 ; 'x} >- 'Z} -->
   sequent['ext]   {'H; u:col_member{'T; add{'C_1;'C_2}; 'x}; 'J >- 'Z}

let tactic i p =
   if i = 0 then
      let flag =
         try get_sel_arg p with
               Not_found ->
                  raise (RefineError ("d_member_add", StringError "requires a flag"))
      in
      let tac =                          
         match flag with
               1 -> member_add1
            |  2 -> member_add2
            |  _ -> raise (RefineError ("d_concl_union", StringError "select either 1 or 2"))
      in       
      tac (Sequent.hyp_count_addr p) (get_univ_arg p) p
   else
      let i', j = hyp_indices p i in
         member_add_elim  i' j  (get_univ_arg p)  p
let term = << col_member{'T;add{'C_1;'C_2};'y}   >>
let d_resource = Mp_resource.improve d_resource (term,  tactic)

                    
(********************** Simplification lemmas **********************)

(* < x:<> | P[x]> = <> in collection(T)  *)                   
interactive filter_none 'H univ[l:l] :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H; x:'T >- member{univ[l:l];'P['x]}} -->
   sequent ['ext] {'H >- col_equal{'T;col_filter{none;x.'P['x]};none}}

(*  < x:(if b then C else D) | P[x]> =
 *  (if b then < x:C | P[x]> else < x:D | P[x]>) in collection(T)
 *) 
interactive filter_if 'H univ[l:l] :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H; x:'T >- member{univ[l:l];'P['x]}} -->
   sequent[squash]{'H >- member{col[l:l]{'T}; 'C}} -->                
   sequent[squash]{'H >- member{col[l:l]{'T}; 'D}} -->                
   sequent[squash]{'H >- member{bool; 'b}} -->                
   sequent ['ext] {'H >- col_equal{'T; col_filter{ifthenelse{'b;'C;'D}; x.'P['x]};
                                       ifthenelse{'b; col_filter{'C;x.'P['x]}; col_filter{'D;x.'P['x]}} }}

(*   < x:(c + d) | P[x]> =
 *   (< x:c | P[x]> + < x:d | P[x]>) in collection(T)
 *)   
interactive filter_add 'H univ[l:l] :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H; x:'T >- member{univ[l:l];'P['x]}} -->
   sequent[squash]{'H >- member{col[l:l]{'T}; 'c}} -->                
   sequent[squash]{'H >- member{col[l:l]{'T}; 'd}} -->                
   sequent ['ext] {'H >- col_equal{'T; col_filter{add{'c;'d}; x.'P['x]};
                                       add{ col_filter{'c;x.'P['x]}; col_filter{'d;x.'P['x]}} }}

(*   < x:(Чs:S.c[s]) | P[x]> =
 *   Чs:S.< x:c[s] | P[x]> in collection(T)
 *)     
interactive filter_union 'H univ[l:l] :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H >- member{univ[l:l];'S}} -->
   sequent[squash]{'H; x:'T >- member{univ[l:l];'P['x]}} -->
   sequent[squash]{'H; s:'S >- member{col[l:l]{'T}; 'c['s]}} -->                
   sequent ['ext] {'H >- col_equal{'T; col_filter{col_union{'S;s.'c['s]}; x.'P['x]};
                                       col_union{'S; s.col_filter{'c['s];x.'P['x]}} }}

(*   Чs:S.(c[s] + d[s]) =
 *    ((Чs:S.c[s]) + (Чs:S.d[s])) in collection(T)
 *)     
interactive union_add  'H univ[l:l] :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H >- member{univ[l:l];'S}} -->
   sequent[squash]{'H; s:'S >- member{col[l:l]{'T}; 'c['s]}} -->                
   sequent[squash]{'H; s:'S >- member{col[l:l]{'T}; 'd['s]}} -->                
   sequent ['ext] {'H >- col_equal{'T; col_union{'S; s.add{'c['s];'d['s]}};
                                       add{ col_union{'S; s.'c['s]}; col_union{'S; s.'d['s]}}  }}
                      
(*     Чs:S.c = c in collection(T)
 *) 
interactive union_const  'H univ[l:l] :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H >- member{univ[l:l];'S}} -->
   sequent[squash]{'H >- member{col[l:l]{'T}; 'c}} -->                
   sequent['ext]  {'H >- 'S} -->
   sequent['ext]  {'H >- col_equal{'T; col_union{'S; s.'c}; 'c}}

(*    Чs:S.(if b then C[s] else D[s]) =
 *    (if b then (Чs:S.C[s]) else (Чs:S.D[s])) in collection(T)
 *)         
interactive union_if  'H univ[l:l] :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H >- member{univ[l:l];'S}} -->
   sequent[squash]{'H; s:'S >- member{col[l:l]{'T}; 'C['s]}} -->                
   sequent[squash]{'H; s:'S >- member{col[l:l]{'T}; 'D['s]}} -->                
   sequent[squash]{'H >- member{bool;'b}} -->
   sequent['ext]  {'H >- col_equal{'T; col_union{'S; s. ifthenelse{'b; 'C['s]; 'D['s]}};
                                       ifthenelse{'b; col_union{'S; s. 'C['s]};  col_union{'S; s. 'D['s]}} }}

(*    (c + d) = (d + c) in collection(T)
 *)
interactive add_com 'H univ[l:l] :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H >- member{col[l:l]{'T}; 'c}} -->                
   sequent[squash]{'H >- member{col[l:l]{'T}; 'd}} -->                
   sequent ['ext] {'H >- col_equal{'T;add{'c;'d};add{'d;'c}}}

(*   (c + <>) = c in collection(T)
 *)     
interactive add_none 'H univ[l:l]:
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H >- member{col[l:l]{'T}; 'c}} -->                
   sequent ['ext] {'H >- col_equal{'T;add{'c;none};'c}}

(*   (c + <>) = c in collection(T)
 *)               
interactive none_add 'H univ[l:l]:
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H >- member{col[l:l]{'T}; 'c}} -->                
   sequent ['ext] {'H >- col_equal{'T;add{'c;none};'c}}

(*    (c + c) = c in collection(T)
 *)
interactive add_idempotent 'H univ[l:l] :
   sequent[squash]{'H >- "type"{'T}} -->
   sequent[squash]{'H >- member{col[l:l]{'T}; 'c}} -->                
   sequent ['ext] {'H >- col_equal{'T;add{'c;'c};'c}}

(*  <(if b then x else y)> = (if b then <x> else <y>) in collection(T)
 *)
interactive singlenton_if  'H univ[l:l] :
   sequent[squash]{'H >- member{'T;'x}} -->
   sequent[squash]{'H >- member{'T;'y}} -->
   sequent[squash]{'H >- member{bool;'b}} -->
   sequent['ext]  {'H >- col_equal{'T; singlenton{ ifthenelse{'b;'x;'y}};
                                       ifthenelse{'b; singlenton{'x}; singlenton{'y}} }}


              
(********************** dforms **********************)
      

dform col_df : Col[l:l]{'T} =`"Collection[" slot[l:l] `"](" slot{'T} `")"
dform col_df : Col{'T} =`"Collection(" slot{'T} `")"

dform col_member_df : Col_member[l:l]{'T;'C;'x} = member{'C;'x} `" in " Col[l:l]{'T}  

dform col_equal_df : col_equal{'T;'c_1;'c_2} = equal{col{'T};'c_1;'c_2}

                                                  
dform type_col_df : type_col{'T} = downarrow slot{'T}
dform col_type_df : col_type{'C;'T} = uparrow slot{'C}
                                         
dform singlenton_df :  singlenton{'x} = `"<" slot{'x} `">"
                                           
dform union_df : mode[prl] :: parens :: "prec"[prec_tunion] :: union{'X; x. 'Y} =
   cup slot{'x} Nuprl_font!member slot{'X} `"." slot{'Y}
      
dform col_union_df : mode[prl] :: parens :: "prec"[prec_tunion] :: col_union{'X; x. 'C} =
   cup slot{'x} `":" slot{'X} `"." slot{'C}

dform map_df : map{'C; x.'f} =
      pushm[3] `"< " slot{'f} `" | " bvar{'x} `":" slot{'C} `">" popm

dform col_filter_df : col_filter{'C; x.'P} =
      pushm[3] `"< " bvar{'x} `":" slot{'C} `" | " slot{'P} `">" popm
         
dform isect_df : mode[prl] :: parens :: "prec"[prec_tunion] :: "isect"{'S; s. 'C;'T} =
   cap slot{'s} `":" slot{'S} `"." slot{'C}
      
dform none_df : none = `"<>"
                          
dform add_df :  mode[prl] :: parens :: "prec"[prec_add] :: "add"{'a; 'b} =
   slot["le"]{'a} `" + " slot["lt"]{'b}
      

