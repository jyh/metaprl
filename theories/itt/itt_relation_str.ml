(*!
 *
 * @begin[doc]
 * @module[Itt_relation_str]
 *
 * The @tt[Itt_relation_str] module defines algebraic structures such
  as ordered sets, PERs, types with decidable equality and so on.
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
 * Author: Alexei Kopylov
 * @email{apk6@cs.cornell.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
extends Itt_equal
extends Itt_int_ext
extends Itt_decidable
extends Itt_record
extends Itt_algebra_df
extends Itt_logic
extends Itt_bisect
extends Itt_comment
(*! @docoff *)

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermAddr
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Var
open Top_conversionals

open Base_dtactic
open Base_auto_tactic

open Itt_decidable
open Itt_record
open Itt_logic
open Itt_bisect

open Itt_comment


let dByDefT  unfold n = rw unfold n thenT dT n
let dByRecDefT term unfold n = dByDefT unfold n thenT rwhAll (makeFoldC term unfold)

let soft_elim term unfold = term, (dByDefT unfold)
let soft_into term unfold = term, (dByDefT unfold 0)
let softrec_elim term unfold = term, (dByRecDefT term unfold)
let softrec_into term unfold = term, (dByRecDefT term unfold 0)



let reduceByDefC unfold =   unfold thenC reduceTopC
let reduceByRecDefC term unfold = reduceByDefC unfold thenC higherC (makeFoldC term unfold)

let soft_reduce term unfold  = term, (reduceByDefC unfold)
let softrec_reduce term unfold  = term, (reduceByRecDefC term unfold)




(*!
 * @begin[doc]
 * @modsection{Order}
   @modsubsection{Definition}
   Order is a type  $<<label["car":t]>>$ with an irreflexive transitive complete
  relation:
     $$<<label["<":t]>>  : <<label["car":t]-> label["car":t] -> bool>>$$
 * @end[doc]
 *)




define order1 : order[i:l] <-->
    { car : univ[i:l];
      "<" : ^car -> ^car -> bool ;
      all x:^car. not{"assert"{.'x ^< 'x}};
      all x:^car.all y:^car.all z:^car. ("assert"{.'x ^< 'y} &  "assert"{.'y ^< 'z} =>  "assert"{.'x ^< 'z});
      all x:^car.all y:^car. ("assert"{.'x ^< 'y} or  "assert"{.'y ^< 'x} or 'x='y in ^car)
    }

(*
define irreflexiveOrder1 :  IrreflexiveOrder[i:l] <--> { self : orderSig[i:l] | all x:^car. not{"assert"{.'x ^< 'x}}}

define transitiveOrder1 :  TransitiveOrder[i:l] <--> { self : orderSig[i:l] | all x:^car.all y:^car.all z:^car. ("assert"{.'x ^< 'y} &  "assert"{.'y ^< 'z} =>  "assert"{.'x ^< 'z})}

define partialOrder1 : PartialOrder[i:l] <--> bisect{ IrreflexiveOrder[i:l]; TransitiveOrder[i:l]}


dform iorder_df : except_mode[src] :: IrreflexiveOrder[i:l] = `"IrreflexiveOrder" sub{slot[i:l]}
dform torder_df : except_mode[src] :: TransitiveOrder[i:l] = `"TransitiveOrder" sub{slot[i:l]}
dform porder_df : except_mode[src] :: PartialOrder[i:l] = `"PartialOrder" sub{slot[i:l]}


define order1 : order[i:l] <-->  { self : PartialOrder[i:l] | all x:^car.all y:^car. ("assert"{.'x ^< 'y} or  "assert"{.'y ^< 'x} or 'x='y in ^car) }
*)

(*! @docoff *)

define less: less{'self; 'a;'b} <--> "assert"{.'a ^< 'b}

dform less_df : parens :: except_mode[src] :: less{'self; 'a;'b}
 = 'a  bf[" <"]sub{'self} `" " 'b

(*!
 * @begin[doc]
 * @modsection{Decidable Equality}
   @modsubsection{Definition}
   @tt[DecEquality] is a type (@tt[car]) with an equality decider:
  $$<<label["=":t]>> : <<label[car:t]-> label[car:t] -> bool>>$$
 * @end[doc]
 *)

define decEquality : DecEquality[i:l] <-->
    { car : univ[i:l];
      "=" : ^car -> ^car -> bool;
       all x:^car. all y:^car. iff{"assert"{.'x ^= 'y}; . 'x='y in ^car}
    }

(*! @docoff *)


dform order_df : except_mode[src] :: order[i:l] = `"Order" sub{slot[i:l]}

dform deq_df : except_mode[src] ::  DecEquality[i:l] = `"DecEquality" sub{slot[i:l]}


let fold_less = makeFoldC <<less{'self; 'a;'b}>> less
(*
let irreflexiveOrder = irreflexiveOrder1 thenC higherC fold_less

let transitiveOrder = transitiveOrder1 thenC higherC fold_less
*)
let order = order1 thenC higherC fold_less


let resource elim += soft_elim <<order[i:l]>> order

(*!
 * @begin[doc]
 * @rules
 * @end[doc]
 *)

interactive less_wf  {| intro[] |} order[i:l] :
   [wf] sequent [squash] { 'H >- 'ord in order[i:l] }  -->
   [wf] sequent [squash] { 'H >- 'x in 'ord^car }  -->
   [wf] sequent [squash] { 'H >- 'y in 'ord^car }  -->
   sequent ['ext]   { 'H >- 'x <['ord] 'y in bool}


define compare: compare{'self; 'a;'b; 'less_case; 'equal_case; 'greater_case} <--> if 'a ^< 'b then 'less_case else if 'b ^< 'a then 'greater_case else 'equal_case



interactive three_cases  compare{'ord; 'x;'y; 'less_case; 'equal_case; 'greater_case}  order[i:l]  bind{t.'T['t]}:
   [wf] sequent [squash] { 'H >- 'ord in order[i:l] }  -->
   [wf] sequent [squash] { 'H >- 'x in 'ord^car }  -->
   [wf] sequent [squash] { 'H >- 'y in 'ord^car }  -->
   sequent ['ext] { 'H; u:  less{'ord;'x;'y} >- 'T['less_case] }  -->
   sequent ['ext] { 'H; u:  less{'ord;'y;'x} >- 'T['greater_case] }  -->
   sequent ['ext] { 'H; u:  'x = 'y in 'ord^car >- 'T['equal_case] }  -->
   sequent ['ext]   { 'H >- 'T[compare{'ord; 'x;'y; 'less_case; 'equal_case; 'greater_case}]}


(*! @docoff *)

let decideOrder3T compare_term order_term p =
   let z = get_opt_var_arg "z" p in
   let bind =
      try
         let b = get_with_arg p in
            if is_xbind_term b then
               b
            else
               raise generic_refiner_exn (* will be immedeiatelly caugh *)
      with
         RefineError _ ->
            mk_xbind_term z (var_subst (Sequent.concl p) compare_term  z)
   in
    three_cases compare_term order_term bind p

(*! @doc { } *)

interactive compare_wf {| intro [] |} order[i:l] :
   [wf] sequent [squash] { 'H >- 'ord in order[i:l] }  -->
   [wf] sequent [squash] { 'H >- 'x in 'ord^car }  -->
   [wf] sequent [squash] { 'H >- 'y in 'ord^car }  -->
   sequent [squash] { 'H; u:  less{'ord;'x;'y} >- 'less_case in 'T }  -->
   sequent [squash] { 'H; u:  less{'ord;'y;'x} >- 'greater_case in 'T } -->
   sequent [squash] { 'H; u: 'x = 'y in 'ord^car >- 'equal_case in 'T } -->
   sequent ['ext]   { 'H >-  compare{'ord; 'x;'y; 'less_case; 'equal_case; 'greater_case} in 'T}



dform match_tree_df : except_mode[src] :: compare{'O; 'a;'b; 'less_case; 'equal_case; 'greater_case} =
   szone pushm[0] pushm[3] `"Compare in " slot{'O} `": " hspace
       'a `"<" 'b `" -> " slot{'less_case} hspace
       'a `"=" 'b `" -> " slot{'equal_case}  hspace
       'a `">" 'b `" -> " slot{'greater_case} popm popm ezone



(*! @begin[doc]
  Corollary: The equality is decidable in ordered sets
  @end[doc]
*)

interactive dec_equalaty  order[i:l] :
   sequent [squash] { 'H >- 'ord in order[i:l] }  -->
   sequent [squash] { 'H >- 'x in 'ord^car }  -->
   sequent [squash] { 'H >- 'y in 'ord^car }  -->
   sequent ['ext]   { 'H >-  decidable{.'x='y in 'ord^car} }


(*! @begin[doc]
@modsection{Example: integers}
  @end[doc]
*)

define int_order: int_order <--> {car= int; "<"= lambda{a.lambda{b.lt_bool{'a;'b}}}}

(*! @docoff *)



