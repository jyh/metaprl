(*!
 * @spelling{arithT tactic implementation}
 *
 * @begin[doc]
 * @module[Itt_int_arith]
 *
 * Prove simple systems of inequalities
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
 * Author: Yegor Bryukhov
 * @email{ynb@mail.ru}
 * @end[license]
 *)

extends Itt_equal
extends Itt_rfun
extends Itt_logic
extends Itt_bool
extends Itt_int_ext
(*! @docoff *)

open Printf
open Mp_debug
open Opname
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.TermType
open Refiner.Refiner.RefineError
open Rformat
open Mp_resource

open Var
open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Conversionals

open Base_meta
open Base_dtactic

open Top_conversionals

open Itt_equal
open Itt_struct
open Itt_bool

open Itt_int_base
open Itt_int_ext

let _ = show_loading "Loading Itt_int_ext%t"

(*******************************************************
 * ARITH
 *******************************************************)

let get_term i p =
(* We skip first item because it is a context *)
   if i<>1 then
      let g=Sequent.goal p in
      let (_,t)=Refiner.Refiner.TermMan.nth_hyp g i in
         t
   else
      mk_simple_term xperv []

let le2geT t p =
   let (left,right)=dest_le t in
   let newt=mk_ge_term right left in
   (assertT newt thenAT (rwh unfold_ge 0 thenT (onSomeHypT nthHypT))) p

interactive lt2ge 'H :
   sequent [squash] { 'H >- 'a IN int } -->
   sequent [squash] { 'H >- 'b IN int } -->
   sequent [squash] { 'H >- 'a < 'b } -->
   sequent ['ext] { 'H >- 'b >= ('a +@ 1) }

let lt2geT t p =
   let (left,right)=dest_lt t in
   let newt=mk_ge_term right
                      (mk_add_term left
                                  (mk_number_term (Mp_num.num_of_int 1))) in
      (assertT newt thenAT lt2ge (Sequent.hyp_count_addr p)) p

interactive gt2ge 'H :
   sequent [squash] { 'H >- 'a IN int } -->
   sequent [squash] { 'H >- 'b IN int } -->
   sequent [squash] { 'H >- 'a > 'b } -->
   sequent ['ext] { 'H >- 'a >= ('b +@ 1) }

let gt2geT t p =
   let (left,right)=dest_gt t in
   let newt=mk_ge_term left
                      (mk_add_term right
                                  (mk_number_term (Mp_num.num_of_int 1))) in
      (assertT newt thenAT gt2ge (Sequent.hyp_count_addr p)) p

interactive eq2ge1 'H :
   sequent [squash] { 'H >- 'a = 'b in int } -->
   sequent ['ext] { 'H >- 'a >= 'b }

let eq2ge1T p = eq2ge1 (Sequent.hyp_count_addr p) p

interactive eq2ge2 'H :
   sequent [squash] { 'H >- 'a = 'b in int } -->
   sequent ['ext] { 'H >- 'b >= 'a }

let eq2ge2T p = eq2ge2 (Sequent.hyp_count_addr p) p

let eq2geT t =
   let (_,l,r)=dest_equal t in
   (assertT (mk_ge_term l r)
      thenAT (eq2ge1T thenT (onSomeHypT nthHypT))
      thenMT ((assertT (mk_ge_term r l))
                 thenAT (eq2ge2T thenT (onSomeHypT nthHypT))))

interactive notle2ge 'H :
   sequent [squash] { 'H >- 'a IN int } -->
   sequent [squash] { 'H >- 'b IN int } -->
   sequent [squash] { 'H >- "not"{('a <= 'b)} } -->
   sequent ['ext] { 'H >- 'a >= ('b +@ 1) }

(*
let notle2geT t =
   let (l,r)=dest_le t in
   let newt = mk_ge_term l (mk_add_term r (Mp_num.num_of_int 1)) in
*)

let anyArithRel2geT i p =
(* We skip first item because it is a context *)
   let t=get_term i p in
   if is_le_term t then le2geT t p
   else if is_lt_term t then lt2geT t p
   else if is_gt_term t then gt2geT t p
   else if is_equal_term t then
      let (tt,l,r)=dest_equal t in
         if tt=int_term then
            (eq2geT t p)
         else
            idT p
   else idT p (*if is_not_term t then
      let t1=dest_not t in
         if is_ge_term t1 then notge2geT t1
         else if is_le_term t1 then notle2geT t1
         else if is_lt_term t1 then notlt2geT t1
         else if is_gt_term t1 then notgt2geT t1 *)

interactive_rw bnot_lt2ge_rw :
   ('a IN int) -->
   ('b IN int) -->
   "assert"{bnot{lt_bool{'a; 'b}}} <--> ('a >= 'b)

let bnot_lt2geC = bnot_lt2ge_rw

let lt2ConclT p = (magicT thenLT [idT; rwh bnot_lt2geC (-1)] ) p

let ltInConcl2HypT =
   (rwh unfold_lt 0) thenMT lt2ConclT

let gtInConcl2HypT p =
   (rwh unfold_gt 0 thenMT ltInConcl2HypT ) p

interactive_rw bnot_le2gt_rw :
   ('a IN int) -->
   ('b IN int) -->
   "assert"{bnot{le_bool{'a; 'b}}} <--> ('a > 'b)

let bnot_le2gtC = bnot_le2gt_rw

let leInConcl2HypT =
   (rwh unfold_le 0 thenMT magicT thenLT [idT;rwh bnot_le2gtC (-1)])

let geInConcl2HypT p =
   (rwh unfold_ge 0 thenMT leInConcl2HypT) p

let arithRelInConcl2HypT p =
   let g=Sequent.goal p in
   let t=Refiner.Refiner.TermMan.nth_concl g 1 in
(*      print_term stdout t; *)
   if is_lt_term t then ltInConcl2HypT p
   else if is_gt_term t then gtInConcl2HypT p
   else if is_le_term t then leInConcl2HypT p
   else if is_ge_term t then geInConcl2HypT p
   else idT p

interactive ge_addMono 'H :
   sequent [squash] { 'H >- 'a IN int } -->
   sequent [squash] { 'H >- 'b IN int } -->
   sequent [squash] { 'H >- 'c IN int } -->
   sequent [squash] { 'H >- 'd IN int } -->
   sequent [squash] { 'H >- 'a >= 'b } -->
   sequent [squash] { 'H >- 'c >= 'd } -->
   sequent ['ext] { 'H >- ('a +@ 'c) >= ('b +@ 'd) }

type comparison = Less | Equal | Greater

let rec compare_terms t1 t2 =
   let {term_op=op1; term_terms=subt1} = dest_term t1 in
   let {term_op=op2; term_terms=subt2} = dest_term t2 in
     match compare_ops op1 op2 with
       Less -> Less
     | Greater -> Greater
     | Equal -> compare_btlists subt1 subt2

and compare_ops op1 op2 =
   let {op_name = opn1; op_params = par1} = dest_op op1 in
   let {op_name = opn2; op_params = par2} = dest_op op2 in
   let str1 = string_of_opname opn1 in
   let str2 = string_of_opname opn2 in
      if str1 < str2 then
        Less
      else if str1 > str2 then
        Greater
      else
        compare_plists par1 par2

and compare_btlists subt1 subt2 =
   match subt1 with
     [] ->
       (
       match subt2 with
         [] -> Equal
       | hd2::tail2 -> Less
       )
   | hd1::tail1 ->
       (
       match subt2 with
         [] -> Greater
       | hd2::tail2 ->
         match compare_bterms hd1 hd2 with
	   Less -> Less
	 | Greater -> Greater
	 | Equal -> compare_btlists tail1 tail2
       )

and compare_bterms b1 b2 =
   let {bvars = bv1; bterm = t1} = dest_bterm b1 in
   let {bvars = bv2; bterm = t2} = dest_bterm b2 in
   compare_terms t1 t2

and compare_plists p1 p2 =
   match p1 with
     [] ->
       (
       match p2 with
         [] -> Equal
       | hd2::tail2 -> Less
       )
   | hd1::tail1 ->
       (
       match p2 with
         [] -> Greater
       | hd2::tail2 ->
         match compare_params hd1 hd2 with
	   Less -> Less
	 | Greater -> Greater
	 | Equal -> compare_plists tail1 tail2
       )

and compare_params par1 par2 =
   let p1 = dest_param par1 in
   let p2 = dest_param par2 in
   match p1 with
     Number(n1) ->
      (
       match p2 with
         Number(n2) ->
	   if n1<n2 then Less
	   else if n1>n2 then Greater
	   else Equal
       | _ -> Less
      )
   | String(s1) ->
      (
       match p2 with
         Number(_) -> Greater
       | String(s2) ->
	   if s1<s2 then Less
	   else if s1>s2 then Greater
	   else Equal
       | _ -> Less
      )
   | Token(s1) ->
      (
       match p2 with
         Number(_) -> Greater
       | String(_) -> Greater
       | Token(s2) ->
	   if s1<s2 then Less
	   else if s1>s2 then Greater
	   else Equal
       | _ -> Less
      )
   | Var(s1) ->
      (
       match p2 with
         Number(_) -> Greater
       | String(_) -> Greater
       | Token(_) -> Greater
       | Var(s2) ->
	   if s1<s2 then Less
	   else if s1>s2 then Greater
	   else Equal
       | _ -> Less
      )
   | MNumber(s1) ->
      (
       match p2 with
         Number(_) -> Greater
       | String(_) -> Greater
       | Token(_) -> Greater
       | Var(_) -> Greater
       | MNumber(s2) ->
	   if s1<s2 then Less
	   else if s1>s2 then Greater
	   else Equal
       | _ -> Less
      )
   | MString(s1) ->
      (
       match p2 with
         Number(_) -> Greater
       | String(_) -> Greater
       | Token(_) -> Greater
       | Var(_) -> Greater
       | MNumber(_) -> Greater
       | MString(s2) ->
	   if s1<s2 then Less
	   else if s1>s2 then Greater
	   else Equal
       | _ -> Less
      )
   | MToken(s1) ->
      (
       match p2 with
         Number(_) -> Greater
       | String(_) -> Greater
       | Token(_) -> Greater
       | Var(_) -> Greater
       | MNumber(_) -> Greater
       | MString(_) -> Greater
       | MToken(s2) ->
	   if s1<s2 then Less
	   else if s1>s2 then Greater
	   else Equal
       | _ -> Less
      )
   | MLevel(l1) ->
      (
       match p2 with
         Number(_) -> Greater
       | String(_) -> Greater
       | Token(_) -> Greater
       | Var(_) -> Greater
       | MNumber(_) -> Greater
       | MString(_) -> Greater
       | MToken(_) -> Greater
       | MLevel(l2) -> compare_levels l1 l2
       | _ -> Less
      )
   | MVar(s1) ->
      (
       match p2 with
         Number(_) -> Greater
       | String(_) -> Greater
       | Token(_) -> Greater
       | Var(_) -> Greater
       | MNumber(_) -> Greater
       | MString(_) -> Greater
       | MToken(_) -> Greater
       | MLevel(_) -> Greater
       | MVar(s2) ->
	   if s1<s2 then Less
	   else if s1>s2 then Greater
	   else Equal
       | _ -> Less
      )
   | ObId(id1) ->
      (
       match p2 with
         Number(_) -> Greater
       | String(_) -> Greater
       | Token(_) -> Greater
       | Var(_) -> Greater
       | MNumber(_) -> Greater
       | MString(_) -> Greater
       | MToken(_) -> Greater
       | MLevel(_) -> Greater
       | MVar(_) -> Greater
       | ObId(id2) -> compare_plists id1 id2
       | _ -> Less
      )
   | ParamList(pl1) ->
      (
       match p2 with
         Number(_) -> Greater
       | String(_) -> Greater
       | Token(_) -> Greater
       | Var(_) -> Greater
       | MNumber(_) -> Greater
       | MString(_) -> Greater
       | MToken(_) -> Greater
       | MLevel(_) -> Greater
       | MVar(_) -> Greater
       | ObId(_) -> Greater
       | ParamList(pl2) -> compare_plists pl1 pl2
      )

and compare_levels l1 l2 =
   let {le_const = c1; le_vars = v1} = dest_level l1 in
   let {le_const = c2; le_vars = v2} = dest_level l2 in
     if c1<c2 then Less
     else if c1>c2 then Greater
     else compare_lvlists v1 v2

and compare_lvlists lv1 lv2 =
   match lv1 with
     [] ->
       (
       match lv2 with
         [] -> Equal
       | hd2::tail2 -> Less
       )
   | hd1::tail1 ->
       (
       match lv2 with
         [] -> Greater
       | hd2::tail2 ->
         match compare_lvars hd1 hd2 with
	   Less -> Less
	 | Greater -> Greater
	 | Equal -> compare_lvlists tail1 tail2
       )

and compare_lvars v1 v2 =
   let {le_var=s1; le_offset=o1}=dest_level_var v1 in
   let {le_var=s2; le_offset=o2}=dest_level_var v2 in
     if s1<s2 then Less
     else if s1>s2 then Greater
     else
       if o1<o2 then Less
       else if o1>o2 then Greater
       else Equal

let ct a b =
  match compare_terms a b with
    Less -> -1
  | Equal -> 0
  | Greater -> 1

interactive_rw mul_BubblePrimitive_rw :
   ( 'a IN int ) -->
   ( 'b IN int ) -->
   ( 'c IN int ) -->
   ('a *@ ('b *@ 'c)) <--> ('b *@ ('a *@ 'c))

let mul_BubblePrimitiveC = mul_BubblePrimitive_rw

(* One step of sorting of production of some terms with simultenious
   contraction of product of integers
 *)
let mul_BubbleStepC tm =
   if is_mul_term tm then
      let (a,s) = dest_mul tm in
         if is_mul_term s then
            let (b,c) = dest_mul s in
	       if (is_number_term a) & (is_number_term b) then
	          (mul_AssocC thenC (addrC [0] reduceC))
	       else
                  if (compare_terms b a)=Less or
                   (is_number_term b) then
                     mul_BubblePrimitiveC
                  else
                     idC
         else
            if (is_number_term a) & (is_number_term s) then
	       reduce_mul
	    else
               if (compare_terms s a)=Less or
                (is_number_term s) then
	          mul_CommutC
	       else
	          idC
   else
      failC

(* here we apply mul_BubbleStepC as many times as possible thus
   finally we have all mul subterms positioned in order
 *)
let mul_BubbleSortC = sweepDnC (termC mul_BubbleStepC)

let inject_coefC t =
   if is_mul_term t then
      mul_Id3C
   else
      failC

(* Before terms sorting we have to put parentheses in the rightmost-first
manner
 *)
let mul_normalizeC = (sweepDnC mul_Assoc2C) thenC
                     (higherC (termC inject_coefC)) thenC
                     (whileProgressC mul_BubbleSortC)

interactive_rw sum_same_products1_rw :
   ('a = 'b in int) -->
   ((number[i:n] *@ 'a) +@ (number[j:n] *@ 'b)) <--> ((number[i:n] +@ number[j:n]) *@ 'a)

let sum_same_products1C = sum_same_products1_rw

interactive_rw sum_same_products2_rw :
   ('a = 'b in int) -->
   ((number[i:n] *@ 'a) +@ 'b) <--> ((number[i:n] +@ 1) *@ 'a)

let sum_same_products2C = sum_same_products2_rw

interactive_rw sum_same_products3_rw :
   ('a = 'b in int) -->
   ('a +@ (number[j:n] *@ 'b)) <--> ((number[j:n] +@ 1) *@ 'a)

let sum_same_products3C = sum_same_products3_rw

interactive_rw sum_same_products4_rw :
   ('a = 'b in int) -->
   ('a +@ 'b) <--> (2 *@ 'a)

let sum_same_products4C = sum_same_products4_rw

let same_productC t =
   if (is_add_term t) then
      let (a,b)=dest_add t in
      if (is_mul_term a) & (is_mul_term b) then
         let (a1,a2)=dest_mul a in
         let (b1,b2)=dest_mul b in
         if is_number_term a1 then
            if is_number_term b1 then
               if (compare_terms a2 b2)=Equal then
                  sum_same_products1C
               else
                  idC
            else
               if (compare_terms a1 b)=Equal then
                  sum_same_products2C
               else
                  idC
         else
            if is_number_term b1 then
               if (compare_terms a b1)=Equal then
                  sum_same_products3C
               else
                  idC
            else
               if (compare_terms a b)=Equal then
                  sum_same_products4C
               else
                  idC
      else
         idC
   else
      idC

interactive_rw add_BubblePrimitive_rw :
   ( 'a IN int ) -->
   ( 'b IN int ) -->
   ( 'c IN int ) -->
   ('a +@ ('b +@ 'c)) <--> ('b +@ ('a +@ 'c))

let add_BubblePrimitiveC = add_BubblePrimitive_rw

(* One step of sorting of sum of some terms with simultenious
   contraction of sum of integers
 *)
let add_BubbleStepC tm =
   if is_add_term tm then
      let (a,s) = dest_add tm in
         if is_add_term s then
            let (b,c) = dest_add s in
	       if (is_number_term a) & (is_number_term b) then
	          (add_AssocC thenC (addrC [0] reduceC))
	       else
                  if (compare_terms b a)=Less then
                     add_BubblePrimitiveC
                  else
                     idC
         else
            if (is_number_term a) & (is_number_term s) then
	       reduceC
	    else
               if (compare_terms s a)=Less then
	          add_CommutC
	       else
	          idC
   else
      failC

(* here we apply add_BubbleStepC as many times as possible thus
   finally we have all sum subterms positioned in order
 *)
let add_BubbleSortC = (sweepDnC (termC same_productC)) thenC
                      (sweepDnC (termC add_BubbleStepC))

(* Before terms sorting we have to put parentheses in the rightmost-first
manner
 *)
let add_normalizeC = (whileProgressC (sweepDnC add_Assoc2C)) thenC
                     (whileProgressC add_BubbleSortC)

let open_parenthesesC = whileProgressC (sweepDnC mul_add_DistribC)

let normalizeC = (sweepDnC reduceC) thenC
                 open_parenthesesC thenC
                 mul_normalizeC thenC
                 add_normalizeC

interactive_rw ge_addContract_rw :
   ( 'a IN int ) -->
   ( 'b IN int ) -->
   ('a >= ('b +@ 'a)) <--> (0 >= 'b)

let ge_addContractC = ge_addContract_rw

(*
   Reduce contradictory relation a>=a+b where b>0.
 *)
let reduceContradRelT i p = (rw ((addrC [0] normalizeC) thenC
                                 (addrC [1] normalizeC) thenC
		                 ge_addContractC thenC
			         reduceC)
                                i) p

let tryReduce_geT i p =
   let t=get_term i p in
      if is_ge_term t then
         (rw ((addrC [0] normalizeC) thenC
             (addrC [1] (add_Id3C thenC normalizeC)))
             i) p
      else
	 idT p

(* Generate sum of ge-relations
 *)
let sumList tl g =
   match tl with
   h::t ->
      let aux a (l,r) =
         let (_,tm) = nth_hyp g a in
         let (al,ar) = dest_ge tm in
         (mk_add_term al l, mk_add_term ar r) in
      let (_,h_tm) = nth_hyp g h in
      let (sl, sr)=List.fold_right aux t (dest_ge h_tm) in
      mk_ge_term sl sr
   | [] ->
      let zero = << 0 >> in
         mk_ge_term zero zero

(* autoT should be removed to permit incorporation
of this tactic into autoT
 *)
let proveSumT p =
   (ge_addMono (Sequent.hyp_count_addr p)) p

(* Asserts sum of ge-relations and grounds it
 *)
let sumListT l p =
   let s = sumList l (Sequent.goal p) in
   (assertT s thenAT (progressT proveSumT)) p

(* Test if term has a form of a>=b+i where i is a number
 *)
let good_term t =
(*
   print_term stdout t;
   eprintf "\n %s \n" (Opname.string_of_opname (opname_of_term t));
*)
   if is_ge_term t then
     let (_,b)=dest_ge t in
        if is_add_term b then
           let (d,_)=dest_add b in
              (is_number_term d)
        else
           false
   else
     ((*print_term stdout t;
      eprintf "%s %s\n" (Opname.string_of_opname (opname_of_term t))
                        (Opname.string_of_opname (opname_of_term ge_term));*)
      false
     )

(* Searches for contradiction among ge-relations
 *)
let findContradRelT p =
(*   let es = explode_sequent (Sequent.goal p) in
   let {sequent_args = sa; sequent_hyps = sh; sequent_goals = sg} = es in
   let aux h = match h with Hypothesis (s,t) -> t
      | Context (s,l) -> (mk_simple_term xperv []) in
   let shl = List.map aux (SeqHyp.to_list sh) in
   let sgl = SeqGoal.to_list sg in
   begin
      print_term stdout sa;
      print_term_list stdout shl;
      print_term_list stdout sgl;
      failT p
   end
*)
   let g=Sequent.goal p in
   let l = Arith.TermHyps.collect good_term g in
(* begin
           List.map (fun x->let (_,t)=(Refiner.Refiner.TermMan.nth_hyp g x)
                     in print_term stdout t) l;
*)
   let ar=Array.of_list l in
   match Arith.TG.solve (g,ar) with
      Arith.TG.Int (_,r),_ ->
         (*
	   let aux i = eprintf "i=%u " i in
           let aux2 i = eprintf "r=%u " ar.(i) in
	 *)
         let aux3 i al = (ar.(i))::al in
         let rl = List.fold_right aux3 r [] in
         begin
            (*
	      List.map aux l;
              prerr_endline "";
              List.map aux rl;
              flush stderr;
            *)
            sumListT rl p
         end
      | Arith.TG.Disconnected,_ ->
         begin
            eprintf "No contradiction found";
            prerr_endline "";
            failT p
         end

(* Finds and proves contradiction among ge-relations
 *)
let arithT = arithRelInConcl2HypT thenMT
   (onAllHypsT anyArithRel2geT)
   thenMT (onAllHypsT tryReduce_geT)
   thenMT findContradRelT
   thenMT reduceContradRelT (-1)

interactive test 'H 'a 'b 'c :
sequent [squash] { 'H >- 'a IN int } -->
sequent [squash] { 'H >- 'b IN int } -->
sequent ['ext] { 'H; x: ('a >= ('b +@ 1));
                     t: ('c >= ('b +@ 3));
                     u: ('b >= ('a +@ 0))
                >- "assert"{bfalse} }

interactive test2 'H 'a 'b 'c :
sequent [squash] { 'H >- 'a IN int } -->
sequent [squash] { 'H >- 'b IN int } -->
sequent ['ext] { 'H; x: (('b +@ 1) <= 'a);
                     t: ('c > ('b +@ 2));
                     u: ('b >= ('a +@ 0))
                >- "assert"{bfalse} }

interactive test3 'H 'a 'b 'c :
sequent [squash] { 'H >- 'a IN int } -->
sequent [squash] { 'H >- 'b IN int } -->
sequent ['ext] { 'H; x: (('b +@ 1) <= 'a);
                     t: ('c > ('b +@ 2))
                >- ('b < ('a +@ 0))  }

interactive test4 'H 'a 'b :
sequent [squash] { 'H >- 'a IN int } -->
sequent [squash] { 'H >- 'b IN int } -->
sequent ['ext] { 'H; x: ('a >= 'b);
                     t: ('a < 'b)
                >- "assert"{bfalse} }

interactive test5 'H 'a 'b :
sequent [squash] { 'H >- 'a IN int } -->
sequent [squash] { 'H >- 'b IN int } -->
sequent ['ext] { 'H; x: ('a >= 'b +@ 0);
                     t: ('a < 'b)
                >- "assert"{bfalse} }

interactive test6 'H 'a 'b 'c :
sequent [squash] { 'H >- 'a IN int } -->
sequent [squash] { 'H >- 'b IN int } -->
sequent [squash] { 'H >- 'c IN int } -->
sequent ['ext] { 'H; x: (('c *@ ('b +@ ('a *@ 'c)) +@ ('b *@ 'c)) >= 'b +@ 0);
                     t: (((((('c *@ 'b) *@ 1) +@ (2 *@ ('a *@ ('c *@ 'c)))) +@ (('c *@ ((-1) *@ 'a)) *@ 'c)) +@ ('b *@ 'c)) < 'b)
                >- "assert"{bfalse} }
