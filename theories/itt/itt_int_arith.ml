(*!
 * @spelling{arithT tactic implementation}
 *
 * @begin[doc]
 * @theory[Itt_int_arith]
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

include Itt_equal
include Itt_rfun
include Itt_logic
include Itt_bool
include Itt_int_ext
(*! @docoff *)

open Printf
open Mp_debug
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
(* open Base_auto_tactic *)

open Top_conversionals

open Itt_equal
open Itt_struct

open Itt_int_base
open Itt_int_ext

let _ = show_loading "Loading Itt_int_ext%t"

(*******************************************************
 * ARITH
 *******************************************************)

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
   if i<>1 then
      let g=Sequent.goal p in
      let (_,t)=Refiner.Refiner.TermMan.nth_hyp g i in
      if is_le_term t then le2geT t p
      else if is_lt_term t then lt2geT t p
      else if is_gt_term t then gt2geT t p
      else if is_equal_term t then
         let (tt,l,r)=dest_equal t in
            if tt=int_term then
               (eq2geT t p)
            else
	       idT p
      else
         idT p
   else
      idT p

(*
   else if is_not_term t then
      let t1=dest_not t in
         if is_ge_term t1 then notge2geT t1
         else if is_le_term t1 then notle2geT t1
         else if is_lt_term t1 then notlt2geT t1
         else if is_gt_term t1 then notgt2geT t1
*)

interactive ge_addMono 'H :
   sequent [squash] { 'H >- 'a IN int } -->
   sequent [squash] { 'H >- 'b IN int } -->
   sequent [squash] { 'H >- 'c IN int } -->
   sequent [squash] { 'H >- 'd IN int } -->
   sequent [squash] { 'H >- 'a >= 'b } -->
   sequent [squash] { 'H >- 'c >= 'd } -->
   sequent ['ext] { 'H >- ('a +@ 'c) >= ('b +@ 'd) }

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
	          (add_AssocC thenC (addrC [0] reduce_add))
	       else
                  if b<a then
                     add_BubblePrimitiveC
                  else
                     idC
         else
            if (is_number_term a) & (is_number_term s) then
	       reduce_add
	    else
(* it is incorrect here to compare terms this way because
result depends on term internal representation. We have to
implement some kind of term ordering and use it here *)
               if s<a then
	          add_CommutC
	       else
	          idC
   else
      failC

(* here we apply add_BubbleStepC as many times as possible thus
   finally we have all sum subterms positioned in order
 *)
let add_BubbleSortC = sweepDnC (termC add_BubbleStepC)

(* Before terms sorting we have to put parentheses in the rightmost-first
manner
 *)
let add_normalizeC = (sweepDnC add_Assoc2C) thenC (whileProgressC
 add_BubbleSortC)

interactive_rw ge_addContract_rw :
   ( 'a IN int ) -->
   ( 'b IN int ) -->
   ('a >= ('b +@ 'a)) <--> (0 >= 'b)

let ge_addContractC = ge_addContract_rw

(* Reduce contradictory relation a>=a+b where b>0. autoT should be removed
later to permit incorporation of this tactic into autoT.
 *)
let reduceContradRelT i p = ((rw ((addrC [0] add_normalizeC) thenC
                               (addrC [1] add_normalizeC) thenC
			       ge_addContractC thenC
			       reduceC)
                              i)) p

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
   if is_ge_term t then
     let (_,b)=dest_ge t in
        if is_add_term b then
           let (_,d)=dest_add b in
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
(*  (List.map (fun x->let (_,t)=(Refiner.Refiner.TermMan.nth_hyp g x)
                     in print_term stdout t) l;
*)
   let ar=Array.of_list l in
   match Arith.TG.solve (g,ar) with
      Arith.TG.Int (_,r),_ ->
         let aux i = eprintf "i=%u " i in
         let aux2 i = eprintf "r=%u " ar.(i) in
         let aux3 i al = (ar.(i))::al in
         let rl = List.fold_right aux3 r [] in
         begin
            List.map aux l;
            prerr_endline "";
            List.map aux rl;
            flush stderr;
            sumListT rl p
         end
      | Arith.TG.Disconnected,_ ->
         begin
            eprintf "No contradiction found";
            failT p
         end

(* Finds and proves contradiction among ge-relations
 *)
let arithT = (onAllHypsT anyArithRel2geT)
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
