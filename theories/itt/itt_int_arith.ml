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
open Base_auto_tactic

open Itt_equal
open Itt_struct

open Itt_int_base
open Itt_int_ext

let _ = show_loading "Loading Itt_int_ext%t"

(*******************************************************
 * ARITH
 *******************************************************)

interactive ge_addMono 'H :
   sequent [squash] { 'H >- 'a IN int } -->
   sequent [squash] { 'H >- 'b IN int } -->
   sequent [squash] { 'H >- 'c IN int } -->
   sequent [squash] { 'H >- 'd IN int } -->
   sequent [squash] { 'H >- 'a >= 'b } -->
   sequent [squash] { 'H >- 'c >= 'd } -->
   sequent ['ext] { 'H >- ('a +@ 'c) >= ('b +@ 'd) }

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

let proveSumT p =
   (ge_addMono (Sequent.hyp_count_addr p) thenAT autoT) p

let sumListT l p =
   let s = sumList l (Sequent.goal p) in
   (assertT s thenAT (progressT proveSumT)) p

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

let arithT p =
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
            List.map aux rl;
            sumListT rl p
         end
      | Arith.TG.Disconnected,_ ->
         begin
            eprintf "No contradiction found";
            failT p
         end

interactive test 'H 'a 'b 'c :
sequent [squash] { 'H >- 'a IN int } -->
sequent [squash] { 'H >- 'b IN int } -->
sequent ['ext] { 'H; x: ('a >= ('b +@ 1));
                     y: (5 IN int);
                     z: (6 IN int);
                     t: ('c >= ('b +@ 3));
                     u: ('b >= ('a +@ 0))
                >- "assert"{bfalse} }
