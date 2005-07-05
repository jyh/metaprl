doc <:doc<
   @spelling{bi}
   @module[s4_logic]

   @docoff
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

   Author : Yegor Bryukhov @email{ybryukhov@conrell.edu}

   @end[license]
>>

doc <:doc<
   @parents
>>

extends Base_theory

open Lm_debug
open Lm_printf
open Simple_print

open Browser_resource

open Basic_tactics

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading s4_logic%t"

let debug_s4prover =
   create_debug (**)
      { debug_name = "s4prover";
        debug_description = "Display S4-Jprover operations";
        debug_value = false
      }

declare default_extract
declare it
declare typeclass Proposition -> Term
declare sequent { Proposition : Term >- Judgment } : Judgment
declare sequent [concl] { Proposition : Term >- Term } : Judgment
declare sequent [boxed] { Proposition : Term >- Term } : Judgment

declare "true" : Proposition
declare "false" : Proposition
declare "not"{'a} : Proposition
declare "and"{'a; 'b} : Proposition
declare "or"{'a; 'b} : Proposition
declare "implies"{'a; 'b} : Proposition
declare "box"{'a} : Proposition

prim ax 'H 'K :
   sequent { <#H>; 'a; <#J> >- concl{| <#K>; 'a; <#L> >- it |} }

prim ax_false 'H :
   sequent { <#H>; "false"; <#J> >- concl{| <#K> >- it |} }

prim not_intro 'J :
   sequent { <#H>; 'a >- concl{| <#J>; <#K> >- it |} } -->
   sequent { <#H> >- concl{| <#J>; "not"{'a}; <#K> >- it |} }

prim not_elim 'H :
   sequent { <#H>; <#J> >- concl{| <#K>; 'a >- it|} } -->
   sequent { <#H>; "not"{'a}; <#J> >- concl{| <#K> >- it|} }

prim and_intro 'J :
   sequent { <#H> >- concl{| <#J>; 'a; <#K> >- it |} } -->
   sequent { <#H> >- concl{| <#J>; 'b; <#K> >- it |} } -->
   sequent { <#H> >- concl{| <#J>; 'a & 'b; <#K> >- it |} }

prim and_elim 'H :
   sequent { <#H>; 'a; 'b; <#J> >- concl{| <#K> >- it|} } -->
   sequent { <#H>; 'a & 'b; <#J> >- concl{| <#K> >- it|} }

prim or_intro 'J :
   sequent { <#H> >- concl{| <#J>; 'a; 'b; <#K> >- it |} } -->
   sequent { <#H> >- concl{| <#J>; 'a or 'b; <#K> >- it |} }

prim or_elim 'H :
   sequent { <#H>; 'a; <#J> >- concl{| <#K> >- it|} } -->
   sequent { <#H>; 'b; <#J> >- concl{| <#K> >- it|} } -->
   sequent { <#H>; 'a or 'b; <#J> >- concl{| <#K> >- it|} }

prim implies_intro 'J :
   sequent { <#H>; 'a >- concl{| <#J>; 'b; <#K> >- it |} } -->
   sequent { <#H> >- concl{| <#J>; 'a => 'b; <#K> >- it |} }

prim implies_elim 'H :
   [assertion] sequent { <#H>; 'a => 'b; <#J> >- concl{| <#K>; 'a >- it |} } -->
   sequent { <#H>; 'a => 'b; <#J>; 'b >- concl{| <#K> >- it|} } -->
   sequent { <#H>; 'a => 'b; <#J> >- concl{| <#K> >- it|} }

prim box_elim 'H :
   sequent { <#H>; 'a; box{'a}; <#J> >- concl{| <#K> >- it|} } -->
   sequent { <#H>; box{'a}; <#J> >- concl{| <#K> >- it|} }

prim box_intro 'J :
   [aux] sequent { >- boxed{| <#H> >- it |} } -->
   sequent { <#H> >- concl{| 'a >- it |} } -->
   sequent { <#H> >- concl{| <#J>; box{'a}; <#K> >- it |} }

prim thin 'H :
   sequent { <#H>; <#J> >- 'C } -->
   sequent { <#H>; 'a; <#J> >- 'C }

prim boxed_step :
   sequent { >- boxed{| <#H> >- it |} } -->
   sequent { >- boxed{| box{'a}; <#H> >- it |} }

prim boxed_base :
   sequent { >- boxed{| >- it |} }

(************************************************************************
 * DISPLAY FORMS							*
 ************************************************************************)

prec prec_implies
prec prec_and
prec prec_or
prec prec_not

prec prec_implies < prec_or
prec prec_or < prec_and
prec prec_and < prec_not

dform true_df : except_mode[src] :: "true" =
   `"True"

dform false_df : except_mode[src] :: "false" =
   `"False"

dform not_df1 : except_mode[src] :: parens :: "prec"[prec_not] :: "not"{'a} =
   Nuprl_font!tneg slot["le"]{'a}

dform not_df2 : mode[src] :: parens :: "prec"[prec_implies] :: "not"{'a} =
   `"\"not\"{" 'a `"}"

(*
 * Implication.
 *)
declare implies_df{'a : Dform } : Dform

dform implies_df1 : parens :: "prec"[prec_implies] :: mode[src] :: mode[prl] :: mode[html] :: mode[tex] :: "implies"{'a; 'b} =
   szone pushm[0] slot["le"]{'a} implies_df{'b} popm ezone

dform implies_df2 : mode[src] :: mode[prl] :: mode[html] :: mode[tex] :: implies_df{"implies"{'a; 'b}} =
   implies_df{'a} implies_df{'b}

dform implies_df3 : mode[src] :: mode[prl] :: mode[html] :: mode[tex] :: implies_df{'a} =
   hspace Nuprl_font!Rightarrow `" " slot{'a}

(*
 * Disjunction.
 *)
declare or_df{'a : Dform } : Dform

dform or_df1 : parens :: "prec"[prec_or] :: mode[src] :: mode[prl] :: mode[html] :: mode[tex] :: "or"{'a; 'b} =
   szone pushm[0] slot["le"]{'a} or_df{'b} popm ezone

dform or_df2 : mode[src] :: mode[prl] :: mode[html] :: mode[tex] :: or_df{"or"{'a; 'b}} =
   or_df{'a} or_df{'b}

dform or_df3 : mode[src] :: mode[prl] :: mode[html] :: mode[tex] :: or_df{'a} =
   hspace Nuprl_font!vee `" " slot{'a}

(*
 * Conjunction.
 *)
declare and_df{'a : Dform } : Dform

dform and_df1 : parens :: "prec"[prec_and] :: mode[src] :: mode[prl] :: mode[html] :: mode[tex] :: "and"{'a; 'b} =
   szone pushm[0] slot["le"]{'a} and_df{'b} popm ezone

dform and_df2 : mode[src] :: mode[prl] :: mode[html] :: mode[tex] :: and_df{"and"{'a; 'b}} =
   and_df{'a} and_df{'b}

dform and_df3 : mode[src] :: mode[prl] :: mode[html] :: mode[tex] :: and_df{'a} =
   hspace Nuprl_font!wedge `" " slot{'a}

(*
 * Box
 *)
dform box_df1 : except_mode[src] :: parens :: "prec"[prec_not] :: box{'a} =
   `"[]" slot["lt"]{'a}

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let false_term = << "false" >>
let is_false_term = is_no_subterms_term (opname_of_term false_term)

let or_term = << 'A or 'B >>
let or_opname = opname_of_term or_term
let is_or_term = is_dep0_dep0_term or_opname
let dest_or = dest_dep0_dep0_term or_opname
let mk_or_term = mk_dep0_dep0_term or_opname

let and_term = << 'A and 'B >>
let and_opname = opname_of_term and_term
let is_and_term = is_dep0_dep0_term and_opname
let dest_and = dest_dep0_dep0_term and_opname
let mk_and_term = mk_dep0_dep0_term and_opname

let implies_term = << 'A => 'B >>
let implies_opname = opname_of_term implies_term
let is_implies_term = is_dep0_dep0_term implies_opname
let dest_implies = dest_dep0_dep0_term implies_opname
let mk_implies_term = mk_dep0_dep0_term implies_opname

let not_term = << "not"{'a} >>
let not_opname = opname_of_term not_term
let is_not_term = is_dep0_term not_opname
let dest_not = dest_dep0_term not_opname
let mk_not_term = mk_dep0_term not_opname

let box_term = << box{'a} >>
let box_opname = opname_of_term box_term
let is_box_term = is_dep0_term box_opname
let dest_box = dest_dep0_term box_opname
let mk_box_term = mk_dep0_term box_opname

let rec thin_nonboxed_aux i p =
   if i > Sequent.hyp_count p then
      idT
   else
      let hyp = Sequent.nth_hyp p i in
      if is_box_term hyp then
         funT (fun p -> thin_nonboxed_aux (succ i) p)
      else
         thin i thenT funT (fun p -> thin_nonboxed_aux i p)

let thin_nonboxedT = funT (fun p -> thin_nonboxed_aux 1 p)

let prove_boxedT = repeatT boxed_step thenT boxed_base

let box_introT i =
   thin_nonboxedT thenT box_intro i thenAT prove_boxedT

(************ logic instance for j-prover in refiner/reflib/jall.ml  **********)

module S4_Logic =
struct
   open Jlogic_sig

   let is_and_term t = is_and_term t
   let dest_and t = dest_and t
   let is_or_term = is_or_term
   let dest_or = dest_or
   let is_implies_term = is_implies_term
   let dest_implies = dest_implies
   let is_not_term = is_not_term
   let dest_not = dest_not

   let is_box_term = is_box_term
   let dest_box t = dest_box t

   let is_exists_term _ = false
   let dest_exists _ = raise (Invalid_argument "S4 is propositional logic")
   let is_all_term _ = false
   let dest_all t = dest_exists t

   type inference = tactic list
   let empty_inf = []

   let find_hyp term tac = funT (fun p ->
      if !debug_s4prover then
         eprintf "hyp: %a@." print_term term;
      let hyps = (explode_sequent_arg p).sequent_hyps in
      let len = SeqHyp.length hyps in
      let rec aux i =
         if i = len then
            raise (RefineError("s4_logic.S4_Logic.find_hyp failed",
                     TermError(goal p)))
         else match SeqHyp.get hyps i with
            Hypothesis(_,t) when alpha_equal t term -> tac (i+1)
          | _ -> aux (i+1)
      in
         aux 0
   )

   let find_concl term tac = funT (fun p ->
      if !debug_s4prover then
         eprintf "concl: %a@." print_term term;
      let concl = (explode_sequent_arg p).sequent_concl in
      let concls = (TermMan.explode_sequent concl).sequent_hyps in
      let len = SeqHyp.length concls in
      let rec aux i =
         if i = len then
            raise (RefineError("s4_logic.S4_Logic.find_concl failed",
                     TermError(concl)))
         else match SeqHyp.get concls i with
            Hypothesis(_,t) when alpha_equal t term -> tac (i+1)
          | _ -> aux (i+1)
      in
         aux 0
   )

   let thenTi tac1 tac2 i = tac1 i thenT tac2
   let thenLTi tac1 tacl i = tac1 i thenLT tacl
   let aTi tac t i = tac i t

   let hypothesis = argfunT (fun i p ->
      let t = Sequent.nth_hyp p i in
      if alpha_equal t false_term then
         ax_false i
      else
         find_concl t (ax i)
   )

   let append_inf inf hyp _ r =
      match r, inf with
         Ax,  _ -> (find_hyp hyp hypothesis) :: inf
       | Andl,t::ts -> (find_hyp hyp (thenTi and_elim t)) :: ts
       | Negl,t::ts -> (find_hyp hyp (thenTi not_elim t)) :: ts
       | Orl, t1::t2::ts ->
            (find_hyp hyp (thenLTi or_elim [t1; t2])) :: ts
       | Impl,t1::t2::ts ->
               (find_hyp hyp (thenLTi implies_elim [t1; t2])) :: ts
       | Andr,t1::t2::ts ->
               (find_concl hyp (thenLTi and_intro [t1; t2])) :: ts
       | Impr,t::ts ->
               (find_concl hyp (thenTi implies_intro t)) :: ts
       | Negr,t::ts ->
               (find_concl hyp (thenTi not_intro t)) :: ts
       | Orr, t::ts ->
               (find_concl hyp (thenTi or_intro t))
            :: ts
       | Boxr,t::ts ->
               (find_concl hyp (thenTi box_introT t))
            :: ts
       | Boxl,t::ts ->
               (find_hyp hyp (thenTi box_elim t))
            :: ts
       | Fail,_ -> raise (RefineError("S4_Logic.create_inf", StringError "failed"))
       | _ ->
             raise (Invalid_argument "S4_Logic.create_inf")
end

module S4_Prover = Jall.JProver(S4_Logic)

let rec all_hyps_aux hyps l i =
   if i = 0 then l else
   let i = pred i in
      match Term.SeqHyp.get hyps i with
         Hypothesis (_, t) ->
            all_hyps_aux hyps (t::l) i
       | Context _ ->
            all_hyps_aux hyps l i

let all_hyps t =
   let hyps = (TermMan.explode_sequent t).sequent_hyps in
      all_hyps_aux hyps [] (Term.SeqHyp.length hyps)

let base_proverT def_mult = funT (fun p ->
   let mult_limit =
      match Sequent.get_int_arg p "s4prover" with
         None -> def_mult
       | Some _ as ml -> ml
   in
   let goal = Sequent.goal p in
   let seq = TermMan.explode_sequent goal in
   let hyps = Sequent.all_hyps p in
   let concl = seq.sequent_concl in
   let concls = all_hyps concl in
   match
      S4_Prover.gen_prover mult_limit Jlogic_sig.S4 hyps concls
   with
      [t] -> t
    | _ -> raise (Invalid_argument "Problems decoding S4_Prover.prover proof"))

let simple_proverT = base_proverT (Some 1)
let proverT = base_proverT (Some 100)

(* TESTS *)

interactive refl0 :
   sequent { box{'a} >- concl {| 'a >- it |} }

interactive refl 'J :
   sequent { >- concl {| <#J>; box{'a} => 'a; <#K> >- it |} }

interactive trans 'J :
   sequent { >- concl {| <#J>; box{'a} => box{box{'a}}; <#K> >- it |} }

interactive norm 'J :
   sequent { >- concl {| <#J>; box{'a => 'b} => box{'a} => box{'b}; <#K> >- it |} }

interactive nec_test :
   sequent { 'c; box{'a}; 'b; box{'b}; 'd >- concl {| box{box{'a}} >- it |} }

interactive selfref :
   sequent { >- concl {| "not"{box{"not"{'a => box{'a}}}} >- it |} }

interactive and_commute1 'J :
   sequent { >- concl {| <#J>; (box{'a} & box{'b}) => box{'a & 'b}; <#K> >- it |} }

interactive and_commute2 'J :
   sequent { >- concl {| <#J>; box{'a & 'b} => (box{'a} & box{'b}); <#K> >- it |} }

interactive box_k 'J :
   sequent { >- concl {| <#J>; box{'a => 'a}; <#K> >- it |} }

interactive box_box_k 'J :
   sequent { >- concl {| <#J>; box{box{'a => 'a}}; <#K> >- it |} }

interactive or_commute 'J :
   sequent { >- concl {| <#J>; (box{'a} or box{'b}) => box{'a or 'b}; <#K> >- it |} }
