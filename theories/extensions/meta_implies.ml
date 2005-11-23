(*
 * Add terms and ML rules for higher-order rules.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2005 Mojave Group, Caltech
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
 * Author: Jason Hickey
 * @email{jyh@cs.caltech.edu}
 * @end[license]
 *)
extends Base_theory
extends Meta_util
extends Meta_dtactic

open Lm_printf

open Simple_print
open Basic_tactics
open Refiner.Refiner.Refine

open Base_meta
open Meta_util

(************************************************************************
 * Terms.
 *)

(*
 * The meta-implication.
 *)
declare mimplies{'premise : Judgment; 'rest : Judgment} : Judgment

(*
 * The extract term.
 *)
declare mlambda{x. 'e['x]}
declare mapply{'e1; 'e2}

(************************************************************************
 * Display forms.
 *)
dform mimplies_df : mimplies{'e1; 'e2} =
   szone pushm[0] slot{'e1} hspace Mpsymbols!longrightarrow `" " slot{'e2} popm ezone

(************************************************************************
 * Term operations.
 *)
let mimplies_opname = opname_of_term << mimplies{'e1; 'e2} >>
let mk_mimplies_term = mk_dep0_dep0_term mimplies_opname
let dest_mimplies_term = dest_dep0_dep0_term mimplies_opname

let mlambda_opname = opname_of_term << mlambda{x. 'e} >>
let mk_mlambda_term = mk_dep1_term mlambda_opname
let dest_mlambda_term = dest_dep1_term mlambda_opname

let mapply_opname = opname_of_term << mapply{'e1; 'e2} >>
let mk_mapply_term = mk_dep0_dep0_term mapply_opname
let dest_mapply_term = dest_dep0_dep0_term mapply_opname

(************************************************************************
 * ML rules.
 *
 * These are ML rules only because the extracts are not
 * expressible in the normal meta-logic.
 *)

(*
 * Introduction rule.
 *
 *     S1 --> ... --> Sn --> T1 --> T2
 *     --------------------------------- [intro]
 *     S1 --> ... --> Sn --> (T1 ==> T2)
 *
 * JYH: I need to check this.  I assume subgoals refers
 * to the extract of the upper rule, and we need to
 * compute an extract for the lower rule.  The main
 * issue is that I need to know what the extract
 * for a rule looks like.
 *
 * For the moment, this is completely wrong.
 *)
let mimplies_intro_extract addrs params goal subgoals =
   let subgoals, ext = Lm_list_util.split_last subgoals in
   let v = dest_var ext in
      mk_mlambda_term v goal

let mimplies_intro_code addrs params goal assums =
   let t1, t2 = dest_mimplies_term goal in
   let seq = mk_msequent t2 (assums @ [t1]) in
      [seq], mimplies_intro_extract

ml_rule mimplies_intro : mimplies{'t1; 't2} =
   mimplies_intro_code

(*
 * Elimination rule.
 *
 *     S1 --> ... --> (T1 ==> T2) --> ... --> T1
 *     S1 --> ... --> (T1 ==> T2) --> ... --> T1 -->  Sn
 *     ------------------------------------------------- [elim]
 *     S1 --> ... --> (T1 ==> T2) --> ... --> Sn
 *
 * JYH: this should be checked.  We build a function
 * by quantifying over T1, which must be a variable.
 *)
let mimplies_elim_extract addrs params goal subgoals =
   let subgoals, ext = Lm_list_util.split_last subgoals in
   let v = dest_var ext in
      mk_mlambda_term v goal

let mimplies_elim_code addrs params goal assums =
   eprintf "mimplies_elim_code@.";
   let i = get_pos_assum_from_params params assums in
   let t = nth_assum assums i in
   let t1, t2 = dest_mimplies_term t in
   let seq1 = mk_msequent t1 assums in
   let seq2 = mk_msequent goal (assums @ [t2]) in
      [seq1; seq2], mimplies_elim_extract

ml_rule mimplies_elim_rule 'i : 'T =
   mimplies_elim_code

let mimplies_elim i =
   eprintf "mimplies_elim@.";
   mimplies_elim_rule (mk_meta_num i)

(************************************************************************
 * Resources.
 *)
let resource meta_intro +=
   [<< mimplies{'e1; 'e2} >>, wrap_intro mimplies_intro]

let resource meta_elim +=
   [<< mimplies{'e1; 'e2} >>, mimplies_elim]

(************************************************************************
 * Tests.
 *)
interactive test1 'S :
   sequent { <H> >- 'S } -->
   mimplies{sequent { <H> >- 'S }; sequent { <H> >- 'T }} -->
   sequent { <H> >- 'T }

interactive test2 :
   mimplies{sequent { <H> >- 'S }; sequent { <H> >- 'T }} -->
   mimplies{sequent { <H> >- 'S }; sequent { <H> >- 'T }}

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
