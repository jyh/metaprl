doc <:doc<
   @begin[doc]
   @module[Itt_int_arith]

	This module defines @hrefconv[normalizeC] and @hreftactic[arithT].

   @noindent @hrefconv[normalizeC] converts polynomials to the canonical form.

   @noindent @hreftactic[arithT] proves simple inequalities.
   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.

   Copyright (C) 2003 Yegor Bryukhov, GC CUNY

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

   Author: Yegor Bryukhov
   @email{ynb@mail.ru}
   @end[license]
>>
extends Itt_equal
extends Itt_rfun
extends Itt_logic
extends Itt_bool
extends Itt_int_ext
doc docoff

open Lm_debug
open Lm_printf
open Lm_num

open Term_order
open Simple_print
open Term_match_table

open Basic_tactics

open Itt_equal
open Itt_struct
open Itt_logic
open Itt_bool

open Itt_int_base
open Itt_int_ext
open Itt_dprod

module TO = TermOrder (Refiner.Refiner)
open TO

let _ = show_loading "Loading Itt_int_ext%t"

let debug_int_arith =
   create_debug (**)
      { debug_name = "debug_int_arith";
        debug_description = "Print out some debug info as tactics proceed";
        debug_value = false
      }

let debug_arith_dtactic =
   create_debug (**)
      { debug_name = "debug_arith_dtactic";
        debug_description = "display operations of conversion to >=";
        debug_value = false
      }

(*******************************************************
 * ARITH
 *******************************************************)

let identity x = x

type ge_elim_type = int -> tactic_arg -> (term list * (int -> tactic))
type ge_intro_type = tactic_arg -> (term list * tactic)

let extract_ge_elim_data tbl i p =
	let t = mk_pair_term (mk_var_term (Sequent.nth_binding p i)) (Sequent.nth_hyp p i) in
   if !debug_arith_dtactic then
		eprintf "Itt_int_arith.ge_elim: lookup %s%t" (SimplePrint.short_string_of_term t) eflush;
	let terms, tac = Term_match_table.lookup_rmap tbl select_all t in
	terms, tac

let extract_ge_intro_data tbl p =
   let t = Sequent.goal p in
   if !debug_arith_dtactic then
		eprintf "Itt_int_arith.ge_intro: lookup %s%t" (SimplePrint.short_string_of_term t) eflush;
	let terms, tac = Term_match_table.lookup_rmap tbl select_all t in
	terms, tac

let resource (term * (term list) * (int -> tactic), ge_elim_type) ge_elim =
   rmap_table_resource_info extract_ge_elim_data

let resource (term * (term list) * tactic, ge_intro_type) ge_intro =
   rmap_table_resource_info extract_ge_intro_data

let rec filter_ge = function
	Hypothesis(v,t)::tl when (is_ge_term t) -> t::(filter_ge tl)
 | _::tl -> filter_ge tl
 | [] -> []

let main_labels = ""::main_labels

let rec on_main_subgoals = function
	(labels,_,seq)::tl ->
		if !debug_arith_dtactic then
			eprintf "Itt_int_arith.ge_elim: on_main_subgoals labels: %s%t" (String.concat ";" labels) eflush;
		(*if List.exists (fun x -> List.mem x labels) main_labels then*)
			let hyps=SeqHyp.to_list (TermMan.explode_sequent seq).sequent_hyps in
			let ge_hyps=filter_ge hyps in
			if ge_hyps=[] then
				on_main_subgoals tl
			else
				let seq_terms = mk_xlist_term ge_hyps in
				if !debug_arith_dtactic then
					eprintf "Itt_int_arith.ge_elim: on_main_subgoals >= terms: %s%t" (SimplePrint.short_string_of_term seq_terms) eflush;
				seq_terms::(on_main_subgoals tl)
		(*else
			on_main_subgoals tl*)
 | [] -> []

let process_ge_elim_resource_annotation name context_args term_args statement pre_tactic =
   let assums, goal = unzip_mfunction statement in
	let _=if !debug_arith_dtactic then
			let l = SeqGoal.to_list (TermMan.explode_sequent goal).sequent_goals in
				eprintf "Itt_int_arith.improve_ge_elim: %s goal: %s%t" name (SimplePrint.short_string_of_term (List.hd l)) eflush
	in
   let v,t =
      match SeqHyp.to_list (TermMan.explode_sequent goal).sequent_hyps with
         [ Context _; Hypothesis(v,t); Context _ ] -> v,t
       | _ ->
            raise (Invalid_argument (sprintf "Itt_int_arith.improve_ge_elim: %s: must be an elimination rule" name))
   in
   let seq_terms = on_main_subgoals assums in
	let tac = argfunT (fun i p -> Tactic_type.Tactic.tactic_of_rule pre_tactic [| i |] []) in
   (mk_pair_term (mk_var_term v) t), seq_terms, tac

let process_ge_intro_resource_annotation name context_args term_args statement pre_tactic =
   let assums, goal = unzip_mfunction statement in
   let t =
      match SeqGoal.to_list (TermMan.explode_sequent goal).sequent_goals with
         [ t ] ->
				if !debug_arith_dtactic then
					eprintf "Itt_int_arith.improve_ge_intro: %s goal: %s%t" name (SimplePrint.short_string_of_term t) eflush;
				t
       | _ ->
            raise (Invalid_argument (sprintf "Itt_int_arith.improve_ge_intro: %s: only one goal is supported" name))
   in
   let seq_terms = on_main_subgoals assums in
	let tac = funT (fun p -> Tactic_type.Tactic.tactic_of_rule pre_tactic [| |] []) in
   t, seq_terms, tac

let hyp2geT = argfunT (fun i p ->
	try
		let _,tac=Sequent.get_resource_arg p get_ge_elim_resource (Sequent.get_pos_hyp_num p i) p in
		tac i
	with Not_found ->
		idT
 | RefineError _ ->
		idT
)

let concl2geT = funT (fun p ->
	try
		let _,tac=Sequent.get_resource_arg p get_ge_intro_resource p in
		tac
	with Not_found ->
		idT
)

let all2geT = onAllMHypsT hyp2geT

let rec all_hyps_aux hyps l i =
   if i = 0 then l else
   let j = pred i in
      match SeqHyp.get hyps j with
         Hypothesis (_, t) ->
				eprintf "hyp %i %s%t" j (SimplePrint.short_string_of_term t) eflush;
            all_hyps_aux hyps ((j+1,t)::l) j
       | Context _ ->
            all_hyps_aux hyps l j

let all_hyps arg =
   let hyps = (Sequent.explode_sequent arg).sequent_hyps in
	let len = Term.SeqHyp.length hyps in
		eprintf "num of hyps %i%t" len eflush;
      all_hyps_aux hyps [] len

let rec append tac len pos l = function
	t::tail ->
		append tac len (succ pos) ((t,pos,len,tac)::l) tail
 | [] -> l

let rec hyp2ge p l = function
	(i,t)::tail ->
		if !debug_arith_dtactic then
			eprintf "Itt_int_arith.hyp2ge: looking for %ith hyp %s%t" i (SimplePrint.short_string_of_term t) eflush;
		if is_member_term t then
			hyp2ge p l tail
		else if is_ge_term t then
			hyp2ge p ((t,i,0,idT)::l) tail
		else
			(try
				if !debug_arith_dtactic then
					eprintf "Itt_int_arith.hyp2ge: searching ge_elim resource%t" eflush;
				let terms,tac=Sequent.get_resource_arg p get_ge_elim_resource (Sequent.get_pos_hyp_num p i) p in
				match terms with
					[t] ->
						if !debug_arith_dtactic then
							eprintf "Itt_int_arith.hyp2ge: found %s%t" (SimplePrint.short_string_of_term t) eflush;
						let terms=dest_xlist t in
						let len=List.length terms in
						let pos= -len in
						let l'=append (tac i) len pos l terms in
						hyp2ge p l' tail
				 | _ -> raise (Invalid_argument "Itt_int_arith: branching is not supported yet")
			with Not_found ->
				if !debug_arith_dtactic then
					eprintf "Itt_int_arith.hyp2ge: looking for %ith hyp %s - not found%t" i (SimplePrint.short_string_of_term t) eflush;
				hyp2ge p l tail)
 | [] -> l

let concl2ge p =
	try
		let terms,tac=Sequent.get_resource_arg p get_ge_intro_resource p in
		match terms with
			[t] ->
				let terms = dest_xlist t in
				let len=List.length terms in
				let pos= -len in
				append tac len pos [] terms
		 | _ -> raise (Invalid_argument "Itt_int_arith: branching is not supported yet")
	with Not_found -> []

let allhyps2ge p tail =
	hyp2ge p tail (all_hyps p)

let all2ge p =
	(*let pos, l = concl2ge p (succ (Sequent.hyp_count p)) in*)
	let l = allhyps2ge p [] in
	if !debug_arith_dtactic then
		eprintf "Itt_int_arith.all2ge: %i inequalities collected%t" (List.length l) eflush;
	l
	(*List.sort (fun x y -> (List.length(fst x))-(List.length(fst y))) l*)

(*let prefix e l = List.map (fun x -> e::x) l

let rec product l = function
	hd::tl ->
		let l=list_product l in
		(prefix hd l)::(product l tl)
 | [e] -> prefix e (list_product l)
 | [] -> raise (Invalid_argument "Itt_int_arith.product: ge_elim/ge_intro entry produced an empty >=-list")

and list_product = function
	hd::tl -> product tl hd
 | [l] -> l
 | [] -> []

let all2ge_flat p =
	list_product (all2ge p)
*)

(*
let testT = argfunT (fun i p ->
   if i = 0 then
      (*let _=Sequent.get_resource_arg p get_ge_intro_resource in*)
		failT
   else
      let f = Sequent.get_resource_arg p get_ge_elim_data_resource in
		let t = Sequent.nth_hyp p i in
		let t' = f i p in
		eprintf "%a -> %a%t" print_term t print_term t' eflush;
		idT
)
*)

interactive le2ge {| ge_elim |} 'H :
   [wf] sequent { <H>; x: 'a < 'b; <J['x]> >- 'a in int } -->
   [wf] sequent { <H>; x: 'a < 'b; <J['x]> >- 'b in int } -->
   [main] sequent { <H>; x: 'a <= 'b; <J['x]>; 'b >= 'a >- 'C['x] } -->
   sequent { <H>; x: 'a <= 'b; <J['x]> >- 'C['x] }

interactive lt2ge {| ge_elim |} 'H :
   [wf] sequent { <H>; x: 'a < 'b; <J['x]> >- 'a in int } -->
   [wf] sequent { <H>; x: 'a < 'b; <J['x]> >- 'b in int } -->
   [main] sequent { <H>; x: 'a < 'b; <J['x]>; 'b >= ('a +@ 1) >- 'C['x] } -->
   sequent { <H>; x: 'a < 'b; <J['x]> >- 'C['x] }

interactive ltb2ge {| ge_elim |} 'H :
   [wf] sequent { <H>; x: "assert"{'a <@ 'b}; <J[it]> >- 'a in int } -->
   [wf] sequent { <H>; x: "assert"{'a <@ 'b}; <J[it]> >- 'b in int } -->
   [main] sequent { <H>; x: "assert"{'a <@ 'b}; <J['x]>; 'b >= ('a +@ 1) >- 'C['x] } -->
   sequent { <H>; x: "assert"{'a <@ 'b}; <J['x]> >- 'C['x] }

(*
let resource ge_elim_data += [
	<<'a < 'b>>, (fun l i p -> (match l with [a;b] -> mk_ge_term b (mk_add_term a <<1>>) | _ -> <<0>>));
]
*)

(*let lt2ge_term l i p =
	match l with
		[a;b] -> mk_ge_term b (mk_add_term a <<1>>)
	 | _ -> <<0>>*)

interactive gt2ge {| ge_elim |} 'H :
   [wf] sequent { <H>; x: 'a > 'b; <J['x]> >- 'a in int } -->
   [wf] sequent { <H>; x: 'a > 'b; <J['x]> >- 'b in int } -->
   [main] sequent { <H>; x: 'a > 'b; <J['x]>; 'a >= ('b +@ 1) >- 'C['x] } -->
   sequent { <H>; x: 'a > 'b; <J['x]> >- 'C['x] }

interactive gtb2ge {| ge_elim |} 'H :
   [wf] sequent { <H>; x: "assert"{'a >@ 'b}; <J['x]> >- 'a in int } -->
   [wf] sequent { <H>; x: "assert"{'a >@ 'b}; <J['x]> >- 'b in int } -->
   [main] sequent { <H>; x: "assert"{'a >@ 'b}; <J['x]>; 'a >= ('b +@ 1) >- 'C['x] } -->
   sequent { <H>; x: "assert"{'a >@ 'b}; <J['x]> >- 'C['x] }

interactive eq2ge {| ge_elim |} 'H :
   sequent { <H>; x: 'a = 'b in int; <J['x]>; 'a >= 'b; 'b >= 'a >- 'C['x] } -->
   sequent { <H>; x: 'a = 'b in int; <J['x]> >- 'C['x] }

interactive assert_beq2ge {| ge_elim |} 'H :
   [wf] sequent { <H>; x: "assert"{'a =@ 'b}; <J[it]> >- 'a in int } -->
   [wf] sequent { <H>; x: "assert"{'a =@ 'b}; <J[it]> >- 'b in int } -->
   sequent { <H>; x: "assert"{'a =@ 'b}; <J['x]>; 'a >= 'b; 'b >= 'a >- 'C['x] } -->
   sequent { <H>; x: "assert"{'a =@ 'b}; <J['x]> >- 'C['x] }

interactive eq2ge1 'H :
   sequent { <H>; x: 'a = 'b in int; <J['x]>; 'a >= 'b >- 'C['x] } -->
   sequent { <H>; x: 'a = 'b in int; <J['x]> >- 'C['x] }

interactive eq2ge2 'H :
   sequent { <H>; x: 'a = 'b in int; <J['x]>; 'b >= 'a >- 'C['x] } -->
   sequent { <H>; x: 'a = 'b in int; <J['x]> >- 'C['x] }

interactive notle2ge :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [aux] sequent { <H> >- "not"{('a <= 'b)} } -->
   sequent { <H> >- 'a >= ('b +@ 1) }

interactive notle2ge_elim {| ge_elim |} 'H :
   [wf] sequent { <H>; x: "not"{'a <= 'b}; <J['x]> >- 'a in int } -->
   [wf] sequent { <H>; x: "not"{'a <= 'b}; <J['x]> >- 'b in int } -->
   sequent { <H>; x: "not"{'a <= 'b}; <J['x]>; 'a >= ('b +@ 1) >- 'C['x] } -->
   sequent { <H>; x: "not"{'a <= 'b}; <J['x]> >- 'C['x] }

interactive notge2ge_elim {| ge_elim |} 'H :
   [wf] sequent { <H>; x: "not"{'a >= 'b}; <J['x]> >- 'a in int } -->
   [wf] sequent { <H>; x: "not"{'a >= 'b}; <J['x]> >- 'b in int } -->
   sequent { <H>; x: "not"{'a >= 'b}; <J['x]>; 'b >= ('a +@ 1) >- 'C['x] } -->
   sequent { <H>; x: "not"{'a >= 'b}; <J['x]> >- 'C['x] }

interactive notlt2ge_elim {| ge_elim |} 'H :
   [wf] sequent { <H>; x: "not"{'a < 'b}; <J['x]> >- 'a in int } -->
   [wf] sequent { <H>; x: "not"{'a < 'b}; <J['x]> >- 'b in int } -->
   sequent { <H>; x: "not"{'a < 'b}; <J['x]>; 'a >= 'b >- 'C['x] } -->
   sequent { <H>; x: "not"{'a < 'b}; <J['x]> >- 'C['x] }

interactive notgt2ge_elim {| ge_elim |} 'H :
   [wf] sequent { <H>; x: "not"{'a > 'b}; <J['x]> >- 'a in int } -->
   [wf] sequent { <H>; x: "not"{'a > 'b}; <J['x]> >- 'b in int } -->
   sequent { <H>; x: "not"{'a > 'b}; <J['x]>; 'b >= 'a >- 'C['x] } -->
   sequent { <H>; x: "not"{'a > 'b}; <J['x]> >- 'C['x] }

interactive noteq2ge_elim (*{| ge_elim |}*) 'H :
   [wf] sequent { <H>; x: "not"{'a = 'b in int}; <J['x]> >- 'a in int } -->
   [wf] sequent { <H>; x: "not"{'a = 'b in int}; <J['x]> >- 'b in int } -->
   sequent { <H>; x: "not"{'a = 'b in int}; <J['x]>; 'a >= 'b +@ 1 >- 'C['x] } -->
   sequent { <H>; x: "not"{'a = 'b in int}; <J['x]>; 'b >= 'a +@ 1 >- 'C['x] } -->
   sequent { <H>; x: "not"{'a = 'b in int}; <J['x]> >- 'C['x] }

interactive notneq2ge_elim {| ge_elim |} 'H :
   [wf] sequent { <H>; x: "not"{'a <> 'b}; <J['x]> >- 'a in int } -->
   [wf] sequent { <H>; x: "not"{'a <> 'b}; <J['x]> >- 'b in int } -->
   sequent { <H>; x: "not"{'a <> 'b}; <J['x]>; 'a = 'b in int >- 'C['x] } -->
   sequent { <H>; x: "not"{'a <> 'b}; <J['x]> >- 'C['x] }

interactive nequal_elim {| elim [] |} 'H :
   [wf] sequent { <H>; x: nequal{'a;'b}; <J['x]>  >- 'a in int } -->
   [wf] sequent { <H>; x: nequal{'a;'b}; <J['x]>  >- 'b in int } -->
   sequent { <H>; <J[it]>; y: (('a >= 'b +@ 1) or ('b >= 'a +@ 1)) >- 'C[it] } -->
   sequent { <H>; x: nequal{'a;'b}; <J['x]> >- 'C['x] }

interactive nequal_elim2 (*{| elim []; ge_elim |}*) 'H :
   [wf] sequent { <H>; x: nequal{'a;'b}; <J['x]>  >- 'a in int } -->
   [wf] sequent { <H>; x: nequal{'a;'b}; <J['x]>  >- 'b in int } -->
   sequent { <H>; x: nequal{'a;'b}; <J['x]>; y: ('a >= 'b +@ 1) >- 'C['x] } -->
   sequent { <H>; x: nequal{'a;'b}; <J['x]>; y: ('b >= 'a +@ 1) >- 'C['x] } -->
   sequent { <H>; x: nequal{'a;'b}; <J['x]> >- 'C['x] }

interactive ltInConcl2ge {| ge_intro |} :
	[wf] sequent { <H> >- 'a in int } -->
	[wf] sequent { <H> >- 'b in int } -->
	sequent { <H>; 'a >= 'b >- "assert"{bfalse} } -->
	sequent { <H> >- 'a < 'b }

interactive gtInConcl2ge {| ge_intro |} :
	[wf] sequent { <H> >- 'a in int } -->
	[wf] sequent { <H> >- 'b in int } -->
	sequent { <H>; 'b >= 'a >- "assert"{bfalse} } -->
	sequent { <H> >- 'a > 'b }

interactive leInConcl2ge {| ge_intro |} :
	[wf] sequent { <H> >- 'a in int } -->
	[wf] sequent { <H> >- 'b in int } -->
	sequent { <H>; 'a >= ('b +@ 1) >- "assert"{bfalse} } -->
	sequent { <H> >- 'a <= 'b }

interactive geInConcl2ge {| ge_intro |} :
	[wf] sequent { <H> >- 'a in int } -->
	[wf] sequent { <H> >- 'b in int } -->
	sequent { <H>; 'b >= ('a +@ 1) >- "assert"{bfalse} } -->
	sequent { <H> >- 'a >= 'b }

interactive eqInConcl2ge (*{| ge_intro |}*) :
	[wf] sequent { <H> >- 'a in int } -->
	[wf] sequent { <H> >- 'b in int } -->
	sequent { <H>; 'a >= ('b +@ 1) >- "assert"{bfalse} } -->
	sequent { <H>; 'b >= ('a +@ 1) >- "assert"{bfalse} } -->
	sequent { <H> >- 'a = 'b in int }

interactive neqInConcl2ge {| ge_intro |} :
	[wf] sequent { <H> >- 'a in int } -->
	[wf] sequent { <H> >- 'b in int } -->
	sequent { <H>; 'a = 'b in int >- "assert"{bfalse} } -->
	sequent { <H> >- 'a <> 'b }

interactive_rw bnot_lt2ge_rw :
   ('a in int) -->
   ('b in int) -->
   "assert"{bnot{lt_bool{'a; 'b}}} <--> ('a >= 'b)

let bnot_lt2geC = bnot_lt2ge_rw

let lt2ConclT = magicT thenLT [(addHiddenLabelT "wf"); rwh bnot_lt2geC (-1)]
let ltInConcl2HypT = (rwh unfold_lt 0) thenMT lt2ConclT
let gtInConcl2HypT = (rwh unfold_gt 0) thenMT ltInConcl2HypT

interactive_rw bnot_le2gt_rw :
   ('a in int) -->
   ('b in int) -->
   "assert"{bnot{le_bool{'a; 'b}}} <--> ('a > 'b)

let bnot_le2gtC = bnot_le2gt_rw

let leInConcl2HypT =
   (rwh unfold_le 0) thenMT (magicT thenLT [idT;rwh bnot_le2gtC (-1)])

let geInConcl2HypT =
   (rwh unfold_ge 0) thenMT leInConcl2HypT

interactive eq2pair_of_ineq :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [main] sequent { <H> >- 'a >= 'b } -->
   [main] sequent { <H> >- 'b >= 'a } -->
   sequent { <H> >- 'a = 'b in int }

let eqInConcl2HypT t =
	let (t,a,b)=dest_equal t in
   if alpha_equal t <<int>> then
   	if alpha_equal a b then
      	idT
		else
			eq2pair_of_ineq thenMT geInConcl2HypT
   else
   	idT

let neqInConcl2HypT =
	(rw (unfold_neq_int thenC (addrC [0] unfold_bneq_int)) 0)
	thenMT
	(assert_bnot_intro thenMT (eq_int_assert_elim (-1)) thenMT (thinT (-2)))

let arithRelInConcl2HypT = funT (fun p ->
   let g=Sequent.goal p in
   let t=Refiner.Refiner.TermMan.nth_concl g 1 in
   if is_lt_term t then ltInConcl2HypT
   else if is_gt_term t then gtInConcl2HypT
   else if is_le_term t then leInConcl2HypT
   else if is_ge_term t then geInConcl2HypT
   else if is_equal_term t then eqInConcl2HypT t
   else if is_neq_int_term t then neqInConcl2HypT
   else if is_not_term t then not_intro
   else idT)

let arith_rels=[
	opname_of_term << 'x<'y >>;
	opname_of_term << 'x>'y >>;
	opname_of_term << 'x<='y >>;
	opname_of_term << 'x>='y >>]

let rec is_arith_rel t =
	let op=opname_of_term t in
   (List.mem op arith_rels) or
   (is_equal_term t && (let (t',_,_)=dest_equal t in alpha_equal t' <<int>>)) or
   (is_not_term t && is_arith_rel (dest_not t))

let negativeHyp2ConclT = argfunT (fun i p ->
   let t = Sequent.nth_hyp p i in
	if is_not_term t then
      if is_arith_rel (dest_not t) then
      	(not_elim i) thenMT arithRelInConcl2HypT
		else
      	idT
	else if is_neq_int_term t then
   	(rw (unfold_neq_int thenC (addrC [0] unfold_bneq_int)) i)
   	thenMT
      ((assert_bnot_elim i) thenMT
      (eq_2beq_int thenMT arithRelInConcl2HypT))
   else
   	idT)

interactive_rw mul_BubblePrimitive_rw :
   ( 'a in int ) -->
   ( 'b in int ) -->
   ( 'c in int ) -->
   ('a *@ ('b *@ 'c)) <--> ('b *@ ('a *@ 'c))

let mul_BubblePrimitiveC = mul_BubblePrimitive_rw

interactive_rw sum_same_products1_rw :
   ('a in int) -->
   ((number[i:n] *@ 'a) +@ (number[j:n] *@ 'a)) <-->
   ((number[i:n] +@ number[j:n]) *@ 'a)

let sum_same_products1C = sum_same_products1_rw thenC (addrC [0] reduce_add)

interactive_rw sum_same_products2_rw :
   ('a in int) -->
   ((number[i:n] *@ 'a) +@ 'a) <--> ((number[i:n] +@ 1) *@ 'a)

let sum_same_products2C = sum_same_products2_rw thenC (addrC [0] reduce_add)

interactive_rw sum_same_products3_rw :
   ('a in int) -->
   ('a +@ (number[j:n] *@ 'a)) <--> ((number[j:n] +@ 1) *@ 'a)

let sum_same_products3C = sum_same_products3_rw thenC (addrC [0] reduce_add)

interactive_rw sum_same_products4_rw :
   ('a in int) -->
   ('a +@ 'a) <--> (2 *@ 'a)

let sum_same_products4C = sum_same_products4_rw

interactive_rw add_BubblePrimitive_rw :
   ( 'a in int ) -->
   ( 'b in int ) -->
   ( 'c in int ) -->
   ('a +@ ('b +@ 'c)) <--> ('b +@ ('a +@ 'c))

let add_BubblePrimitiveC = add_BubblePrimitive_rw

let stripCoef t =
	if is_mul_term t then
      let (c,t')=dest_mul t in
      if (is_number_term c) then
         t'
      else
         t
   else
      t

interactive_rw sub_elim_rw {| arith_unfold |} :
   ( 'a in int ) -->
   ( 'b in int ) -->
   ('a -@ 'b ) <--> ('a +@ ((-1) *@ 'b))

let compare_terms a b =
	if is_number_term a then
		if is_number_term b then Equal
		else Less
	else
		if is_number_term b then Greater
		else
			if is_mul_term a then
				if is_mul_term b then
					compare_terms a b
				else
					Greater
			else
				if is_mul_term b then
					Less
				else
					compare_terms a b

let addSwap1C t =
	match explode_term t with
		<<'a +@ 'b>> when
			let a' = stripCoef a in
			let b' = stripCoef b in
			(compare_terms b' a')=Less -> add_CommutC
	 | _ -> failC

let addSwap2C t =
	match explode_term t with
		<<'a +@ 'b>> ->
			(match explode_term b with
				<<'c +@ 'd>> when
					let a' = stripCoef a in
					let c' = stripCoef c in
					(compare_terms c' a')=Less -> add_BubblePrimitiveC
			 | _ -> failC
			)
	 | _ -> failC

let mulSwap1C t =
	match explode_term t with
		<<'a *@ 'b>> when
			(compare_terms b a)=Less -> mul_CommutC
	 | _ -> failC

let mulSwap2C t =
	match explode_term t with
		<<'a *@ 'b>> ->
			(match explode_term b with
				<<'c *@ 'd>> when
					(compare_terms c a)=Less -> mul_BubblePrimitiveC
			 | _ -> failC
			)
	 | _ -> failC

let resource arith_unfold +=[
	<<'a *@ 'b>>, termC mulSwap1C;
	<<'a *@ ('b *@ 'c)>>, termC mulSwap2C;
	(*<<number[i:n] *@ 'a>>, failC;*)
	<<'a *@ number[i:n]>>, mul_CommutC;
	(*<<number[i:n] *@ ('b *@ 'c)>>, failC;*)
	(*<<'b *@ (number[i:n] *@ 'c)>>, mul_BubblePrimitiveC;*)
	<<number[i:n] *@ (number[j:n] *@ 'c)>>, (mul_AssocC thenC (addrC [0] reduce_mul));

	<<'a +@ 'b>>, termC addSwap1C;
	<<'a +@ ('b +@ 'c)>>, termC addSwap2C;
	(*<<number[i:n] +@ 'a>>, failC;*)
	<<'a +@ number[i:n]>>, add_CommutC;
	(*<<number[i:n] +@ ('b +@ 'c)>>, failC;*)
	(*<<'a +@ (number[i:n] +@ 'c)>>, add_BubblePrimitiveC;*)
	<<number[i:n] +@ (number[j:n] +@ 'c)>>, (add_AssocC thenC (addrC [0] reduce_add));

	<<('a +@ 'b) +@ 'c>>, add_Assoc2C;
	<<('a *@ 'b) *@ 'c>>, mul_Assoc2C;

	<<(number[i:n] *@ 'a) +@ (number[j:n] *@ 'a)>>, sum_same_products1C;
	<<(number[i:n] *@ 'a) +@ 'a>>, sum_same_products2C;
	<<'a +@ (number[j:n] *@ 'a)>>, sum_same_products3C;
	<<'a +@ 'a>>, sum_same_products4C;

	<<(number[i:n] *@ 'a) +@ ((number[j:n] *@ 'a) +@ 'b)>>, (add_AssocC thenC (addrC [0] sum_same_products1C));
	<<(number[i:n] *@ 'a) +@ ('a +@ 'b)>>, (add_AssocC thenC (addrC [0] sum_same_products2C));
	<<'a +@ ((number[j:n] *@ 'a) +@ 'b)>>, (add_AssocC thenC (addrC [0] sum_same_products3C));
	<<'a +@ ('a +@ 'b)>>, (add_AssocC thenC (addrC [0] sum_same_products4C));
]

doc <:doc<
	@begin[doc]

	@begin[description]
	@item{@conv[normalizeC];
   The @tt[normalizeC] converts polynomials to canonical form (normalizes),
   it is supposed to work not only when applied precisely
   on a polynomial but also when the polynomial is just a subterm of the
   term the rewrite applied to.  For instance, if you have a hypothesis
   in the form of inequality or equality you can apply this rewrite to the whole
   hypothesis and it will normalize both sides of inequality (or equality).

   Example: The canonical form of <<'b *@ 2 *@ ('a +@ 'c) -@ ('a *@ 'b) +@ 1>> is
   <<1 +@ (('a *@ 'b) +@ (2 *@ ('b *@ 'c)))>>

   The canonical form of a polynomial is achieved by the following steps:
   @begin[enumerate]
   @item{Get rid of subtraction.}

   @item{Open parentheses using distributivity, move parentheses to the right
   using associativity of addition and multiplication, make other simplifications
   encoded in @hrefconv[reduceC].}

   @item{In every monomial sort (commuting) multipliers in increasing order,
   but pull literal integers to the left (we put coefficients first because later
   we have to reduce similar monomials) and multiply them if there is more than one
   literal integer in one monomial. If monomial does not have literal multipliers
   at all, put <<1>> in front of it for uniformity.}

   @item{Sort monomials in increasing order, reducing similar monomials on the fly.
   Again integer literals should be pulled to the left
   (i.e. considered to be the least terms).}

   @item{Get rid of zeros and ones in the resulting term using @hrefconv[reduceC]}

   @end[enumerate]
	}
	@end[description]

	@end[doc]
>>
let normalizeC = reduceC thenC arith_unfoldC thenC reduceC

doc <:doc< @docoff >>

interactive_rw ge_addContract_rw :
   ( 'a in int ) -->
   ( 'b in int ) -->
   ('a >= ('b +@ 'a)) <--> (0 >= 'b)

interactive_rw ge_addContract_rw1 {| reduce |} :
   ( 'a in int ) -->
   ('a >= (number[i:n] +@ 'a)) <--> (0 >= number[i:n])

interactive_rw ge_addContract_rw2 {| reduce |} :
   ( 'a in int ) -->
   ((number[i:n] +@ 'a) >= 'a) <--> (number[i:n] >= 0)

interactive_rw ge_addContract_rw3 {| reduce |} :
   ( 'a in int ) -->
   ((number[i:n] +@ 'a) >= (number[j:n] +@ 'a)) <--> (number[i:n] >= number[j:n])

interactive ge_addMono2 'c :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- ('a >= 'b) ~ (('c +@ 'a) >= ('c +@ 'b)) }

interactive_rw ge_addMono2_rw 'c :
   ( 'a in int ) -->
   ( 'b in int ) -->
   ( 'c in int ) -->
   ('a >= 'b) <--> (('c +@ 'a) >= ('c +@ 'b))

let ge_addMono2C = ge_addMono2_rw

interactive sumGe 'H 'J :
	[wf] 	sequent { <H>; v: 'a >= 'b; <J['v]>; w: 'c >= 'd; <K['v;'w]> >- 'a in int } -->
	[wf] 	sequent { <H>; v: 'a >= 'b; <J['v]>; w: 'c >= 'd; <K['v;'w]> >- 'b in int } -->
	[wf] 	sequent { <H>; v: 'a >= 'b; <J['v]>; w: 'c >= 'd; <K['v;'w]> >- 'c in int } -->
	[wf] 	sequent { <H>; v: 'a >= 'b; <J['v]>; w: 'c >= 'd; <K['v;'w]> >- 'd in int } -->
			sequent { <H>; v: 'a >= 'b; <J['v]>; w: 'c >= 'd; <K['v;'w]>; ('a +@ 'c) >= ('b +@ 'd) >- 'C['v;'w] } -->
			sequent { <H>; v: 'a >= 'b; <J['v]>; w: 'c >= 'd; <K['v;'w]> >- 'C['v;'w] }

let rec printList = function
	(a,b,n,(i,len,tac))::tl ->
		eprintf "%i/%i: %s >= %s + %s%t" i len
			(SimplePrint.short_string_of_term a)
			(Lm_num.string_of_num n)
			(SimplePrint.short_string_of_term b)
			eflush;
		printList tl
 | [] -> ()

let rec sumListAuxT tac len offset i l = funT ( fun p ->
	let k=succ (Sequent.hyp_count p) in
	match l with
		(_,_,_,(j,len',tac'))::tl ->
			if tac==tac' then
				let posj = offset+j in
				let i'=min i posj in
				let j'=max i posj in
				let _ = 	if !debug_int_arith then
								eprintf " %i%t" posj flush
				in
				sumGe i' (j'-i') thenMT sumListAuxT tac len offset k tl
			else
				let new_hyp_count = len'+k in
				let offset' = if j>=0 then 0 else new_hyp_count in
				let posj = offset'+j in
				let i'=min i posj in
				let j'=max i posj in
				if !debug_int_arith then
					eprintf " %i%t" posj flush;
				tac' thenMT sumGe i' (j'-i') thenMT sumListAuxT tac' len' offset' new_hyp_count tl
	 | [] -> idT (*raise (RefineError("Itt_int_arith.sumListT", StringError "impossible case"))*)
)

let sumListT l = funT ( fun p ->
	if !debug_int_arith then
		(eprintf "contradictory list:\n"; printList l;eflush stderr);
	match l with
	 | [(_,_,_,(i,len,tac))] ->
			let new_hyp_count = succ (len+(Sequent.hyp_count p)) in
			let offset = if i>=0 then 0 else new_hyp_count in
			let i = offset+i in
			if !debug_int_arith then
				eprintf "Itt_int_arith.sumList: only one inequality %i%t" i flush;
			tac thenMT copyHypT i new_hyp_count
	 | (_,_,_,(i,len,tac))::tl ->
			let offset = if i>=0 then 0 else succ (len+(Sequent.hyp_count p)) in
			let i = offset+i in
			if !debug_int_arith then
				eprintf "Itt_int_arith.sumList: %i items: %i%t" (List.length l) i flush;
			tac thenMT (sumListAuxT tac len offset i tl)
	 | [] ->	idT
)

let num0 = num_of_int 0
let num1 = num_of_int 1

let term2term_number p t =
	let es={sequent_args=t; sequent_hyps=(SeqHyp.of_list []); sequent_goals=(SeqGoal.of_list [t])} in
	let s=mk_sequent_term es in
	let s'=Top_conversionals.apply_rewrite p normalizeC s in
	let t'=SeqGoal.get (TermMan.explode_sequent s').sequent_goals 0 in
	begin
		if !debug_int_arith then
			eprintf "t2t_n: %a -> %a%t" print_term t print_term t' eflush;
		if is_add_term t' then
			let a,b=dest_add t' in
			if is_number_term a then
				(b,dest_number a)
			else
				(t',num0)
		else
			if is_number_term t' then
				(mk_number_term num0, dest_number t')
			else
				(t',num0)
	end

let term2inequality_aux p (a,b,n,tac) =
	let a1,a2=term2term_number p a in
	let b1,b2=term2term_number p b in
	(a1,b1,sub_num (add_num b2 n) a2,tac)

let term2inequality p (i,t) =
	if is_ge_term t then
		let a,b=dest_ge t in
		List.map (term2inequality_aux p) [(a,b,num0,copyHypT i (-1))]
	else if is_le_term t then
		let a,b=dest_le t in
		List.map (term2inequality_aux p) [(b,a,num0,((rw fold_ge i) thenT (copyHypT i (-1))))]
	else if is_gt_term t then
		let a,b=dest_gt t in
		List.map (term2inequality_aux p) [(a,b,num1,gt2ge i)]
	else if is_lt_term t then
		let a,b=dest_lt t in
		List.map (term2inequality_aux p) [(b,a,num1,lt2ge i)]
	else if is_equal_term t then
		let _,a,b=dest_equal t in
		List.map (term2inequality_aux p) [(a,b,num0,eq2ge1 i);(b,a,num0,eq2ge2 i)]
	else
		raise (Invalid_argument "Itt_int_arith.term2triple - unexpected opname")

(*
let good_term t =
	let op=opname_of_term t in
   (List.mem op arith_rels) or
   (match explode_term t with
      << 'l = 'r in 'tt >> when alpha_equal tt <<int>> && not (alpha_equal l r) -> true
    | _ -> false)
*)
(*
 * Caching

let main_label="main"

module TermPos=
struct
	type data = int
	let append l1 l2 = l1 @ l2
end

module TTable=Term_eq_table.MakeTermTable(TermPos)

let empty _ = ref (0, 0, TTable.empty)

let start_from h n =
	let (_,k,table) = !h in
	h:=(n,k,table)

let mem h t =
	let (n,_,table) = !h in
	TTable.mem table t

let lookup h t =
	let (n,k,table) = !h in
	begin
		h:=(n,succ k,table);
		TTable.find table t
	end

let add h t =
	let (n,k,tab) = !h in
	begin
		(*eprintf"%i<-%a%t" n print_term t eflush;*)
		h:=(succ n, k, TTable.add tab t n)
	end

let print_stat h =
	let (_,k,table) = !h in
	let n = List.length (TTable.list_of table) in
	eprintf "cacheT: %i goals, %i lookups%t" n k eflush

let print_statT h = funT ( fun p ->
	if !debug_int_arith then
		print_stat h;
	idT
)

let tryAssertT info t = funT ( fun p ->
	if mem info t then idT
	else
		begin
			(*eprintf "%i<-%a%t" (succ(Sequent.hyp_count p)) print_term t eflush;*)
			add info t;
			assertT t
		end
)

let rec assertListT info = function
	[(t,_)] -> tryAssertT info t
 | (t,_)::tl -> tryAssertT info t thenMT assertListT info tl
 | _ -> idT

let printT i = funT ( fun p ->
	let t=Sequent.concl p in
	let h=Sequent.nth_hyp p i in
	eprintf "missed %a -> %i: %a%t" print_term t i print_term h eflush;
	idT
)

let tryInfoT info = funT ( fun p ->
	let g=Sequent.concl p in
	let i=lookup info g in
	nthHypT i orelseT printT i
)

let cacheT info = argfunT ( fun tac p ->
	start_from info (succ(Sequent.hyp_count p));
	let (goals,_) = refine (tac thenMT addHiddenLabelT main_label) p in
	let aux_list = List.map (fun p -> (Sequent.concl p, Sequent.label p)) goals in
	let aux_list = List.filter (fun (g,l) -> l<>main_label) aux_list in
	assertListT info aux_list thenMT (tac thenAT (tryInfoT info)) thenMT (print_statT info)
)
*)

let norm_triple p a b =
	let a1,a2=term2term_number p a in
	let b1,b2=term2term_number p b in
	(a1,b1,sub_num b2 a2)

let four2inequality p (t,i,len,tac) =
	let a,b = dest_ge t in
	let a',b',n' = norm_triple p a b in
	a',b',n',(i,len,tac)

let findContradRelT = funT ( fun p ->
	let l = all2ge p in
	let l' = List.map (four2inequality p) l in
	if !debug_int_arith then
		(eprintf "total list:\n"; printList l';eflush stderr);
	let l'' = Arith.find_contradiction l' in
	sumListT l''
)

(*
   Reduce contradictory relation a>=a+b where b>0.
 *)
let reduceContradRelT =
   rw ((addrC [0] normalizeC) thenC (addrC [1] normalizeC) thenC
		 reduceC)

doc <:doc<
	@begin[doc]

	@begin[description]
	@item{@tactic[arithT];
   The @tt[arithT] proves simple inequalities. More precisely it can prove
   inequalities that logically follows from hypotheses using associativity and
   commutativity of addition and multiplication, properties of <<0>> and <<1>>,
   reflexivity, transitivity and weak monotonicity of <<Perv!nil >= Perv!nil>>.
   Weak monotonicity is the @hrefrule[lt_addMono] rule:

   $$
   @rulebox{lt@_addMono; c;
     <<sequent{ <H> >- 'a in int }>>@cr
     	 <<sequent{ <H> >- 'b in int }>>@cr
     	 <<sequent{ <H> >- 'c in int }>>;
     <<sequent{ <H> >- lt_bool{'a; 'b} ~ lt_bool{('a +@ 'c); ('b +@ 'c)} }>>}
   $$

   with restriction to use only literal integers for <<'c>> (or anything that
   can be automatically reduced to literal integer by @hrefconv[reduceC]).

   @tt[arithT] supports addition, multiplication, unary minus and subtraction
   operations. Division and remainder operations are not supported.
   Among arithmetic relations it supports are << cdot = (cdot) in int >>,
	<< nequal {Perv!nil ; Perv!nil } >>,
   << Perv!nil < Perv!nil >>, << Perv!nil > Perv!nil >>,
   << Perv!nil <= Perv!nil >>, and << Perv!nil >= Perv!nil >>. Arbitrary many negations
   of these relations are also supported. Other logical connectives are not supported.

   @tt[arithT] puts together everything that was defined in this module:
	@begin[enumerate]
	@item{First it moves arithmetic fact from conclusion to hypotheses in negated form
	using reasoning by contradiction.}

	@item{Then it converts all negative arithmetic facts in hypotheses to positive
	ones,
	it actually adds new hypotheses and leaves originals
	intact. Because there could be several nested negations this tactic should be
	also applied to hypotheses that were just generated by this tactic.}

	@item{Next it converts all positive arithmetic facts in hypotheses
	to <<Perv!nil >= Perv!nil>>-inequalities.}

	@item{Now every << Perv!nil >= Perv!nil >>-inequality should be normalized.}

	@item{Then it tries to find the contradictory inequality
	that logically follows from that normalized <<Perv!nil >= Perv!nil>>-inequalities
	and proves this implication.
   This problem is reduced to search for positive cycle in a directed graph and
   is performed by @hrefmodule[Arith] module. If successful, found inequality
   will be derived from hypotheses.}

	@item{Finally, false is derived from found inequality, this completes proof by
   contradiction scheme.}
	@end[enumerate]}
	@end[description]

	@end[doc]
	@docoff
>>

let preArithT = funT (fun p ->
   arithRelInConcl2HypT thenMT
   ((tryOnAllMCumulativeHypsT negativeHyp2ConclT) thenMT
	findContradRelT)
)

(* Finds and proves contradiction among ge-relations
 *)
let arithT = preArithT thenMT reduceContradRelT (-1)

interactive test 'a 'b 'c :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H> >- 'c in int } -->
sequent { <H>; x: ('a >= ('b +@ 1));
                     t: ('c >= ('b +@ 3));
                     u: ('b >= ('a +@ 0))
                >- "assert"{bfalse} }

interactive test2 'a 'b 'c :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H> >- 'c in int } -->
sequent { <H>; x: (('b +@ 1) <= 'a);
                     t: ('c > ('b +@ 2));
                     u: ('b >= ('a +@ 0))
                >- "assert"{bfalse} }

interactive test3 'a 'b 'c :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H> >- 'c in int } -->
sequent { <H>; x: (('b +@ 1) <= 'a);
                     t: ('c > ('b +@ 2))
                >- ('b < ('a +@ 0))  }

interactive test4 'a 'b :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H>; x: ('a >= 'b);
                     t: ('a < 'b)
                >- "assert"{bfalse} }

interactive test5 'a 'b :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H>; x: ('a >= 'b +@ 0);
                     t: ('a < 'b)
                >- "assert"{bfalse} }
(*
let mul_sort2C t =
	let a,b=dest_mul t in
   if ((compare_terms b a)=Less & not (is_number_term a)) or
     	(is_number_term b) then
  		mul_CommutC
	else
  		failC

let mul_sort3C t =
	let a,t'=dest_mul t in
	let b,_=dest_mul t' in
	if (compare_terms b a)=Less or (is_number_term b) then
		mul_BubblePrimitiveC
	else
		failC

let resource arith_unfold +=[
	<<'a *@ 'b>>, termC mul_sort2C;
	<<'a *@ ('b *@ 'c)>>, termC mul_sort3C;
]
*)

interactive test6 'b 'c :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H> >- 'c in int } -->
sequent { <H>; x: (('c *@ ('b +@ ('a *@ 'c)) +@ ('b *@ 'c)) >= 'b +@ 0);
                     t: (((((('c *@ 'b) *@ 1) +@ (2 *@ ('a *@ ('c *@ 'c)))) +@
 (('c *@ ((-1) *@ 'a)) *@ 'c)) +@ ('b *@ 'c)) < 'b)
                >- "assert"{bfalse} }

interactive test7 :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H>; 'a < 'b >- 'a <> 'b }

interactive test8 :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H>; 'a < 'b >- not{'a = 'b in int} }

interactive test9 :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H>; not{'a < 'b} >- 'a >= 'b }

interactive test10 :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H>; 'a <> 'b >- 'a <> 'b }

let rec gen_term nvars vars intrange maxdepth =
	let choice=Random.int 2 in
	if maxdepth>0 && choice=0 then
		mk_add_term (gen_term nvars vars intrange (maxdepth-1)) (gen_term nvars vars intrange (maxdepth-1))
	else if maxdepth>0 && choice=1 then
		mk_mul_term (gen_term nvars vars intrange (maxdepth-1)) (gen_term nvars vars intrange (maxdepth-1))
	else
		let choice=Random.int 1 in
		if choice=0 then
			let i=Random.int (nvars-1) in
			vars.(i)
		else
			mk_number_term (num_of_int (Random.int intrange))

let gen_ineq nvars intrange =
	(Random.int (nvars-1), Random.int (nvars-1), Random.int intrange)

let rec gen nvars intrange left =
	if left=0 then []
	else (gen_ineq nvars intrange)::(gen nvars intrange (left-1))

let triple2term vars (v1,v2,n) =
	mk_ge_term vars.(v1) (mk_add_term vars.(v2) (mk_number_term (num_of_int n)))

let rec assertListT vars = function
	[triple] -> assertT (triple2term vars triple)
 | hd::tl -> assertT (triple2term vars hd) thenMT (assertListT vars tl)
 | _ -> failT

let genT vl seed nvars nineq intrange maxdepth =
	Random.init seed;
	let vars=Array.of_list vl in
(*	let vars=Array.init nvars (fun i -> mk_var_term (Lm_symbol.make "v" i)) in*)
	let terms=Array.init nvars (fun i -> gen_term nvars vars intrange maxdepth) in
	let l=gen nvars intrange nineq in
	assertListT terms l

interactive testn :
	sequent {'v  in int;
				'v1 in int;
				'v2 in int;
				'v3 in int;
				'v4 in int;
				'v5 in int;
				'v6 in int;
				'v7 in int;
				'v8 in int;
				'v9 in int; "assert"{bfalse} >- "assert"{bfalse} }

interactive eq2ineq :
	[wf] sequent { <H> >- 'a in int } -->
	[wf] sequent { <H> >- 'b in int } -->
   [main] sequent { <H> >- 'a = 'b in int } -->
	sequent { <H> >- 'a <= 'b }

interactive_rw beq2ineq_rw :
	('a in int) -->
   ('b in int) -->
   beq_int{'a;'b} <--> band{le_bool{'a;'b}; le_bool{'b;'a}}
