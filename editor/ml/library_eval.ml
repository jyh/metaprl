(*
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 1998 Lori Lorigo, Richard Eaton, Cornell University
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
 * Authors: Lori Lorigo, Richard Eaton
 *
 *)

(*
 * This implements a filesystem interface to the library.
 *)



open Refiner.Refiner.Term
open Refiner.Refiner.TermType
open Refiner.Refiner.Refine
open Basic

open Mp

open Utils
open Library

open Printf
open Mp_debug
open Mp_num

exception LibraryException of string

let itt_bug = ref true

let _ =
   show_loading "Loading Library_eval%t"

let library = null_oref()
let connection = null_oref()

let library_close () =
  if oref_p library
  then (leave (oref_val library);
	disconnect (oref_val connection);
	oref_nullify library
       )
  else raise (LibraryException "Close: No library open.")

let lib_open_eval env ehook host localport remoteport =

 (* eprintf "%s %d %d %t" host localport remoteport eflush; *)

  if oref_p library
  then raise (LibraryException "Open: Library already open.")
  else let _ = oref_set library (join_eval (oref_set connection (connect host localport remoteport))
			    [env]
			    ehook) in
	at_exit library_close (* jyh: something is strange here *)

(*
 *
 * MetaPRL cmd syntax
 *
 * !mp_list_root{}() returns !tok_cons
 * !mp_list_module_all{}(tok_cons) returns !cons{}(!cons(!token{thm:t}(); sequent); !cons ...
 * !mp_list_module{}(tok_cons) returns !mp_edit{}(!cons(!token{thm:t}(); sequent); !cons ...
 * !mp_thm_create{}(!msequent) returns !void()
 * !mp_create_set{}(!tok_cons; sequent) returns !void()
 * !mp_set_goal{}(!tok_cons; sequent) returns !void()
 * !mp_lookup_proof{}(symaddr) returns !mp_prf(goal; tactic; children; extras) g and ex are sequent, ch are mp_prf
 * !mp_refine{}(symaddr; address; tactic) returns !mp_ref(goal; subgoals; extras) g, subs and ex are sequent terms
 * !mp_undo{}(symb) returns !mp_prf(goal; tactic; children; extras)
 * !mp_save{}(symb) returns !void()
 *
 *)

let mp_list_root_op = mk_nuprl5_op [ make_param (Token "!mp_list_root")]
let mp_list_display_op = mk_nuprl5_op [ make_param (Token "!mp_list_display")]
let mp_list_module_all_op = mk_nuprl5_op [ make_param (Token "!mp_list_module_all")]
let mp_list_module_op = mk_nuprl5_op [ make_param (Token "!mp_list_module")]
let mp_create_op = mk_nuprl5_op [ make_param (Token "!mp_create")]
let mp_create_rw_op = mk_nuprl5_op [ make_param (Token "!mp_create_rw")]
let mp_create_set_op = mk_nuprl5_op [ make_param (Token "!mp_create_set")]
let mp_set_goal_op = mk_nuprl5_op [ make_param (Token "!mp_set_goal")]
let mp_set_thm_op = mk_nuprl5_op [ make_param (Token "!mp_set_thm")]
let mp_set_rw_op = mk_nuprl5_op [ make_param (Token "!mp_set_rw")]
let mp_lookup_op = mk_nuprl5_op [ make_param (Token "!mp_lookup_proof")]
let mp_refine_op = mk_nuprl5_op [ make_param (Token "!mp_refine")]
let mp_undo_op = mk_nuprl5_op [ make_param (Token "!mp_undo")]
let mp_save_op = mk_nuprl5_op [ make_param (Token "!mp_save")]
let mp_save_thy_op = mk_nuprl5_op [ make_param (Token "!mp_save_thy")]
let mp_node_op = mk_nuprl5_op [ make_param (Token "!mp_node")]
let refiner_op = mk_nuprl5_op [ make_param (Token "!refine")]

let refine_req_p t = opeq refiner_op (operator_of_term t)

let current_symaddr = ref []
let current_pair = ref ("foo", "foo")

let refine_args t =
  match dest_term t with
    {term_op = op; term_terms = goal :: tac :: r } when (opeq op refiner_op)

    -> (term_of_unbound_term goal, term_of_unbound_term tac)

  | _ -> error ["eval"; "op"; "unrecognized"] [] [t]

let iinf_sequent_op = mk_nuprl5_op [make_param (Token "!inf_sequent"); Basic.inil_parameter]
let iinf_sequent_term hyp term = mk_term iinf_sequent_op [(mk_bterm [] hyp); (mk_bterm [""] term)]

let mp_prf_term g tac s e =
  mk_term (mk_nuprl5_op [make_param (Token "!mp_prf")])
    [(mk_bterm [] g); (mk_bterm [] tac); (mk_bterm [] s); (mk_bterm [] e)]

let mp_edit_term w c a r =
  mk_term (mk_nuprl5_op [make_param (Token "!mp_edit")])
    [(mk_bterm [] w); (mk_bterm [] c); (mk_bterm [] a); (mk_bterm [] r)]

let mp_ref_term g s e =
  mk_term (mk_nuprl5_op [make_param (Token "!mp_ref")])
    [(mk_bterm [] g); (mk_bterm [] s); (mk_bterm [] e)]

let inatural_cons_op = (mk_nuprl5_op [make_param (Token "!natural_cons")])
let int_list_of_term t =
  map_isexpr_to_list_by_op inatural_cons_op number_of_inatural_term t

let string_list_of_term t =
  map_isexpr_to_list_by_op icons_op string_of_itoken_term t

let imp_msequent_op = (mk_nuprl5_op [make_param (Token "!mp_msequent")])
let imp_msequent_term a g = mk_term imp_msequent_op [(mk_bterm [] a); (mk_bterm [] g)]
let imcons_op = (mk_nuprl5_op [make_param (Token "!mcons")])

let msequent_to_term mseq =
  let (goal, hyps) = dest_msequent mseq
  in imp_msequent_term (list_to_ilist_by_op imcons_op hyps) goal

let term_to_msequent t =
  match dest_term t with
      { term_op = imp_msequent_op; term_terms = [assums; goal]} ->
	(map_isexpr_to_list_by_op imcons_op (let f x = x in f) (term_of_unbound_term assums),
	 (term_of_unbound_term goal))
    | _ ->
        raise (Refiner.Refiner.RefineError.RefineError
		 ("term_to_msequent", (Refiner.Refiner.RefineError.TermMatchError
					 (t, "malformed metasequent"))))

let term_to_symaddr t =
  match string_list_of_term t with
      a::b::c::tl -> (b, c)
    | _ ->
        raise (Refiner.Refiner.RefineError.RefineError
		 ("term_to_symaddr", (Refiner.Refiner.RefineError.TermMatchError
					 (t, "malformed msequent"))))

let ilist_op = (mk_nuprl5_op [make_param (Token "!list")])

let ipair_op = (mk_nuprl5_op [make_param (Token "!pair")])
let ipair_term h t = mk_term ipair_op [(mk_bterm [] h); (mk_bterm [] t)]

let list_of_ints length =
  let rec ll len =
    if len = 0 then []
    else len::(ll (len - 1))
  in List.rev (ll length)

open List
open List_util

let get_fl name =
  let rec lp ls lf =
    if ls = [] then lf
    else let el = edit_list_parents (hd ls) in
      lp (union el (tl ls)) (union el lf) in
    lp [name] [name]

let idform_op = (mk_nuprl5_op [make_param (Token "!dform")])
let idform_term attr lhs rhs =
  mk_term idform_op [mk_bterm [] attr; mk_bterm [] lhs; mk_bterm [] rhs]

let imp_prec_pair_op = (mk_nuprl5_op [make_param (Token "!mp_prec_pair")])
let imp_prec_pair_term lhs rhs =
  mk_term imp_prec_pair_op [mk_bterm [] lhs; mk_bterm [] rhs]
let imp_prec_rel_op r = (mk_nuprl5_op [make_param (Token "!mp_prec_rel"); make_param (Token r)])
let imp_prec_rel_term r lhs rhs =
  mk_term (imp_prec_rel_op r) [mk_bterm [] lhs; mk_bterm [] rhs]

let idform_attr_op = (mk_nuprl5_op [make_param (Token "!dform_attr_cons")])
let imode_cons_op = (mk_nuprl5_op [make_param (Token "!mode_cons")])
let imp_prec_cons_op = (mk_nuprl5_op [make_param (Token "!mp_prec_cons")])
let imp_prec_rel_cons_op = (mk_nuprl5_op [make_param (Token "!mp_prec_rel_cons")])

let ifail_parameter = make_param (Token "!fail")
let ifail_op = mk_nuprl5_op [ifail_parameter]
let ifail_term t = mk_term ifail_op [mk_bterm [] t]

(*
let dest_rw_term t =
  match dest_term t with
      { term_op = imp_rw_op; term_terms = [redex; contract]} ->
	((term_of_unbound_term redex), (term_of_unbound_term contract))
    | _ ->
        raise (Refiner.Refiner.RefineError.RefineError
		 ("dest_rw_term", (Refiner.Refiner.RefineError.TermMatchError
					 (t, "malformed rw"))))

let dest_rw_term t =
  match dest_term t with
      { term_op = imp_msequent_op; term_terms = [assums; goal]} ->
	  (match dest_term (term_of_unbound_term goal) with
                { term_op = op ; term_terms = [redex; contract]} ->
                ((term_of_unbound_term redex), (term_of_unbound_term contract))
		| _ ->
                raise (Refiner.Refiner.RefineError.RefineError
		 ("dest_rw_term", (Refiner.Refiner.RefineError.TermMatchError
					 ((term_of_unbound_term goal), "malformed rw")))))
    | _ ->
        raise (Refiner.Refiner.RefineError.RefineError
		 ("term_to_msequent", (Refiner.Refiner.RefineError.TermMatchError
					 (t, "malformed metasequent"))))

this one if treated as proof
let dest_rw_term t =
  match dest_term t with
      { term_op = imp_msequent_op; term_terms = [assums; goal]} ->
	  (match dest_term (term_of_unbound_term goal) with
                { term_op = op ; term_terms = [seq]} ->
                (match dest_term (term_of_unbound_term seq) with
                { term_op = op ; term_terms = [h]} ->
		(match dest_term (term_of_unbound_term h) with
                { term_op = op ; term_terms = [concl]} ->
		(match dest_term (term_of_unbound_term concl) with
                { term_op = op ; term_terms = [rw]} ->
		(match dest_term (term_of_unbound_term rw) with
                { term_op = op ; term_terms = [redex; contract]} ->
		((term_of_unbound_term redex), (term_of_unbound_term contract))))))
		| _ ->
                raise (Refiner.Refiner.RefineError.RefineError
		 ("dest_rw_term", (Refiner.Refiner.RefineError.TermMatchError
					 ((term_of_unbound_term goal), "malformed rw")))))
    | _ ->
        raise (Refiner.Refiner.RefineError.RefineError
		 ("term_to_msequent", (Refiner.Refiner.RefineError.TermMatchError
					 (t, "malformed metasequent"))))

*)
let dest_rw_term t =
  match dest_term t with
      { term_op = imp_msequent_op; term_terms = [assums; goal]} ->
	  (match dest_term (term_of_unbound_term goal) with
                { term_op = op ; term_terms = [redex; contract]} ->
		((term_of_unbound_term redex), (term_of_unbound_term contract))
		| _ ->
                raise (Refiner.Refiner.RefineError.RefineError
		 ("dest_rw_term", (Refiner.Refiner.RefineError.TermMatchError
					 ((term_of_unbound_term goal), "malformed rw")))))
    | _ ->
        raise (Refiner.Refiner.RefineError.RefineError
		 ("term_to_msequent", (Refiner.Refiner.RefineError.TermMatchError
					 (t, "malformed metasequent"))))



let refine_ehook rhook =
  unconditional_error_handler
    (function () ->
       (function t ->
    (* used in undo and lookup cmds *)
	  let rec visit_proof root_il =
	    let (s, goal, subgoals, extras) = edit_node root_il
	    in
	      (match s with
		   Some ss -> let length = List.length subgoals in
			      let vps i = visit_proof (i :: root_il) in
				(mp_prf_term (msequent_to_term goal) (itext_term ss)
				   (list_to_ilist (List.map vps (list_of_ints length)))
				   (list_to_ilist (List.map msequent_to_term extras)))
		 | None -> (mp_prf_term (msequent_to_term goal) ivoid_term inil_term
			      (list_to_ilist (List.map msequent_to_term extras))))
	  in
	    (match dest_term t with
		 {term_op = op; term_terms = symaddr :: addr :: tac :: r } when (opeq op mp_refine_op) ->
		   (let l = string_list_of_term (term_of_unbound_term symaddr)
		    in if l = !current_symaddr then ()
		      else (current_symaddr := l; Mp.edit_cd_thm (hd (tl l)) (hd (tl (tl l))));
		      let tactic = string_of_itext_term (term_of_unbound_term tac) in
			eprintf "%s %t" tactic eflush;

			let (gg, subgoals, extras) =
      			  Mp.edit_refine (int_list_of_term (term_of_unbound_term addr)) tactic in
			  mp_ref_term (msequent_to_term gg)
      			    (list_to_ilist (List.map msequent_to_term subgoals))
			    (list_to_ilist (List.map msequent_to_term extras)))

  (* node not needed at command call level*)
  (*| {term_op = op; term_terms = addr :: tac :: r } when (opeq op mp_node_op) ->
    let (goal, subgoals, extras) =
    Mp.edit_refine (int_list_of_term (term_of_unbound_term addr))
    (string_of_itext_term tac)
    in
    icons_term icons_op (msequent_to_term goal)
    (icons_term icons_op (list_to_ilist (map msequent_to_term subgoals))
    (list_to_ilist (List.map msequent_to_term extras)))
  *)

	       | {term_op = op; term_terms = symaddr :: r } when (opeq op mp_undo_op) ->
		   (let l = string_list_of_term (term_of_unbound_term symaddr) in
		      if l = !current_symaddr then ()
		      else (current_symaddr := l; Mp.edit_cd_thm (hd (tl l)) (hd (tl (tl l))));
		      Mp.edit_undo ();
		      visit_proof [])

	       | {term_op = op; term_terms = symaddr :: r } when (opeq op mp_save_op) ->
		   ((*let (b, c) = term_to_symaddr (term_of_unbound_term symaddr) in
		      if (b, c) = !current_pair then ()
		      else (current_pair := (b, c); Mp.edit_cd_thm b c);*)
                     let l = string_list_of_term (term_of_unbound_term symaddr) in
		      if l = !current_symaddr then () else
		      (current_symaddr := l; Mp.edit_cd_thm (hd (tl l)) (hd (tl (tl l))));
		      eprintf "saving thm %s %t" (hd (tl (tl l))) eflush;
                      Mp.save();
		      ivoid_term)

	       | {term_op = op; term_terms = symaddr :: r } when (opeq op mp_save_thy_op) ->
		   ((*let l = string_list_of_term (term_of_unbound_term symaddr) in
		      Mp.edit_save_thy (hd (tl l));*)
		      ivoid_term)

	       | {term_op = op; term_terms = [] } when (opeq op mp_list_root_op) ->
		   list_to_ilist (map itoken_term (Mp.edit_list_modules ()))

	       | {term_op = op; term_terms = symaddr :: r } when (opeq op mp_list_module_all_op) ->
		   let name = (hd (map_isexpr_to_list string_of_itoken_term
						      (term_of_unbound_term symaddr))) in
		   let f x = (Mp.edit_cd_thm name x;
			 let (s, goal, subgoals, extras) = Mp.edit_node [] in
			   ipair_term (itoken_term x) (msequent_to_term goal))

		   and flat_list = get_fl name
		   in icons_term icons_op
			(list_to_ilist_map (function x -> itoken_term (String.uncapitalize x)) flat_list)
			(list_to_ilist_map f (Mp.edit_list_module_all name))

	       | {term_op = op; term_terms = symaddr :: r } when (opeq op mp_list_module_op) ->
		   let name = (hd (map_isexpr_to_list string_of_itoken_term
						      (term_of_unbound_term symaddr))) in
		   let f x = (Mp.edit_cd_thm name x;
			     let (s, goal, subgoals, extras) = Mp.edit_node [] in
			      ipair_term (itoken_term x) (msequent_to_term goal))

		   and flat_list = get_fl name
		   in icons_term icons_op
			(list_to_ilist_map (function x -> itoken_term (String.uncapitalize x)) flat_list)
			(let (w, c, a, rl) = Mp.edit_list_module name in
			    mp_edit_term (list_to_ilist_map f w) (list_to_ilist_map f c) (list_to_ilist_map f a) (list_to_ilist_map f rl))

	       | {term_op = op; term_terms = symaddr :: r } when (opeq op mp_list_display_op) ->
		   let ff name =
		     let f = function (n, modes, attr, model, formats) ->
		       (ipair_term (itoken_term n)
			  (idform_term (list_to_ilist_by_op idform_attr_op
					  ((list_to_ilist_by_op imode_cons_op (map itoken_term modes)) :: attr))
			     formats
			     model))
		     in
		       ipair_term (imp_prec_pair_term (list_to_ilist_by_op imp_prec_cons_op
							 (edit_list_precs name))
				     (list_to_ilist_by_op_map imp_prec_rel_cons_op
					(function (r, t1, t2) -> imp_prec_rel_term r t1 t2)
					(edit_list_prec_rels name)))
			 (list_to_ilist (List.map f (edit_list_dforms name)))
		   in list_to_ilist_map ff (map (function x -> hd (map_isexpr_to_list string_of_itoken_term x))
					      (map_isexpr_to_list_by_op ilist_op
						 (function x -> x) (term_of_unbound_term symaddr)))

	       | {term_op = op; term_terms = symaddr :: mseq :: r} when (opeq op mp_set_thm_op) ->
		   let l = string_list_of_term (term_of_unbound_term symaddr)
		   in
		   (if l = !current_symaddr then () else Mp.edit_cd_thm (hd (tl l)) (hd (tl (tl l)));
		       let (assums, goal) = term_to_msequent (term_of_unbound_term mseq) in
		       (eprintf "setting goal %s %s %t" (hd (tl l)) (hd (tl (tl l))) eflush;
			 eprintf "TO: %a/%t" print_term goal eflush;
			 Mp.set_goal goal; Mp.set_assumptions assums; ivoid_term))

	       | {term_op = op; term_terms = symaddr :: rw :: r} when (opeq op mp_set_rw_op) ->
		   let l = string_list_of_term (term_of_unbound_term symaddr)
		   in
		   (if l = !current_symaddr then () else Mp.edit_cd_thm (hd (tl l)) (hd (tl (tl l)));
		       let (redex, contract) = dest_rw_term (term_of_unbound_term rw) in
		       (eprintf "setting redex %s %s %t" (hd (tl l)) (hd (tl (tl l))) eflush;
			 eprintf "TO: %a/%a%t" print_term redex print_term contract eflush;
			 Mp.set_redex redex; Mp.set_contractum contract; ivoid_term)) (*use edit_set?*)


 (* cd not needed at command call level*)
 (*
   | {term_op = op; term_terms = symaddr :: r} when (opeq op mp_cd_thm_op) ->
   let l = string_list_of_term (term_of_unbound_term symaddr)
   in
   (current_symaddr := l; Shell.edit_cd_thm (hd (tl l)) (hd (tl (tl l))); ivoid_term)
   *)
	| {term_op = op; term_terms = mname :: name :: r} when (opeq op mp_create_op) ->
	    (Mp.edit_create_thm (string_of_itoken_term (term_of_unbound_term mname))
	       (string_of_itoken_term (term_of_unbound_term name));
	     ivoid_term)

	| {term_op = op; term_terms = mname :: name :: r} when (opeq op mp_create_rw_op) ->
	    (Mp.edit_create_rw (string_of_itoken_term (term_of_unbound_term mname))
	       (string_of_itoken_term (term_of_unbound_term name));
	     ivoid_term)

	| {term_op = op; term_terms = symaddr :: r} when (opeq op mp_lookup_op) ->
	    let l = string_list_of_term (term_of_unbound_term symaddr)
	    in
	    (if l = !current_symaddr then ()
	    else Mp.edit_cd_thm (hd l) (hd (tl l));
	     visit_proof [])

	| _ -> error ["eval"; "op"; "unrecognized"] [] [t])))

    (function term -> (function t -> (ifail_term term)))



let library_open_eval name rhook =

  if not (oref_p library)
  then let host = Sys.getenv "NUPRLLIB_HOST"
  and port = int_of_string (Sys.getenv "NUPRLLIB_PORT")
  in
  lib_open_eval name (refine_ehook rhook) host port (port+2)
    ; ()


let library_loop_eval () =

  let lib = oref_val library in

  (with_transaction lib
     (function t ->
       (eval t
	  (null_ap (itext_term "\l. inform_message nil ``MetaPRL Loop Start`` nil")))))

    ; server_loop lib


let library_open_and_loop_eval name rhook =

  library_open_eval name rhook;

  (unwind_error
     (function () -> library_loop_eval ();
       library_close ())
     (function () -> library_close ()))


let faux_refine g t =
  print_newline();
  Mbterm.print_term g;
  Mbterm.print_term t;
  print_newline();
  [g; g]
