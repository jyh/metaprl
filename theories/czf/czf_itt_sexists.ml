(*
 * Primitiva axiomatization of implication.
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
 * Author: Jason Hickey
 * jyh@cs.cornell.edu
 *)

include Czf_itt_and

open Printf
open Mp_debug

open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Tactic_type.Sequent
open Var

open Itt_logic
open Itt_rfun

let _ =
   show_loading "Loading Czf_itt_exists%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "sexists"{x. 'A['x]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

prim_rw unfold_sexists : "sexists"{x. 'A['x]} <--> (exst x: set. 'A['x])

let fold_sexists = makeFoldC << "sexists"{x. 'A['x]} >> unfold_sexists

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform sexists_df : mode[prl] :: parens :: "prec"[prec_lambda] :: "sexists"{x. 'A} =
   pushm[0] Nuprl_font!"exists" slot{'x} `"." slot{'A} popm

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typing.
 *)
interactive sexists_type 'H 'y :
   sequent [squash] { 'H; y: set >- "type"{'A['y]} } -->
   sequent ['ext] { 'H >- "type"{."sexists"{x. 'A['x]} } }

(*
 * Intro.
 *)
interactive sexists_intro 'H 'z 'w :
   sequent ['ext] { 'H >- isset{'z} } -->
   sequent ['ext] { 'H >- 'A['z] } -->
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H >- "sexists"{x. 'A['x]} }

(*
 * Elimination.
 *)
interactive sexists_elim 'H 'J 'x 'z 'w :
   sequent ['ext] { 'H;
                    z: set;
                    w: 'A['z];
                    'J[pair{'z; 'w}]
                    >- 'T[pair{'z; 'w}]
                  } -->
   sequent ['ext] { 'H; x: "sexists"{y. 'A['y]}; 'J['x] >- 'T['x] }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Propositional reasoning.
 *)
let d_sexistsT i p =
   if i = 0 then
      let z = get_with_arg p in
      let w = maybe_new_vars1 p "v" in
         (sexists_intro (hyp_count_addr p) z w
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "main";
                  addHiddenLabelT "wf"]) p
   else
      let x, _ = nth_hyp p i in
      let z, w = Var.maybe_new_vars2 p "u" "v" in
      let i, j = hyp_indices p i in
          sexists_elim i j x z w p

let sexists_term = << "sexists"{x. 'B['x]} >>

let d_resource = Mp_resource.improve d_resource (sexists_term, d_sexistsT)

(*
 * Well-formedness.
 *)
let d_exists_typeT i p =
   if i = 0 then
      let v = maybe_new_vars1 p "v" in
         sexists_type (hyp_count_addr p) v p
   else
      raise (RefineError ("d_exists_typeT", StringError "no elim form"))

let sexists_type_term = << "type"{sexists{x. 'B['x]}} >>

let d_resource = Mp_resource.improve d_resource (sexists_type_term, d_exists_typeT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
