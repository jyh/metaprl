(*
 * Display all the elements in a particular theory.
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

include Itt_theory

open Printf
open Mp_debug

open Refiner.Refiner.Refine

open Mp_resource

open Tacticals
open Conversionals

open Itt_rfun
open Itt_bool
open Itt_int
open Itt_int_bool

declare fact{'i}

interactive_rw reduceFact : fact{'i} <--> fix{f. lambda{i. ifthenelse{eq_int{'i; 0}; 1; .'i *@ 'f ('i -@ 1)}}} 'i

dform fact_df : parens :: "prec"[prec_apply] :: fact{'i} =
   `"fact" " " slot{'i}

let redexC =
   firstC [reduceBeta;
           reduceEQInt;
           reduceFact;
           reduceBoolTrue;
           reduceBoolFalse;
           reduceIfthenelseTrue;
           reduceIfthenelseFalse;
           reduceAdd;
           reduceSub;
           reduceMul;
           reduceDiv;
           reduceFix]

let goal = mk_msequent << sequent { 'H >- fact{300} = 0 in int } >> []

let cache = Tactic_cache.extract (cache_resource.resource_extract cache_resource)

let arg =
   Sequent.create (**)
      (Sequent.sentinal_of_refiner "itt")      (* Sentinal *)
      "main"            (* Label *)
      goal              (* Goal of proof *)
      (Sequent.make_cache (fun () -> cache))             (* Proof cache *)
      []                (* Attributes *)

let test () =
   let subgoals, ext = Tacticals.refine (timingT (rw (repeatC (higherC redexC)) 0)) arg in
      match subgoals with
         [subgoal] ->
            Simple_print.SimplePrint.print_simple_term (Sequent.goal subgoal);
            eflush stdout
       | [] ->
            eprintf "No subgoals%t" eflush
       | _ ->
            eprintf "Too many subgoals%t" eflush

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.top"
 * End:
 * -*-
 *)
