(*
 * We need a rule for when rewrites are valid.
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

include Perv
include Base_auto_tactic

open Mp_debug
open Printf

open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError

open Tactic_type
open Tactic_type.Tacticals

open Var

open Base_auto_tactic

declare rw_just
declare bind{v. 'C['v]}

let bind_term = << bind{v. 'C['v]} >>
let bind_opname = opname_of_term bind_term
let is_bind_term = is_dep1_term bind_opname
let mk_bind_term = mk_dep1_term bind_opname
let dest_bind = dest_dep1_term bind_opname

prim rewriteAxiom 'H :
   sequent ['ext] { 'H >- Perv!"rewrite"{'a; 'a} } =
   rw_just

prim rewriteConcl 'H bind{v. 'C['v]} Perv!"rewrite"{'a; 'b} :
   sequent ['ext] { 'H >- Perv!"rewrite"{'a; 'b} } -->
   ('t : sequent ['ext] { 'H >- 'C['b] }) -->
   sequent ['ext] { 'H >- 'C['a] } =
   't

(*
 * Substitution.
 * The binding term may be optionally supplied.
 *)
let rewriteT t p =
   let a, _ = dest_xrewrite t in
   let bind =
      try
         let t1 = get_with_arg p in
            if is_bind_term t1 then
               t1
            else
               raise (RefineError ("rewriteT", StringTermError ("need a \"bind\" term: ", t)))
      with
         RefineError _ ->
            let x = get_opt_var_arg "z" p in
               mk_bind_term x (var_subst (Sequent.concl p) a x)
   in
      rewriteConcl (Sequent.hyp_count_addr p) bind t p

let d_rewrite_axiomT p =
   rewriteAxiom (Sequent.hyp_count_addr p) p

let trivial_resource =
   Mp_resource.improve trivial_resource (**)
      { auto_name = "triv_equalT";
        auto_prec = trivial_prec;
        auto_tac = d_rewrite_axiomT
      }

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
