(*!
 * @begin[doc]
 * @module[M_closure]
 *
 * Closure conversion for the @emph{M} language.  We close
 * a function by repeating two steps.
 *
 * @begin[enumerate]
 * @item{First, assume we have a function with a free variable $y$.
 *
 *
 * @begin[verbatim]
 * declare f in
 * define f = e1[f] in
 * e2[f]
 * <-->
 * declare f
 * define f = lambda{y. e1[f]} y in
 * e2[f]
 * @end[verbatim]}
 *
 * @item{Next, apply the following transformation.
 *
 * @begin[verbatim]
 * declare f in
 * define f = lambda{y. e1[y,f]} a in
 * e2[f]
 * <-->
 * declare f in
 * define f =
 *    lambda{y.
 *       let closure g = f(y) in
 *          e1[y,g]}
 * in
 * let closure g = f(a) in
 *    e2[g]
 * @end[verbatim]}
 * @end[enumerate]
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2003 Jason Hickey, Caltech
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

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
extends M_ir
(*! @docoff *)

open M_ir

open Printf
open Mp_debug
open String_set

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError

open Mp_resource
open Simple_print
open Term_match_table

open Tactic_type.Conversionals
open Tactic_type.Sequent

(*!
 * @begin[doc]
 * @modsubsection{Phase 1}
 *
 * In the first phase, apply inverse beta reduction to abstract
 * free variables from function bodies.  We use a custom version of
 * $@lambda$ and function application.
 * @end[doc]
 *)
declare CloseLambda{x. 'e['x]}
declare CloseApply{'e1; 'e2}

prim_rw reduce_beta : CloseApply{CloseLambda{x. 'e1['x]}; 'e2} <--> 'e1['e2]

(*
 * Display.
 *)
prec prec_apply
prec prec_lambda
prec prec_lambda < prec_apply

dform apply_df : parens :: "prec"[prec_apply] :: CloseApply{'f; 'a} =
   slot["lt"]{'f} " " slot["le"]{'a}

dform lambda_df : parens :: except_mode [src] :: "prec"[prec_lambda] :: CloseLambda{x. 'b} =
   Nuprl_font!lambda Nuprl_font!subc slot{'x} `"." slot{'b}


let lambda_term = << CloseLambda{x. 'e['x]} >>
let lambda_opname = opname_of_term lambda_term
let is_lambda_term = is_dep1_term lambda_opname
let dest_lambda = dest_dep1_term lambda_opname
let mk_lambda_term = mk_dep1_term lambda_opname

let apply_term = << CloseApply{'e1; 'e2} >>
let apply_opname = opname_of_term apply_term
let is_apply_term = is_dep0_dep0_term apply_opname
let dest_apply = dest_dep0_dep0_term apply_opname
let mk_apply_term = mk_dep0_dep0_term apply_opname

(*
 * Now, a conversional to apply the inverse-beta reduction.
 *)
let abstractTopC vars =
   let convC e =
      let t = env_term e in
         if is_fundef_term t then
            let f, e1, e2 = dest_fundef_term t in
            let rec search l =
               match l with
                  v :: l ->
                     if StringSet.mem vars v then
                        search l
                     else
                        let lambda = mk_lambda_term v e1 in
                        let apply = mk_apply_term lambda (mk_var_term v) in
                           addrC [1] (foldC apply reduce_beta)
                | [] ->
                     failC
            in
               search (free_vars_list e1)
         else
            failC
   in
      funC convC

(*
 * Define a tactic to do the rewriting.
 * We first want to collect all the functions that are declared.
 * Those are not free.
 *)
let abstractT p =
   let rec collect vars t =
      if is_fundecl_term t then
         let v, t = dest_fundecl_term t in
            collect (StringSet.add vars v) t
      else
         List.fold_left collect vars (subterms_of_term t)
   in
   let vars = collect StringSet.empty (concl p) in
      rwh (abstractTopC vars) 0 p

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
