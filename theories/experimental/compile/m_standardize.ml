(*
 * Rename all binding variables so that they
 * are all different.
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
extends Shell_theory
extends M_ir

open Lm_printf
open Lm_symbol

open Term_sig
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermSubst

open Tactic_type.Sequent
open Tactic_type.Tacticals

(*
 * Alpha equality.
 *)
declare equal{'e1; 'e2}

prim alpha_equal :
   sequent { <H> >- equal{'e; 'e} }

prim subst 'e2 :
   sequent { <H> >- 'e2 } -->
   ["wf"] sequent { <H> >- equal{'e1; 'e2} } -->
   sequent { <H> >- 'e1 }

doc <:doc< @docoff >>

let standardizeT =
   funT (fun p -> subst (standardize (concl p)))
   thenWT alpha_equal

(*
 * Destandardize a term.
 *)
let destandardize_var table v =
   try SymbolTable.find table v with
      Not_found ->
         v

let destandardize_var_term table v =
   try mk_var_term (SymbolTable.find table (dest_var v)) with
      Not_found ->
         v

let rec destandardize_term table t =
   if is_var_term t then
      destandardize_var_term table t
   else
      let { term_op = op; term_terms = bterms } = dest_term t in
      let bterms = List.map (destandardize_bterm table) bterms in
         mk_term op bterms

and destandardize_bterm table bterm =
   let { bvars = bvars; bterm = t } = dest_bterm bterm in
   let bvars = List.map (destandardize_var table) bvars in
   let t = destandardize_term table t in
      mk_bterm bvars t

let destandardizeT table =
   funT (fun p -> subst (destandardize_term table (concl p)))
   thenWT alpha_equal

let destandardize_debugT table =
   let vars =
      SymbolTable.fold (fun vars v1 v2 ->
            (v1, v2) :: vars) [] table
   in
   let failT v1 v2 =
      eprintf "Failed on %s -> %s%t" (string_of_symbol v1) (string_of_symbol v2) eflush;
      idT
   in
   let rec debugT vars =
      match vars with
         [] ->
            idT
       | (v1, v2) :: vars ->
            let table = SymbolTable.add SymbolTable.empty v1 v2 in
               ((destandardizeT table thenT debugT vars)
                orelseT failT v1 v2)
   in
      debugT vars

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
