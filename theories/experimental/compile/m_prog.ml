(*!
 * @begin[doc]
 * @module[M_prog]
 *
 * Lift closed function definitions to the top level.
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

open Mp_debug
open Printf

open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermAddr

open Tactic_type.Tacticals
open Tactic_type.Sequent

open Var
open Perv

(*!
 * @begin[doc]
 * The following two rules hoist function declarations and definitions.
 * @end[doc]
 *)
interactive hoist_fundecl 'H bind{x. 'A['x]} FunDecl{f. 'e['f]} :
   sequent [m] { 'H; f: exp >- 'A['e['f]] } -->
   sequent [m] { 'H >- 'A[FunDecl{f. 'e['f]}] }

interactive hoist_fundef 'H bind{x. 'A['x]} FunDef{'f; 'e1; 'e2} :
   sequent [m] { 'H; w: def{'f; 'e1} >- 'A['e2] } -->
   sequent [m] { 'H >- 'A[FunDef{'f; 'e1; 'e2}] }

(*!
 * @begin[doc]
 * A tactic to apply the hoisting rules.
 * @end[doc]
 *)
exception Found of address

let declareT p =
   let goal = concl p in
   let rec search addr t =
      if is_fundecl_term t then
         raise (Found (make_address (List.rev addr)));
      search_subterms addr 0 (subterms_of_term t)
   and search_subterms addr next tl =
      match tl with
         t :: tl ->
            search (next :: addr) t;
            search_subterms addr (succ next) tl
       | [] ->
            ()
   in
   let goal = concl p in
   let tac =
      try search [] goal; failT with
         Found addr ->
            let decl = term_subterm goal addr in
            let x = get_opt_var_arg "z" p in
            let a = replace_subterm goal addr (mk_var_term x) in
            let bind = mk_bind1_term x a in
               eprintf "Bind: %a\nDecl: %a%t" debug_print bind debug_print decl eflush;
               hoist_fundecl (hyp_count_addr p) bind decl
   in
      tac p

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
