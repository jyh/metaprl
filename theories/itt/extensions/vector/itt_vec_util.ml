(*
 * Some frequently-used utilities.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2006 Mojave Group, Caltech
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
open Lm_printf

open Basic_tactics
open Base_trivial

let var_x = Lm_symbol.add "x"

(*
 * In many case, we have rules that say the the hyp values do not matter.
 * The rules have the following form:
 *
 * rewrite foo Perv!bind{x. arg{| <J[x]> >- e |}} :
 *    arg{| <J[t]> >- e |}
 *    <-->
 *    arg{| <J[it]> >- e |}
 *
 * The following function takes a rule of this form and computes
 * and appropriate argument.
 *)
let squash_rewrite_arg t =
   let { sequent_args = arg;
         sequent_hyps = hyps;
         sequent_concl = concl
       } = explode_sequent t
   in

   (*
    * Find the term to be replaced.
    *)
   let x = maybe_new_var_set var_x (all_vars t) in
   let x_t = mk_var_term x in
   let rec search rev_hyps hyps =
      match hyps with
         [] ->
            raise (RefineError ("reduce_length_fun_term_conv", StringTermError ("already converted", t)))
       | Context (z, cv, args) as hyp :: hyps ->
            let rec search_args rev_args args =
               match args with
                  arg :: args ->
                     if is_it_term arg then
                        search_args (arg :: rev_args) args
                     else
                        rev_hyps, Context (z, cv, List.rev_append rev_args (x_t :: args)), hyps
                | [] ->
                     search (hyp :: rev_hyps) hyps
            in
               search_args [] args
       | Hypothesis (z, t) as hyp :: hyps ->
            if is_it_term t then
               search (hyp :: rev_hyps) hyps
            else
               rev_hyps, Hypothesis (z, x_t), hyps
   in
   let rev_hyps, hyp, hyps = search [] (SeqHyp.to_list hyps) in
   let eseq =
      { sequent_args = arg;
        sequent_hyps = SeqHyp.of_list (List.rev_append rev_hyps (hyp :: hyps));
        sequent_concl = concl
      }
   in
   let t_var = mk_sequent_term eseq in
      mk_bind1_term x t_var

(*
 * -*-
 * Local Variables:
 * Fill-column: 100
 * End:
 * -*-
 * vim:ts=3:et:tw=100
 *)
