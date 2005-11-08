doc <:doc<
   Define a non-normalized representation of a sequent as a
   sequent.

   ----------------------------------------------------------------

   @begin[license]
   Copyright (C) 2005 Mojave Group, Caltech

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

   Author: Jason Hickey
   @email{jyh@cs.caltech.edu}
   @end[license]

   @parents
>>
extends Itt_hoas_sequent_native

doc docoff

open Basic_tactics

open Itt_list
open Itt_list2
open Itt_dprod

declare Context{'C}
declare Hypothesis{'e}
declare sequent [make_sequent{'arg}] { Term : Term >- Term }

let make_sequent_opname = opname_of_term << make_sequent{'arg} >>
let is_make_sequent_term = is_dep0_term make_sequent_opname
let dest_make_sequent_term = dest_dep0_term make_sequent_opname

let opname_Context = opname_of_term << Context{'C} >>
let is_Context_term = is_dep0_term opname_Context
let dest_Context_term = dest_dep0_term opname_Context

let opname_Hypothesis = opname_of_term << Hypothesis{'e} >>
let is_Hypothesis_term = is_dep0_term opname_Hypothesis
let dest_Hypothesis_term = dest_dep0_term opname_Hypothesis

let opname_bind = opname_of_term << bind{x. 'e['x]} >>
let mk_bind_term = mk_dep1_term opname_bind

let opname_bind_vec = opname_of_term << bind{'l; x. 'e['x]} >>
let mk_bind_vec_term = mk_dep0_dep1_term opname_bind_vec

let mk_list1_term t =
   mk_cons_term t nil_term

let rec mk_rev_append_list_term l hyps =
   match hyps with
      [] ->
         l
    | h :: hyps ->
         mk_rev_append_list_term (mk_append_term h l) hyps

(*
 * Callisfy vars into Context and Hypothesis vars.
 *)
type hyp_var =
   ContextVar of var
 | HypothesisVar of var

(*
 * Bind over the vars in the list.
 *)
let rec quantify_vars vars e =
   match vars with
      v :: vars ->
         let e = quantify_vars vars e in
            (match v with
                ContextVar v ->
                   mk_bind_vec_term v (mk_length_term (mk_var_term v)) e
              | HypothesisVar v ->
                   mk_bind_term v e)
    | [] ->
         e

(*
 * Build the tuple sequent from the native form.
 *)
let make_sequent s =
   let { sequent_args = arg;
         sequent_hyps = hyps;
         sequent_concl = concl
       } = explode_sequent s
   in
   let () =
      if not (is_make_sequent_term arg) then
         raise (RefineError ("Itt_hoas_sequent.make_sequent", StringTermError ("not a sequent", s)))
   in

   (* Collect the hyps *)
   let vars, hyps =
         SeqHyp.fold (fun (vars, hyps) _ h ->
               match h with
                  Hypothesis (x, t) ->
                     if is_Context_term t then
                        let t = quantify_vars vars (dest_Context_term t) in
                        let vars = ContextVar x :: vars in
                           vars, t :: hyps
                     else if is_Hypothesis_term t then
                        let t = quantify_vars vars (dest_Hypothesis_term t) in
                        let t = mk_list1_term t in
                        let vars = HypothesisVar x :: vars in
                           vars, t :: hyps
                     else
                        raise (RefineError ("Itt_hoas_sequent.make_sequent", StringTermError ("malformed sequent", s)))
                | Context _ ->
                     raise (RefineError ("Itt_hoas_sequent.make_sequent", StringTermError ("malformed sequent", s)))) ([], []) hyps
   in
   let hyps = mk_rev_append_list_term nil_term hyps in

   (* Collect the concl *)
   let concl = quantify_vars vars concl in
      mk_pair_term arg (mk_pair_term hyps concl)

ml_rw reduce_make_sequent : ('s : sequent [make_sequent{'arg}] { <H> >- 'C }) =
   make_sequent s

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
