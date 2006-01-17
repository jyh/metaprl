(*
 * Sequent contexts.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2005 Mojave Group, Caltech
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
extends Base_theory

open Lm_printf

open Basic_tactics
open Simple_print

doc <:doc<
   The meta-lambda calculus includes typed functions << hlambda{'A; x. 'e['x]} >>
   and application << happly{'e1; 'e2} >>.  There is also a destructor
   << htype{'e} >> that produces the type of the function << 'e >>.
>>
prim_rw reduce_hbeta {| reduce |} :
   happly{hlambda{'A; x. 'e1['x]}; 'e2}
   <-->
   'e1['e2]

prim_rw reduce_htype {| reduce |} :
   htype{hlambda{'A; x. 'e['x]}}
   <-->
   'A

doc docoff

(*
 * Inference on the raw terms is not possible because
 * of the location of quantifiers.  Add type constraint terms.
 *)
declare hyp_constrain{'arg : ty_sequent{ty_hyp{'a; 'b}; 'c; 'd}; 'B : 'b; x : 'a. 's['x] : 'e}

declare concl_constrain{'arg : ty_sequent{ty_hyp{'a; 'b}; 'c; 'd};
                        x : ty_sequent{ty_hyp{'a; 'b}; 'c; 'd}, y: 'c. 'concl : 'e}

doc <:doc<
   The << concl{'arg; 'c} >> produces a sequent with no hypotheses,
   conclusion << 'c >>, and sequent argument << 'arg >>.

   The << hyp{'A; x. 'e['x]} >> adds the hypothesis $x : A$ to the
   sequent << 'e['x] >>.
>>
define unfold_concl {| reduce |} : concl{'arg : ty_sequent{ty_hyp{'a; 'b}; 'c; 'd}; 'concl : 'c} : 'd <-->
   sequent ['arg] { >- 'concl }

prim_rw reduce_hyp hyp_constrain{'arg; 'A; y. sequent ['arg] { <H['y]> >- 'C['y] }} :
   hyp{'A; x. sequent ['arg] { <H['x]> >- 'C['x] }}
   <-->
   sequent ['arg] { x: 'A; <H['x]> >- 'C['x] }

doc <:doc<
   The induction combinator << sequent_ind{a, c. 'concl['a; 'c]; h. 'step['h]; 's} >>
   computes over the sequent << 'e >>.  In the base case, << 'a >> is the sequent
   argument and << 'c >> is the conclusion.  In the step case, << 'h >> is a
   meta-lambda << hlambda{'A; x. 's['x]} >> that represents a hypothesis.
>>
prim_rw reduce_sequent_ind_base1 concl_constrain{'arg; x, y. 'concl['x; 'y]} :
   sequent_ind{x, y. 'concl['x; 'y]; h. 'step['h]; sequent ['arg] { <H> >- 'C }}
   <-->
   sequent_ind{h. 'step['h]; SequentTerm{| <H> >- 'concl['arg; 'C] |}}

(*
 * Reduce the inner induction form.
 *)
prim_rw reduce_sequent_ind_base2 {| reduce |} :
   sequent_ind{h. 'step['h]; SequentTerm{| >- 'C |}}
   <-->
   'C

prim_rw reduce_sequent_ind_left {| reduce |} :
   sequent_ind{h. 'step['h]; SequentTerm{| x: 'A; <H['x]> >- 'C['x] |}}
   <-->
   'step[hlambda{'A; x. sequent_ind{h. 'step['h]; SequentTerm{| <H['x]> >- 'C['x] |}}}]

doc docoff

(************************************************
 * ML code.
 *)

(*
 * Hypothesis reduction.
 *)
let hyp_opname = opname_of_term << hyp{'A; x. 'e} >>
let mk_hyp_term = mk_dep0_dep1_term hyp_opname
let dest_hyp_term = dest_dep0_dep1_term hyp_opname

let hlambda_opname = opname_of_term << hlambda{'A; x. 'e} >>
let mk_hlambda_term = mk_dep0_dep1_term hlambda_opname
let dest_hlambda_term = dest_dep0_dep1_term hlambda_opname

let hyp_constrain_opname = opname_of_term << hyp_constrain{'arg; 'A; x. 'e} >>
let mk_hyp_constrain_term = mk_dep0_dep0_dep1_term hyp_constrain_opname
let dest_hyp_constrain_term = dest_dep0_dep0_dep1_term hyp_constrain_opname

let reduce_hyp t =
   let x, a, s = dest_hyp_term t in
   let arg = Refiner.Refiner.TermMan.args s in
   let c = mk_hyp_constrain_term arg a x s in
      reduce_hyp c

(*
 * Sequent_ind reduction.
 *)
let mk_dep2_dep1_dep0_term opname x1 y1 e1 x2 e2 e3 =
   let bterms =
      [mk_bterm [x1; y1] e1;
       mk_bterm [x2] e2;
       mk_bterm [] e3]
   in
   let op = mk_op opname [] in
      mk_term op bterms

let dest_dep2_dep1_dep0_term opname t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = opname'; op_params = params } = dest_op op in
      if Opname.eq opname' opname then
         match params, bterms with
            [], [b1; b2; b3] ->
               (match dest_bterm b1, dest_bterm b2, dest_bterm b3 with
                   { bvars = [x1; y1]; bterm = t1 },
                   { bvars = [x2]; bterm = t2 },
                   { bvars = []; bterm = t3 } ->
                      x1, y1, t1, x2, t2, t3
                 | _ ->
                      raise (RefineError ("dest_dep2_dep1_dep0_term", StringTermError ("bad arity", t))))
          | _ ->
               raise (RefineError ("dest_dep2_dep1_dep0_term", StringTermError ("bad arity", t)))
      else
         raise (RefineError ("dest_dep2_dep1_dep0_term", StringTermError ("opname mismatch", t)))

let sequent_ind_opname = opname_of_term << sequent_ind{x, y. 'concl['x; 'y]; h. 'step['h]; 'e} >>
let mk_sequent_ind_term = mk_dep2_dep1_dep0_term sequent_ind_opname
let dest_sequent_ind_term = dest_dep2_dep1_dep0_term sequent_ind_opname

let concl_constrain_opname = opname_of_term << concl_constrain{'arg; x, y. 'e} >>
let mk_concl_constrain_term = mk_dep0_dep2_term concl_constrain_opname
let dest_concl_constrain_term = dest_dep0_dep2_term concl_constrain_opname

let reduce_concl t =
   let x, y, concl, h, step, s = dest_sequent_ind_term t in
   let arg = Refiner.Refiner.TermMan.args s in
   let c = mk_concl_constrain_term x y arg concl in
      reduce_sequent_ind_base1 c

let reduce_concl_conv = termC reduce_concl

(*
 * Add the reductions.
 *)
let resource reduce +=
   [<< hyp{'A; x. sequent ['arg] { <H['x]> >- 'C['x] }} >>, wrap_reduce (termC reduce_hyp);
    << sequent_ind{x, y. 'concl['x; 'y]; h. 'step['h]; sequent ['arg] { <H> >- 'C }} >>, wrap_reduce (termC reduce_concl)]

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
