doc <:doc<
   @module[Itt_vec_bind]

   Vector binder.

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
extends Meta_context_theory
extends Itt_theory
extends Itt_match

doc docoff

open Lm_printf

open Basic_tactics
open Simple_print
open Itt_squiggle
open Itt_struct
open Itt_dfun

declare Invalid_argument

(************************************************************************
 * Simple version.
 *)
doc <:doc<
   The bind terms are modeled after the terms in Itt_hoas_base.
   The function space is marked by a disjoint union.
>>
define unfold_mk_bind : mk_bind{x. 'e['x]} <-->
   inl{lambda{x. 'e['x]}}

define unfold_mk_core : mk_core{'e} <-->
   inr{'e}

define unfold_dest_bind : dest_bind{'e; 'bind; t. 'core['t]} <-->
   decide{'e; x. 'bind; y. 'core['y]}

define unfold_bind_subst : bind_subst{'e1; 'e2} <-->
   decide{'e1; f. 'f 'e2; x. "Invalid_argument"}

doc <:doc<
   Rewriting for the << dest_bind{'e; 'bind; t. 'core['t]} >> term.
>>
interactive_rw reduce_dest_bind_bind {| reduce |} :
   dest_bind{mk_bind{x. 'e1['x]}; 'base; t. 'core['t]}
   <-->
   'base

interactive_rw reduce_dest_bind_core {| reduce |} :
   dest_bind{mk_core{'e1}; 'base; t. 'core['t]}
   <-->
   'core['e1]

interactive_rw reduce_subst_bind {| reduce |} :
   bind_subst{mk_bind{x. 'e1['x]}; 'e2}
   <-->
   'e1['e2]

(************************************************************************
 * Vector version.
 *)
doc <:doc<
   A vector binding ignores the actual hyp values and just performs a bind
   of the comclusion.
>>
prim_rw unfold_mk_vbind : <:xrewrite<
   "mk_vbind"{| <J> >- C |}
   <-->
   sequent_ind{u, v. mk_bind{x. happly{v; x}}; "TermSequent"{| <J> >- C |}}
>>

doc <:doc<
   Reductions.
>>
interactive_rw reduce_mk_vbind_nil {| reduce |} : <:xrewrite<
   "mk_vbind"{| >- C |}
   <-->
   C
>>

interactive_rw reduce_mk_vbind_left : <:xrewrite<
   "mk_vbind"{| x: A; <J[x]> >- C[x] |}
   <-->
   mk_bind{x. "mk_vbind"{| <J[x]> >- C[x] |}}
>>

interactive_rw reduce_mk_vbind_right : <:xrewrite<
   "mk_vbind"{| <J>; x: A >- C[x] |}
   <-->
   "mk_vbind"{| <J> >- mk_bind{x. C[x]} |}
>>

interactive_rw reduce_mk_vbind_merge : <:xrewrite<
   "mk_vbind"{| <J> >- "mk_vbind"{| <K> >- C |} |}
   <-->
   "mk_vbind"{| <J>; <K> >- C |}
>>

let reduceVBindC = repeatC (reduceC thenC (higherC reduce_mk_vbind_left) thenC (higherC reduce_mk_vbind_right))

(************************************************************************
 * Dummy substitution.
 *)
declare sequent [vsubst_dummy] { Term : Term >- Term } : Term

prim_rw unfold_vsubst_dummy : <:xrewrite<
   "vsubst_dummy"{| <J> >- C |}
   <-->
   sequent_ind{u, v. happly{v; "it"}; "TermSequent"{| <J> >- C |}}
>>

interactive_rw reduce_vsubst_dummy_nil {| reduce |} : <:xrewrite<
   "vsubst_dummy"{| >- C |}
   <-->
   C
>>

interactive_rw reduce_vsubst_dummy_left {| reduce |} : <:xrewrite<
   "vsubst_dummy"{| x: A; <J[x]> >- C[x] |}
   <-->
   "vsubst_dummy"{| <J["it"]> >- C["it"] |}
>>

interactive_rw reduce_vsubst_dummy_right {| reduce |} : <:xrewrite<
   "vsubst_dummy"{| <J>; x: A >- C[x] |}
   <-->
   "vsubst_dummy"{| <J> >- C["it"] |}
>>

interactive_rw reduce_vsubst_dummy_null {| reduce |} : <:xrewrite<
   "vsubst_dummy"{| <J> >- e<||> |}
   <-->
   e
>>

interactive_rw reduce_vsubst_dummy_middle 'J : <:xrewrite<
   "vsubst_dummy"{| <J>; x: A; <K[x]> >- e[x] |}
   <-->
   "vsubst_dummy"{| <J>; <K["it"]> >- e["it"] |}
>>

interactive_rw reduce_vsubst_dummy_core {| reduce |} : <:xrewrite<
   "vsubst_dummy"{| <J> >- mk_core{e} |}
   <-->
   mk_core{"vsubst_dummy"{| <J> >- e |}}
>>

interactive_rw reduce_vsubst_dummy_cons {| reduce |} : <:xrewrite<
   "vsubst_dummy"{| <J> >- e1 :: e2 |}
   <-->
   "vsubst_dummy"{| <J> >- e1 |} :: "vsubst_dummy"{| <J> >- e2 |}
>>

(************************************************************************
 * List version.
 *)
doc <:doc<
   The list binding is like a vector binding, but wraps the binders
   in a list.  Use unit lists (unary natural numbers) instead of
   << nat >> to avoid wf subgoals.
>>
define unfold_mk_lbind : mk_lbind{'n; x. 'e['x]} <--> <:xterm<
   list_ind{n; lambda{f. f "nil"}; u, v, g. lambda{f. mk_bind{x. g (lambda{l. f (x :: l)})}}} lambda{x. e[x]}
>>

define unfold_bind_substl : bind_substl{'e; 'l} <--> <:xterm<
   list_ind{l; lambda{e. e}; u, v, g. lambda{e. g bind_subst{e; u}}} e
>>

declare sequent [vbind_arity] { Term : Term >- Term } : Term

prim_rw unfold_vbind_arity : <:xrewrite<
   "vbind_arity"{| <J> >- C |}
   <-->
   sequent_ind{u, v. "it" :: happly{v; "it"}; "TermSequent"{| <J> >- [] |}}
>>

doc docoff

(*
 * Reductions.
 *)
interactive_rw reduce_vbind_arity_nil {| reduce |} : <:xrewrite<
   "vbind_arity"{| >- C |}
   <-->
   []
>>

interactive_rw reduce_mk_lbind_zero {| reduce |} : <:xrewrite<
   mk_lbind{[]; x. e[x]}
   <-->
   e["nil"]
>>

interactive_rw reduce_bind_substl_nil {| reduce |} : <:xrewrite<
   bind_substl{e; []}
   <-->
   e
>>

interactive_rw reduce_vbind_arity_cons {| reduce |} : <:xrewrite<
   "vbind_arity"{| x: A; <J[x]> >- C[x] |}
   <-->
   "it" :: "vbind_arity"{| <J["it"]> >- C["it"] |}
>>

interactive_rw reduce_mk_lbind_succ {| reduce |} : <:xrewrite<
   mk_lbind{z::n; l. e[l]}
   <-->
   mk_bind{x. mk_lbind{n; l. e[x:: l]}}
>>

interactive_rw reduce_bind_substl_cons {| reduce |} : <:xrewrite<
   bind_substl{e; u::v}
   <-->
   bind_substl{bind_subst{e; u}; v}
>>

(*
 * Well-formedness rules.
 *)
interactive vbind_arity_wf {| intro [] |} : <:xrule<
   <H> >- "vbind_arity"{| <J> >- C |} IN list{"unit"}
>>

interactive vsubst_dummy_vbind_arity_wf {| intro [] |} : <:xrule<
   <H> >- "vsubst_dummy"{| <J> >- "vbind_arity"{| <K> >- C |} |} IN list{"unit"}
>>

doc <:doc<
   The most important use of << mk_lbind{'n; x. 'e['x]} >> is to
   eta-expand a vector binding.
>>

interactive_rw vbind_eta_expand : <:xrewrite<
   "mk_vbind"{| <J> >- C |}
   <-->
   mk_lbind{"vbind_arity"{| <J> |}; l. bind_substl{"mk_vbind"{| <J> >- C |}; l}}
>>

doc <:doc<
   Move the binder inward.
>>
interactive_rw vbind_subst_push Perv!bind{x. 'C['x]} 'e : <:xrewrite<
   mk_lbind{"vbind_arity"{| <J> |}; l. bind_substl{"mk_vbind"{| <J> >- C<||>[e] |}; l}}
   <-->
   mk_lbind{"vbind_arity"{| <J> |}; l. C[bind_substl{"mk_vbind"{| <J> >- e |}; l}]}
>>

interactive_rw vbind_subst_push2 Perv!bind{x. 'C['x]} 'e : <:xrewrite<
   mk_lbind{"vbind_arity"{| <J> |}; l. bind_substl{"mk_vbind"{| <J> >- C[e] |}; l}}
   <-->
   mk_lbind{"vbind_arity"{| <J> |}; l. bind_substl{"mk_vbind"{| <J> >- C[bind_substl{"mk_vbind"{| <J> >- e |}; l}] |}; l}}
>>

(************************************************************************
 * Tactics.
 *)
let mk_empty_vbind_term t =
   <:con< sequent [mk_vbind] { >- $t$ } >>

let mk_vbind_arg_term = << mk_vbind >>
let mk_vbind_arg_opname = opname_of_term mk_vbind_arg_term
let is_mk_vbind_arg_term = is_no_subterms_term mk_vbind_arg_opname

let is_mk_vbind_term t =
   is_sequent_term t && is_mk_vbind_arg_term (TermMan.args t)

let mk_mk_vbind_term hyps t =
   let s =
      { sequent_args = mk_vbind_arg_term;
        sequent_hyps = hyps;
        sequent_concl = t
      }
   in
      mk_sequent_term s

let dest_mk_vbind_term t =
   let { sequent_args = arg;
         sequent_hyps = hyps;
         sequent_concl = concl
       } = explode_sequent t
   in
      if is_mk_vbind_arg_term arg then
         hyps, concl
      else
         raise (RefineError ("dest_vbind_term", StringTermError ("not a mk_vbind term", t)))

let mk_lbind_term = << mk_lbind{'n; l. 'e} >>
let mk_lbind_opname = opname_of_term mk_lbind_term
let is_mk_lbind_term = is_dep0_dep1_term mk_lbind_opname
let dest_mk_lbind_term = dest_dep0_dep1_term mk_lbind_opname

let bind_substl_term = << bind_substl{'e1; 'e2} >>
let bind_substl_opname = opname_of_term bind_substl_term
let dest_bind_substl_term = dest_dep0_dep0_term bind_substl_opname

let wrap_vbind p =
   let t = concl p in
   let t1, t2 = dest_squiggle t in
   let t1 = mk_empty_vbind_term t1 in
   let t2 = mk_empty_vbind_term t2 in
   let t = mk_squiggle_term t1 t2 in
      assertT t
      thenLT [idT; rw (addrC [Subterm 1] reduceTopC thenC addrC [Subterm 2] reduceTopC) (-1) thenT nthHypT (-1)]

let wrapVBindT = funT wrap_vbind

(*
 * Bind pushing.
 *)
let var_x = Lm_symbol.add "x"

let push_vbind_subst t1 t =
   if is_mk_lbind_term t then
      let _, _, c = dest_mk_lbind_term t in
      let c, _ = dest_bind_substl_term c in
      let c = TermMan.concl c in
      let fv = free_vars_set c in
      let x = maybe_new_var_set var_x fv in
      let t_var = var_subst c t1 x in
      let t_bind = mk_bind1_term x t_var in
         vbind_subst_push t_bind t1 orelseC vbind_subst_push2 t_bind t1
   else
      raise (RefineError ("push_vbind_subst", StringError "not a mk_lbind term"))

let pushVBindSubstC t1 = termC (push_vbind_subst t1)

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
