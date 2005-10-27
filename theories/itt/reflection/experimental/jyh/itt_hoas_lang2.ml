(*
 * Some utilities for wrapping and simplifying the reflection theory.
 * We define a new kind of language olang{'ops}, where 'ops is an
 * operator list, and we define several simplified theorems, including
 * induction, and squiggle equality.
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
doc <:doc< @parents >>

extends Itt_hoas_lang
extends Itt_image
extends Itt_subset

doc docoff

open Lm_printf

open Simple_print
open Basic_tactics
open Itt_list
open Itt_struct

(************************************************************************
 * Utilities.
 *)

(*
 * Fold up Aleksey's dummy term.
 *)
define unfold_dummy :
   dummy
   <-->
   mk_term{it; nil}

let fold_dummy = makeFoldC << dummy >> unfold_dummy

(************************************************************************
 * Operators.
 *)

doc <:doc<
   A language is defined by a set of operators << SubOp{'ops} >>, where
   << 'ops >> is a list of operators.  The following rules define case
   analysis on the operator set.
>>

(*
 * Case analysis on operators in a language.
 *)
interactive operator_elim_cons {| elim [] |} 'H :
   [wf] sequent { <H>; op: SubOp{'h :: 't}; <J['op]> >- 'h in Operator } -->
   [wf] sequent { <H>; op: SubOp{'h :: 't}; <J['op]> >- 't in list{Operator} } -->
   [base] sequent { <H>; op: SubOp{'h :: 't}; <J['h]> >- 'C['h] } -->
   [main] sequent { <H>; op: SubOp{'t}; <J['op]> >- 'C['op] } -->
   sequent { <H>; op: SubOp{'h :: 't}; <J['op]> >- 'C['op] }

interactive operator_elim_nil {| elim [] |} 'H :
   sequent { <H>; op: SubOp{nil}; <J['op]> >- 'C['op] }

doc docoff

let listmem_opname = opname_of_term << SubOp{'ops} >>
let dest_listmem_term = dest_dep0_dep0_term listmem_opname

let rec opset_elim i p =
   let t = nth_hyp p i in
   let ops, _ = dest_listmem_term t in
      if is_cons_term ops then
         operator_elim_cons i thenLT [idT; idT; thinT i; funT (opset_elim i)]
      else if is_nil_term ops then
         operator_elim_nil i
      else
         raise (RefineError ("elim_operator", StringTermError ("non-constant term", t)))

let opset_elimT i =
   funT (opset_elim i)

let resource elim +=
    [<< SubOp{'h :: 't} >>, opset_elimT;
     << SubOp{nil} >>,      opset_elimT]

(************************************************************************
 * Our version of a language is defined by a list of operators.
 *)
define unfold_olang :
   olang{'ops}
   <-->
   Lang{SubOp{'ops}}

let fold_olang = makeFoldC << olang{'ops} >> unfold_olang

dform olang_df : olang{'ops} =
   `"OLang(" slot{'ops} `")"

doc <:doc<
   The << olang{'ops} >> type defines a language over the list of
   operators << 'ops >>.  The "o" in "olang" stands for "operator."
>>
interactive olang_wf {| intro [] |} :
   [wf] sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- olang{'ops} Type }

doc docoff

doc <:doc<
   The induction rule.
>>
interactive olang_elim {| elim [] |} 'H :
   [wf] sequent { <H>; e: olang{'ops}; <J['e]> >- 'ops in list{Operator} } -->
   [base] sequent { <H>; e: olang{'ops}; <J['e]>; x: Var >- 'P['x] } -->
   [step] sequent { <H>; e: olang{'ops}; <J['e]>;
       depth: nat;
       op: listmem_set{'ops; Operator};
       subs: list{olang{'ops}};
       compatible_shapes{'depth; shape{'op}; 'subs};
       all_list{'subs; t. 'P['t]} >- 'P[mk_bterm{'depth; 'op; 'subs}] } -->
   sequent { <H>; e: olang{'ops}; <J['e]> >- 'P['e] }

doc docoff

(************************************************************************
 * Shapes.
 *)

(*
 * Basic well-formedness we could not prove before.
 *)
interactive bdepth_wf {| intro [intro_typeinf << 'e >>] |} olang{'ops} :
   [wf] sequent { <H> >- 'ops in list{Operator} } -->
   [wf] sequent { <H> >- 'e in olang{'ops} } -->
   sequent { <H> >- bdepth{'e} in nat }

interactive bdepth_wf_int {| intro [intro_typeinf << 'e >>] |} olang{'ops} :
   [wf] sequent { <H> >- 'ops in list{Operator} } -->
   [wf] sequent { <H> >- 'e in olang{'ops} } -->
   sequent { <H> >- bdepth{'e} in int }

(*
 * Well-formedness.
 *)
doc <:doc<
    The << compatible_shapes{'depth; 'shape; 'subterms} >> predicate defines when
    a list of subterms << 'subterms >> is compatible with a specific operator.
>>
interactive compatible_shapes_wf {| intro [intro_typeinf << 'l2 >>] |} list{olang{'ops}} :
    [wf] sequent { <H> >- 'ops in list{Operator} } -->
    [wf] sequent { <H> >- 'depth in int } -->
    [wf] sequent { <H> >- 'l1 in list{int} } -->
    [wf] sequent { <H> >- 'l2 in list{olang{'ops}} } -->
    sequent { <H> >- compatible_shapes{'depth; 'l1; 'l2} Type }

doc docoff

(*
 * Useful lemmas for proving the compatible_shapes_intro rule.
 *)
interactive compatible_shapes_length_elim 'H 'ops :
   [wf] sequent { <H>; u: compatible_shapes{'depth; 'l1; 'l2}; <J['u]> >- 'depth in nat } -->
   [wf] sequent { <H>; u: compatible_shapes{'depth; 'l1; 'l2}; <J['u]> >- 'ops in list{Operator} } -->
   [wf] sequent { <H>; u: compatible_shapes{'depth; 'l1; 'l2}; <J['u]> >- 'l1 in list{int} } -->
   [wf] sequent { <H>; u: compatible_shapes{'depth; 'l1; 'l2}; <J['u]> >- 'l2 in list{olang{'ops}} } -->
   sequent { <H>; u: compatible_shapes{'depth; 'l1; 'l2}; length{'l1} = length{'l2} in int; <J['u]> >- 'C['u] } -->
   sequent { <H>; u: compatible_shapes{'depth; 'l1; 'l2}; <J['u]> >- 'C['u] }

interactive compatible_shapes_index_elim 'H 'ops :
   [wf] sequent { <H>; u: compatible_shapes{'depth; 'l1; 'l2}; <J['u]> >- 'depth in nat } -->
   [wf] sequent { <H>; u: compatible_shapes{'depth; 'l1; 'l2}; <J['u]> >- 'ops in list{Operator} } -->
   [wf] sequent { <H>; u: compatible_shapes{'depth; 'l1; 'l2}; <J['u]> >- 'l1 in list{int} } -->
   [wf] sequent { <H>; u: compatible_shapes{'depth; 'l1; 'l2}; <J['u]> >- 'l2 in list{olang{'ops}} } -->
   sequent { <H>; u: compatible_shapes{'depth; 'l1; 'l2}; <J['u]>; all i: Index{'l1}. 'depth +@ nth{'l1; 'i} = bdepth{nth{'l2; 'i}} in int >- 'C['u] } -->
   sequent { <H>; u: compatible_shapes{'depth; 'l1; 'l2}; <J['u]> >- 'C['u] }

interactive compatible_shapes_depth_bound_elim 'H 'ops :
    [wf] sequent { <H>; u: compatible_shapes{'depth; 'l1; 'l2}; <J['u]> >- 'depth in nat } -->
    [wf] sequent { <H>; u: compatible_shapes{'depth; 'l1; 'l2}; <J['u]> >- 'ops in list{Operator} } -->
    [wf] sequent { <H>; u: compatible_shapes{'depth; 'l1; 'l2}; <J['u]> >- 'l1 in list{nat} } -->
    [wf] sequent { <H>; u: compatible_shapes{'depth; 'l1; 'l2}; <J['u]> >- 'l2 in list{olang{'ops}} } -->
    sequent { <H>; u: compatible_shapes{'depth; 'l1; 'l2}; <J['u]>; all i: Index{'l2}. bdepth{nth{'l2; 'i}} >= 'depth >- 'C['u] } -->
    sequent { <H>; u: compatible_shapes{'depth; 'l1; 'l2}; <J['u]> >- 'C['u] }

interactive compatible_shapes_map_bind_vec_equal 'H 'ops :
    [wf] sequent { <H>; u: compatible_shapes{'depth; 'l1; 'l2}; <J['u]> >- 'depth in nat } -->
    [wf] sequent { <H>; u: compatible_shapes{'depth; 'l1; 'l2}; <J['u]> >- 'ops in list{Operator} } -->
    [wf] sequent { <H>; u: compatible_shapes{'depth; 'l1; 'l2}; <J['u]> >- 'l1 in list{nat} } -->
    [wf] sequent { <H>; u: compatible_shapes{'depth; 'l1; 'l2}; <J['u]> >- 'l2 in list{olang{'ops}} } -->
    sequent { <H>; u: compatible_shapes{'depth; 'l1; 'l2}; <J['u]>;
       map{bt. bind{'depth; x. substl{'bt; 'x}}; 'l2} = 'l2 in list{olang{'ops}} >- 'C['u] } -->
    sequent { <H>; u: compatible_shapes{'depth; 'l1; 'l2}; <J['u]> >- 'C['u] }

doc <:doc<
   Basic membership and well-formedness judgments.
>>
interactive var_in_olang {| intro [intro_typeinf << 'x >>] |} Var :
   [wf] sequent { <H> >- 'ops in list{Operator} } -->
   [wf] sequent { <H> >- 'x in Var } -->
   sequent { <H> >- 'x in olang{'ops} }

interactive bterm_in_olang {| intro [] |} :
   [wf] sequent { <H> >- 'ops in list{Operator} } -->
   [wf] sequent { <H> >- 'depth in nat } -->
   [wf] sequent { <H> >- 'op in SubOp{'ops} } -->
   [wf] sequent { <H> >- 'subs in list{olang{'ops}} } -->
   [aux] sequent { <H> >- compatible_shapes{'depth; shape{'op}; 'subs} } -->
   sequent { <H> >- mk_bterm{'depth; 'op; 'subs} in olang{'ops} }

doc docoff

(************************************************************************
 * Squiggle equality.
 *)
interactive var_olang_squiggle 'ops :
   [wf] sequent { <H> >- 'x in Var } -->
   [wf] sequent { <H> >- 'y in Var } -->
   [wf] sequent { <H> >- 'ops in list{Operator} } -->
   [aux] sequent { <H> >- 'x = 'y in olang{'ops} } -->
   sequent { <H> >- 'x ~ 'y }

interactive var_neq_bterm 'H :
   [wf] sequent { <H>; u: var{'l; 'r} = mk_bterm{'depth; 'op; 'subterms} in olang{'ops}; <J['u]> >- 'l in nat } -->
   [wf] sequent { <H>; u: var{'l; 'r} = mk_bterm{'depth; 'op; 'subterms} in olang{'ops}; <J['u]> >- 'r in nat } -->
   [wf] sequent { <H>; u: var{'l; 'r} = mk_bterm{'depth; 'op; 'subterms} in olang{'ops}; <J['u]> >- 'depth in nat } -->
   [wf] sequent { <H>; u: var{'l; 'r} = mk_bterm{'depth; 'op; 'subterms} in olang{'ops}; <J['u]> >- 'op in Operator } -->
   [wf] sequent { <H>; u: var{'l; 'r} = mk_bterm{'depth; 'op; 'subterms} in olang{'ops}; <J['u]> >- 'ops in list{Operator} } -->
   [wf] sequent { <H>; u: var{'l; 'r} = mk_bterm{'depth; 'op; 'subterms} in olang{'ops}; <J['u]> >- 'subterms in list{olang{'ops}} } -->
   sequent { <H>; u: var{'l; 'r} = mk_bterm{'depth; 'op; 'subterms} in olang{'ops}; <J['u]> >- 'C['u] }

interactive bterm_neq_var 'H :
   [wf] sequent { <H>; u: var{'l; 'r} = mk_bterm{'depth; 'op; 'subterms} in olang{'ops}; <J['u]> >- 'l in nat } -->
   [wf] sequent { <H>; u: var{'l; 'r} = mk_bterm{'depth; 'op; 'subterms} in olang{'ops}; <J['u]> >- 'r in nat } -->
   [wf] sequent { <H>; u: var{'l; 'r} = mk_bterm{'depth; 'op; 'subterms} in olang{'ops}; <J['u]> >- 'depth in nat } -->
   [wf] sequent { <H>; u: var{'l; 'r} = mk_bterm{'depth; 'op; 'subterms} in olang{'ops}; <J['u]> >- 'op in Operator } -->
   [wf] sequent { <H>; u: var{'l; 'r} = mk_bterm{'depth; 'op; 'subterms} in olang{'ops}; <J['u]> >- 'ops in list{Operator} } -->
   [wf] sequent { <H>; u: var{'l; 'r} = mk_bterm{'depth; 'op; 'subterms} in olang{'ops}; <J['u]> >- 'subterms in list{olang{'ops}} } -->
   sequent { <H>; u: mk_bterm{'depth; 'op; 'subterms} = var{'l; 'r} in olang{'ops}; <J['u]> >- 'C['u] }

interactive subs_equal 'depth 'op :
   [wf] sequent { <H> >- 'ops in list{Operator} } -->
   [wf] sequent { <H> >- 'depth in nat } -->
   [wf] sequent { <H> >- 'op in SubOp{'ops} } -->
   [wf] sequent { <H> >- 's1 in list{olang{'ops}} } -->
   [wf] sequent { <H> >- 's2 in list{olang{'ops}} } -->
   [aux] sequent { <H> >- compatible_shapes{'depth; shape{'op}; 's1} } -->
   [aux] sequent { <H> >- compatible_shapes{'depth; shape{'op}; 's2} } -->
   sequent { <H> >- mk_bterm{'depth; 'op; 's1} = mk_bterm{'depth; 'op; 's2} in olang{'ops} } -->
   sequent { <H> >- 's1 = 's2 in list{olang{'ops}} }

doc <:doc<
   Any language << olang{'ops} >> has a trivial squiggle equality.
>>
interactive olang_sqsimple {| intro [] |} :
   [wf] sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- sqsimple{olang{'ops}} }

(************************************************************************
 * Properties of compatible_shapes.
 *)
doc <:doc<
   When using induction on a specific language, it is useful to have elimination
   rules for each of the specific operators in the language.  The << listmem_set{'ops; Operator} >>
   term can be used for a case analysis on the operators.  Once given a specific
   operator, we need to split the subterm list into a list of a specific length.
>>
interactive subterm_cons_elim 'H 'depth ('h :: 't) :
   [wf] sequent { <H>; l: list{olang{'ops}}; <J['l]> >- 'ops in list{Operator} } -->
   [wf] sequent { <H>; l: list{olang{'ops}}; <J['l]> >- 'depth in nat } -->
   [wf] sequent { <H>; l: list{olang{'ops}}; <J['l]> >- 'h in int } -->
   [wf] sequent { <H>; l: list{olang{'ops}}; <J['l]> >- 't in list{int} } -->
   [aux] sequent { <H>; l: list{olang{'ops}}; <J['l]> >- compatible_shapes{'depth; 'h :: 't; 'l} } -->
   sequent { <H>; e: olang{'ops}; l: list{olang{'ops}}; <J['e :: 'l]>;
       bdepth{'e} = 'depth +@ 'h in int;
       compatible_shapes{'depth; 't; 'l} >-
       'C['e :: 'l] } -->
   sequent { <H>; l: list{olang{'ops}}; <J['l]> >- 'C['l] }

interactive subterm_nil_elim 'H 'depth :
   [wf] sequent { <H>; l: list{olang{'ops}}; <J['l]> >- 'ops in list{Operator} } -->
   [wf] sequent { <H>; l: list{olang{'ops}}; <J['l]> >- 'depth in nat } -->
   [aux] sequent { <H>; l: list{olang{'ops}}; <J['l]> >- compatible_shapes{'depth; nil; 'l} } -->
   sequent { <H>; <J[nil]> >- 'C[nil] } -->
   sequent { <H>; l: list{olang{'ops}}; <J['l]> >- 'C['l] }

doc docoff

let compatible_shapes_opname = opname_of_term << compatible_shapes{'depth; 'l1; 'l2} >>
let dest_compatible_shapes_term = dest_dep0_dep0_dep0_term compatible_shapes_opname

let rec dest_compatible_shapes i p =
   let i = get_pos_hyp_num p i in
   let t = nth_hyp p i in
   let depth, op, subs = dest_compatible_shapes_term t in
      if is_var_term subs then
         let v = dest_var subs in
         let j = get_decl_number p v in
            if is_cons_term op then
               subterm_cons_elim j depth op thenMT (thinT (i + 1) thenT funT (dest_compatible_shapes (-1)))
            else if is_nil_term op then
               subterm_nil_elim j depth thenMT thinT (-1)
            else
               raise (RefineError ("Itt_hoas_lang2.dest_compatible_shapes", StringTermError ("opname should be a constant", op)))
      else
         raise (RefineError ("Itt_hoas_lang2.dest_compatible_shapes", StringTermError ("subterms should be a variable", subs)))

let dest_compatible_shapesT i =
   funT (dest_compatible_shapes i)

let dest_compatible_shapes_shapeT i =
   rw (addrC [Subterm 2] reduceC) i thenT dest_compatible_shapesT i

let resource elim +=
    [<< compatible_shapes{'depth; 'h :: 't; !v} >>, dest_compatible_shapesT;
     << compatible_shapes{'depth; nil; !v} >>, dest_compatible_shapesT;
     << compatible_shapes{'depth; shape{'op}; !v} >>, dest_compatible_shapes_shapeT]

(************************************************************************
 * Eta-expansion.
 *)

doc <:doc<
   When proving facts about specific terms and languages, we often need
   eta-expansion because the representation of specific terms with binders
   uses an explicit bind term.
>>
interactive_rw eta_reduce_term 'ops :
   'ops in list{Operator} -->
   'e in olang{'ops} -->
   bdepth{'e} > 0 -->
   bind{x. subst{'e; 'x}} <--> 'e

doc docoff

let bind_opname = opname_of_term << bind{x. 'e} >>
let mk_bind_term = mk_dep1_term bind_opname

let subst_opname = opname_of_term << subst{'e1; 'e2} >>
let mk_subst_term = mk_dep0_dep0_term subst_opname

let olang_opname = opname_of_term << olang{'ops} >>
let dest_olang_term = dest_dep0_term olang_opname

let var_x = Lm_symbol.add "x"
let eta_expand e env =
   let t = env_term env in
      if alpha_equal t e then
         (* The result term *)
         let x = maybe_new_var_set var_x (free_vars_set e) in
         let bind = mk_bind_term x (mk_subst_term e (mk_var_term x)) in

         (* The type of the term *)
         let p = env_arg env in
         let ops =
            try get_with_arg p with
               RefineError _ ->
                  dest_olang_term (infer_type p e)
         in
            foldC bind (eta_reduce_term ops)
      else
         failC

let etaExpandC e =
   funC (eta_expand e)

(************************************************************************
 * Restate the reduction on mk_bterm.
 *)
interactive_rw reduce_dest_bterm_mk_bterm 'ops :
   'ops in list{Operator} -->
   'depth in nat -->
   'op in Operator -->
   mem{'op; 'ops; Operator} -->
   'subs in list{olang{'ops}} -->
   compatible_shapes{'depth; shape{'op}; 'subs} -->
   dest_bterm{mk_bterm{'depth; 'op; 'subs};
      l, r. 'var_case['l; 'r];
      depth, op, subs. 'op_case['depth; 'op; 'subs] }
   <-->
   'op_case['depth; 'op; 'subs]

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
