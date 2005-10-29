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

extends Itt_hoas_bterm
extends Itt_hoas_util
extends Itt_image
extends Itt_subset

doc docoff

open Lm_printf

open Simple_print
open Basic_tactics
open Itt_list
open Itt_struct

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

(*
 * Subtyping.  These rules are mainly for directing autoT.
 *)
interactive olang_bterm_intro {| intro [intro_typeinf << 'e >>] |} olang{'ops} :
   [wf] sequent { <H> >- 'ops in list{Operator} } -->
   [wf] sequent { <H> >- 'e in olang{'ops} } -->
   sequent { <H> >- 'e in BTerm }

interactive olang_bterm_list_intro {| intro [intro_typeinf << 'e >>] |} list{olang{'ops}} :
   [wf] sequent { <H> >- 'ops in list{Operator} } -->
   [wf] sequent { <H> >- 'e in list{olang{'ops}} } -->
   sequent { <H> >- 'e in list{BTerm} }

interactive olang_bterm_list_nil_intro {| intro [] |} :
   sequent { <H> >- nil in list{BTerm} }

interactive olang_bterm_list_cons_intro {| intro [] |} :
   [wf] sequent { <H> >- 'e in BTerm } -->
   [wf] sequent { <H> >- 'l in list{BTerm} } -->
   sequent { <H> >- 'e :: 'l in list{BTerm} }

(************************************************************************
 * Shapes.
 *)

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

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
