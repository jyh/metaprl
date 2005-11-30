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

doc docoff

open Basic_tactics

open Itt_list
open Itt_struct

(************************************************************************
 * Ignore terms.
 *)
doc <:doc<
   The << dummy_term >> is used for constants that don't mean anything.
>>
declare dummy_term

define unfold_dummy_bterm {| reduce |} : dummy_bterm <--> <:xterm<
   $`"dummy_term"
>>

declare sequent [ignore] { Term : Term >- Term } : Term

prim_rw unfold_ignore : <:xrewrite<
   "ignore"{| <J> >- C |}
   <-->
   "dummy_bterm"
>>

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
 * Properties of compatible_shapes.
 *)
doc <:doc<
   When using induction on a specific language, it is useful to have elimination
   rules for each of the specific operators in the language.  The << listmem_set{'ops; Operator} >>
   term can be used for a case analysis on the operators.  Once given a specific
   operator, we need to split the subterm list into a list of a specific length.
>>
interactive subterm_cons_elim 'H 'depth ('h :: 't) :
   [wf] sequent { <H>; l: list{BTerm}; <J['l]> >- 'depth in nat } -->
   [wf] sequent { <H>; l: list{BTerm}; <J['l]> >- 'h in int } -->
   [wf] sequent { <H>; l: list{BTerm}; <J['l]> >- 't in list{int} } -->
   [aux] sequent { <H>; l: list{BTerm}; <J['l]> >- compatible_shapes{'depth; 'h :: 't; 'l} } -->
   sequent { <H>; e: BTerm; l: list{BTerm}; <J['e :: 'l]>;
       bdepth{'e} = 'depth +@ 'h in nat;
       compatible_shapes{'depth; 't; 'l} >-
       'C['e :: 'l] } -->
   sequent { <H>; l: list{BTerm}; <J['l]> >- 'C['l] }

interactive subterm_nil_elim 'H 'depth :
   [wf] sequent { <H>; l: list{BTerm}; <J['l]> >- 'depth in nat } -->
   [aux] sequent { <H>; l: list{BTerm}; <J['l]> >- compatible_shapes{'depth; nil; 'l} } -->
   sequent { <H>; <J[nil]> >- 'C[nil] } -->
   sequent { <H>; l: list{BTerm}; <J['l]> >- 'C['l] }

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
 * Other junk.
 *)

(*
 * OmegaT is failing on some artihmetic, so make it simpler.
 *)
interactive elim_bdepth {| elim [] |} 'H :
   [wf] sequent { <H>; u: bdepth{'t1} = bdepth{'t2} +@ 1 in nat; <J['u]> >- 't1 in BTerm } -->
   [wf] sequent { <H>; u: bdepth{'t1} = bdepth{'t2} +@ 1 in nat; <J['u]> >- 't2 in BTerm } -->
   sequent { <H>; u: bdepth{'t1} = bdepth{'t2} +@ 1 in nat; <J['u]>;
      bdepth{'t1} > 0; bdepth{'t1} -@ 1 = bdepth{'t2} in nat >- 'C['u] } -->
   sequent { <H>; u: bdepth{'t1} = bdepth{'t2} +@ 1 in nat; <J['u]> >- 'C['u] }

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
