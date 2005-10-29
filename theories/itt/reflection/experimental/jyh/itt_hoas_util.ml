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
