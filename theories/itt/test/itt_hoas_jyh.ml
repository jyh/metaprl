(*
 * Some utilities for simplifying the reflection theory.
 * These should eventually be migrated into the reflection
 * theory proper as necessary.
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
extends Itt_hoas_lang

open Basic_tactics

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

(*
 * Case analysis on operators in a language.
 *)
interactive operator_elim_cons {| elim [] |} 'H :
   sequent { <H>; op: SubOp{'h :: 't}; <J['op]> >- 'h in Operator } -->
   sequent { <H>; op: SubOp{'h :: 't}; <J['op]> >- 't in list{Operator} } -->
   sequent { <H>; op: SubOp{'h :: 't}; <J['h]> >- 'C['h] } -->
   sequent { <H>; op: SubOp{'h :: 't}; <J['op]> >- 'C['op] }

interactive operator_elim_nil {| elim [] |} 'H :
   sequent { <H>; op: SubOp{nil}; <J['op]> >- 'C['op] }

(************************************************************************
 * Shapes.
 *)

(*
 * compatible_shapes{depth; op; subs} is very hard to work with.
 * Use compatible_depths{depth; shape; subs} instead.
 *)
define unfold_compatible_depths :
   compatible_depths{'depth; 'shape; 'subs}
   <-->
   map{i. 'depth +@ 'i; 'shape} = map{e. bdepth{'e}; 'subs} in list{int}

interactive compatible_shapes_intro {| intro [] |} :
    sequent { <H> >- 'depth in nat } -->
    sequent { <H> >- 'op in Operator } -->
    sequent { <H> >- compatible_depths{'depth; shape{'op}; 'subs} } -->
    sequent { <H> >- compatible_shapes{'depth; 'op; 'subs} }

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
