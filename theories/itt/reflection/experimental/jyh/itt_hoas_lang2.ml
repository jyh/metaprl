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
extends Itt_image

open Basic_tactics

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
 * Variables.
 * The main objective here is to hide the deBruijn representation.
 *)
define unfold_Var : Var <--> Img{nat * nat; v. spread{'v; i, j. var{'i; 'j}}}

interactive var_type_univ {| intro [] |} :
   sequent { <H> >- Var in univ[i:l] }

interactive var_type_wf {| intro [] |} :
   sequent { <H> >- Var Type }

interactive var_wf {| intro [] |} :
   [wf] sequent { <H> >- 'l in nat } -->
   [wf] sequent { <H> >- 'r in nat } -->
   sequent { <H> >- var{'l; 'r} in Var }

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

interactive olang_wf {| intro [] |} :
   [wf] sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- olang{'ops} Type }

(*
 * This is really a private definition until we get a proper compatible_shapes
 * definition.
 *)
interactive olang_elim1 'H :
   [wf] sequent { <H>; e: olang{'ops}; <J['e]> >- 'ops in list{Operator} } -->
   [base] sequent { <H>; e: olang{'ops}; <J['e]>; x: Var >- 'P['x] } -->
   [step] sequent { <H>; e: olang{'ops}; <J['e]>;
       depth: nat;
       op: listmem_set{'ops; Operator};
       subs: list{olang{'ops}};
       compatible_shapes{'depth; 'op; 'subs} >- 'P[mk_bterm{'depth; 'op; 'subs}] } -->
   sequent { <H>; e: olang{'ops}; <J['e]> >- 'P['e] }

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
   sequent { <H>; op: SubOp{'t}; <J['op]> >- 'C['op] } -->
   sequent { <H>; op: SubOp{'h :: 't}; <J['op]> >- 'C['op] }

interactive operator_elim_nil {| elim [] |} 'H :
   sequent { <H>; op: SubOp{nil}; <J['op]> >- 'C['op] }

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

interactive bdepth_wf_int {| intro [intro_typeinf << 'e >>] |} Lang{SubOp{'ops}} :
   [wf] sequent { <H> >- 'ops in list{Operator} } -->
   [wf] sequent { <H> >- 'e in olang{'ops} } -->
   sequent { <H> >- bdepth{'e} in int }

(*
 * compatible_shapes{depth; op; subs} is very hard to work with.
 * Use compatible_depths{depth; shape; subs} instead.
 *)
define unfold_compatible_depths :
   compatible_depths{'depth; 'shape; 'subs}
   <-->
   map{i. 'depth +@ 'i; 'shape} = map{e. bdepth{'e}; 'subs} in list{int}

(*
 * Well-formedness.
 *)
interactive compatible_depths_wf {| intro [intro_typeinf << 'l2 >>] |} list{olang{'ops}} :
    [wf] sequent { <H> >- 'ops in list{Operator} } -->
    [wf] sequent { <H> >- 'depth in int } -->
    [wf] sequent { <H> >- 'l1 in list{int} } -->
    [wf] sequent { <H> >- 'l2 in list{olang{'ops}} } -->
    sequent { <H> >- compatible_depths{'depth; 'l1; 'l2} Type }

(*
 * Useful lemmas for proving the compatible_shapes_intro rule.
 *)
interactive compatible_shapes_length_equal 'depth list{Lang{SubOp{'ops}}} :
    [wf] sequent { <H> >- 'ops in list{Operator} } -->
    [wf] sequent { <H> >- 'depth in nat } -->
    [wf] sequent { <H> >- 'l1 in list{int} } -->
    [wf] sequent { <H> >- 'l2 in list{Lang{SubOp{'ops}}} } -->
    sequent { <H> >- compatible_depths{'depth; 'l1; 'l2} } -->
    sequent { <H> >- length{'l1} = length{'l2} in int }

(*
 * Reduce compatible_shapes to compatible_depths.
 *)
interactive compatible_shapes_intro {| intro [intro_typeinf << 'subs >>] |} list{Lang{SubOp{'ops}}} :
    sequent { <H> >- 'ops in list{Operator} } -->
    sequent { <H> >- 'subs in list{Lang{SubOp{'ops}}} } -->
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
