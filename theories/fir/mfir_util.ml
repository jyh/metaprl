(*!
 * @begin[doc]
 * @module[Mfir_util]
 *
 * The @tt[Mfir_util] module defines terms and rewrites for working
 * with the @MetaPRL representation of the FIR.
 * @end[doc]
 *
 * ------------------------------------------------------------------------
 *
 * @begin[license]
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.  Additional
 * information about the system is available at
 * http://www.metaprl.org/
 *
 * Copyright (C) 2002 Brian Emre Aydemir, Caltech
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
 * Author: Brian Emre Aydemir
 * @email{emre@cs.caltech.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)

extends Mfir_int
extends Mfir_list
extends Mfir_int_set
extends Mfir_ty
extends Mfir_exp

(*!
 * @docoff
 *)

open Top_conversionals
open Mfir_bool
open Mfir_int
open Mfir_int_set


(**************************************************************************
 * Declarations.
 **************************************************************************)

(*!
 * @begin[doc]
 * @terms
 *
 * The term @tt[offset] is the type of offsets into data aggregates,
 * such as arrays.  This includes the atoms used to specify the initial
 * size of the data when it is allocated, as well as an index into the data.
 * @end[doc]
 *)

declare offset

(*! @begin[doc]
 *
 * If @tt[poly_ty] is a parametrized type definition or type, then
 * @tt[do_tyApply] instantiates it at the types in the list @tt[ty_list].
 * @end[doc]
 *)

declare do_tyApply{ 'poly_ty; 'ty_list }

(*!
 * @begin[doc]
 *
 * The term @tt[instantiate_tyExists] is used to instantiate
 * an existential type @tt[ty] using type projections (@hrefterm[tyProject])
 * with @tt[var], starting at @tt[num].
 * @end[doc]
 *)

declare instantiate_tyExists{ 'ty; 'var; 'num }

(*!
 * @begin[doc]
 *
 * The term @tt[num_params] counts the number of parameters in an
 * existential type @tt[ty].
 * @end[doc]
 *)

declare num_params{ 'ty }

(*!
 * @begin[doc]
 *
 * The term @tt[nth_unionCase] returns the $n$th tuple space of a
 * non-polymorphic union definition.
 * @end[doc]
 *)

declare nth_unionCase{ 'n; 'union_def }

(*!
 * @begin[doc]
 *
 * The term @tt[union_cases] takes the union of the sets in
 * a list of match cases, and then unions that with @tt[set].
 * @end[doc]
 *)

declare union_cases{ 'set; 'cases }

(*!
 * @begin[doc]
 *
 * The term @tt[index_of_subscript] is used to turn a term representing
 * a subscript into a number term.
 * @end[doc]
 *)

declare index_of_subscript{ 'atom }


(**************************************************************************
 * Rewrites.
 **************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 *
 * Instantiating a parameterized type at a given list of types is
 * straightforward.
 * @end[doc]
 *)

prim_rw reduce_do_tyApply_base :
   do_tyApply{ 'ty; nil } <-->
   'ty

prim_rw reduce_do_tyApply_ind_poly :
   do_tyApply{ tyDefPoly{ t. 'ty['t] }; cons{ 'a; 'b } } <-->
   do_tyApply{ 'ty['a]; 'b }

prim_rw reduce_do_tyApply_ind_all :
   do_tyApply{ tyAll{ t. 'ty['t] }; cons{ 'a; 'b } } <-->
   do_tyApply{ 'ty['a]; 'b }

prim_rw reduce_do_tyApply_ind_exists :
   do_tyApply{ tyExists{ t. 'ty['t] }; cons{ 'a; 'b } } <-->
   do_tyApply{ 'ty['a]; 'b }

(*!
 * @docoff
 *)

let reduce_do_tyApply =
   firstC [reduce_do_tyApply_base;
           reduce_do_tyApply_ind_poly;
           reduce_do_tyApply_ind_all;
           reduce_do_tyApply_ind_exists]

let resource reduce += [
   << do_tyApply{ 'ty; nil } >>,
      reduce_do_tyApply
]

(*!
 * @begin[doc]
 *
 * The following rewrites are the basis for reducing
 * $<< instantiate_tyExists{ 'ty; 'var; 'num } >>$.
 * The are combined into the @tt[reduce_instantiate_tyExists]
 * conversional in order to control the order of their application.
 * @end[doc]
 *)

prim_rw reduce_instantiate_tyExists_aux1 :
   instantiate_tyExists{ 'ty; 'var; 'num } <-->
   'ty

prim_rw reduce_instantiate_tyExists_aux2 :
   instantiate_tyExists{ tyExists{ t. 'ty['t] }; 'var; number[i:n] } <-->
   instantiate_tyExists{ do_tyApply{ tyExists{ t. 'ty['t] };
                                     cons{ tyProject[i:n]{ 'var }; nil } };
                         'var;
                         (number[i:n] +@ 1) }

(*!
 * @docoff
 *)

let reduce_instantiate_tyExists =
   (reduce_instantiate_tyExists_aux2
      thenC (repeatC reduce_do_tyApply)
      thenC reduce_add)
   orelseC
   (reduce_instantiate_tyExists_aux1)

let resource reduce += [
   << instantiate_tyExists{ 'ty; 'var; 'num } >>,
      reduce_instantiate_tyExists
]

(*!
 * @begin[doc]
 *
 * Counting the number of parameters in a type $<< tyExists{t. 'ty['t]} >>$ is
 * also straightforward. Note the bogus instantiation at $<< tyInt >>$ to
 * address the problem of free variables.  The following rewrites are
 * combined into the @tt[reduce_num_params] conversional in order to control
 * the order of their application.
 * @end[doc]
 *)

prim_rw reduce_num_params_exists :
   num_params{ tyExists{ t. 'ty['t] } } <-->
   (1 +@ num_params{ 'ty[tyInt] })

prim_rw reduce_num_params_any :
   num_params{ 'ty } <-->
   0

(*!
 * @docoff
 *)

let reduce_num_params =
   reduce_num_params_exists orelseC reduce_num_params_any

let resource reduce += [
   << num_params{ 'ty } >>,
      reduce_num_params
]

(*!
 * @begin[doc]
 *
 * Computing the $n$th tuple space of a non-polymorphic union definition
 * is straightforward, since the cases are given as a list.
 * @end[doc]
 *)

prim_rw reduce_nth_unionCase :
   nth_unionCase{ number[n:n]; tyDefUnion[str:s]{ 'cases } } <-->
   nth_elt{ number[n:n]; 'cases }

(*!
 * @docoff
 *)

let resource reduce += [
   << nth_unionCase{ number[i:n]; tyDefUnion[str:s]{ 'cases } } >>,
      reduce_nth_unionCase
]

(*!
 * @begin[doc]
 *
 * Taking the union of the sets in a list of match cases is straightforward.
 * @end[doc]
 *)

prim_rw reduce_union_cases_base :
   union_cases{ 'set; nil } <-->
   'set

prim_rw reduce_union_cases_ind :
   union_cases{ 'set; cons{ matchCase{ 'case; 'exp }; 'tail } } <-->
   union_cases{ union{ 'set; 'case }; 'tail }

(*!
 * @docoff
 *)

let reduce_union_cases =
   reduce_union_cases_base orelseC
   (  reduce_union_cases_ind thenC
      (addrC [0] (repeatC reduce_union))
   )

let resource reduce += [
   << union_cases{ 'set; 'cases } >>, reduce_union_cases
]

(*!
 * @begin[doc]
 *
 * Raw integer subscripts represent byte offsets, while integer
 * subscripts represent logical offsets.  Byte offsets must be aligned
 * on four byte boundaries.  If this is not the case, then the result
 * of converting the subscript to a (logical) index is $-1$, which is
 * an invalid index.
 * @end[doc]
 *)

prim_rw reduce_index_of_subscript_atomInt :
   index_of_subscript{ atomInt{ number[i:n] } } <-->
   number[i:n]

prim_rw reduce_index_of_subscript_atomRawInt :
   index_of_subscript{ atomRawInt[32, "signed"]{ number[i:n] } } <-->
   ifthenelse{ int_eq{ 0; rem{ number[i:n]; 4 } };
      rem{ number[i:n]; 4 };
      . -1 }

(*!
 * @docoff
 *)

let reduce_index_of_subscript =
   reduce_index_of_subscript_atomInt orelseC
   (  reduce_index_of_subscript_atomRawInt thenC
      (addrC [0; 1] reduce_rem) thenC
      (addrC [0] reduce_int_eq) thenC
      reduce_ifthenelse
   )

let resource reduce += [
   << index_of_subscript{ 'atom } >>, reduce_index_of_subscript
]


(**************************************************************************
 * Display forms.
 **************************************************************************)

dform offset_df : except_mode[src] ::
   offset =
   bf["offset"]

dform do_tyApply_df : except_mode[src] ::
   do_tyApply{ 'poly_ty; 'ty_list } =
   `"((" slot{'poly_ty} `") " slot{'ty_list} `")"

dform do_instantiate_tyExists_df : except_mode[src] ::
   instantiate_tyExists{ 'ty; 'var; 'num } =
   bf["inst"] exists `"[" slot{'num} `"](" slot{'ty} `"," slot{'var} `")"

dform num_params_df : except_mode[src] ::
   num_params{ 'ty } =
   bf["num_params"] `"(" slot{'ty} `")"

dform nth_unionCase_df : except_mode[src] ::
   nth_unionCase{ 'i; 'union } =
   bf["nth_case"] `"(" slot{'i} `"," slot{'union} `")"

dform union_cases_df : except_mode[src] ::
   union_cases{ 'set; 'cases } =
   `"(" slot{'set} cup sub{it["cases"]} slot{'cases} `")"

dform index_of_subscript_df : except_mode[src] ::
   index_of_subscript{ 'atom } =
   `"(" bf["index"] leftarrow bf["sub"] `")(" slot{'atom} `")"
