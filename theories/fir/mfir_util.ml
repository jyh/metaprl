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
extends Mfir_sequent

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
 * @modsubsection{Definition extraction}
 *
 * I should probably document the following.
 * @end[doc]
 *)

declare get_core{ 'poly_ty }


(*!************************************
 * @begin[doc]
 * @modsubsection{Type application}
 *
 * If @tt[poly_ty] is a parametrized type definition or type, then
 * @tt[do_tyApply] instantiates it at the types in the list @tt[ty_list].
 * @end[doc]
 *)

declare apply_types{ 'poly_ty; 'ty_list }


(*!************************************
 * @begin[doc]
 * @modsubsection{Parameter counting}
 *
 * The term @tt[num_params] counts the number of parameters in an
 * existential type @tt[ty].
 * @end[doc]
 *)

declare num_params{ 'ty }


(*!************************************
 * @begin[doc]
 * @modsubsection{Existential unpacking}
 *
 * The term @tt[instantiate_tyExists] is used to instantiate
 * an existential type @tt[ty] using type projections (@hrefterm[tyProject])
 * with @tt[var], starting at @tt[num].
 * @end[doc]
 *)

declare unpack_exists{ 'ty; 'var; 'num }


(**************************************************************************
 * Rewrites.
 **************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 * @modsubsection{Definition extraction}
 *
 * I should probably document the following.
 * @end[doc]
 *)

prim_rw reduce_get_core_poly :
   get_core{ tyDefPoly{ t. 'ty['t] } } <-->
   get_core{ 'ty[it] }

prim_rw reduce_get_core_any :
   get_core{ 'ty } <-->
   'ty

(*!
 * @docoff
 *)

let reduce_get_core =
   reduce_get_core_poly orelseC reduce_get_core_any

let resource reduce += [
   << get_core{ 'ty } >>,
      reduce_get_core
]


(*!************************************
 * @begin[doc]
 * @modsubsection{Type application}
 *
 * Instantiating a parameterized type at a given list of types is
 * straightforward.
 * @end[doc]
 *)

prim_rw reduce_apply_types_base :
   apply_types{ 'ty; nil } <-->
   'ty

prim_rw reduce_apply_types_ind_poly :
   apply_types{ tyDefPoly{ t. 'ty['t] }; cons{ 'a; 'b } } <-->
   apply_types{ 'ty['a]; 'b }

prim_rw reduce_apply_types_ind_all :
   apply_types{ tyAll{ t. 'ty['t] }; cons{ 'a; 'b } } <-->
   apply_types{ 'ty['a]; 'b }

prim_rw reduce_apply_types_ind_exists :
   apply_types{ tyExists{ t. 'ty['t] }; cons{ 'a; 'b } } <-->
   apply_types{ 'ty['a]; 'b }

(*!
 * @docoff
 *)

let reduce_apply_types =
   firstC [reduce_apply_types_base;
           reduce_apply_types_ind_poly;
           reduce_apply_types_ind_all;
           reduce_apply_types_ind_exists]

let resource reduce += [
   << apply_types{ 'ty; nil } >>,
      reduce_apply_types
]


(*!************************************
 * @begin[doc]
 * @modsubsection{Parameter counting}
 *
 * Counting the number of parameters in a type $<< tyExists{t. 'ty['t]} >>$ is
 * also straightforward. Note the bogus instantiation at $<< it >>$ to
 * address the problem of free variables.  The following rewrites are
 * combined into the @tt[reduce_num_params] conversional in order to control
 * the order of their application.
 * @end[doc]
 *)

prim_rw reduce_num_params_exists :
   num_params{ tyExists{ t. 'ty['t] } } <-->
   (1 +@ num_params{ 'ty[it] })

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

(*!************************************
 * @begin[doc]
 *
 * The following rewrites are the basis for reducing
 * $<< unpack_exists{ 'ty; 'var; 'num } >>$.
 * The are combined into the @tt[reduce_instantiate_tyExists]
 * conversional in order to control the order of their application.
 * @end[doc]
 *)

prim_rw reduce_unpack_exists_aux1 :
   unpack_exists{ 'ty; 'var; 'num } <-->
   'ty

prim_rw reduce_unpack_exists_aux2 :
   unpack_exists{ tyExists{ t. 'ty['t] }; 'var; number[i:n] } <-->
   unpack_exists{ apply_types{ tyExists{ t. 'ty['t] };
                               cons{ tyProject[i:n]{ 'var }; nil } };
                  'var;
                  (number[i:n] +@ 1) }

(*!
 * @docoff
 *)

let reduce_unpack_exists =
   (reduce_unpack_exists_aux2
      thenC (repeatC reduce_apply_types)
      thenC reduce_add)
   orelseC
   (reduce_unpack_exists_aux1)

let resource reduce += [
   << unpack_exists{ 'ty; 'var; 'num } >>,
      reduce_unpack_exists
]


(**************************************************************************
 * Display forms.
 **************************************************************************)

dform get_core_df : except_mode[src] ::
   get_core{ 'ty } =
   bf["core"] `"(" slot{'ty} `")"

dform apply_types_df : except_mode[src] ::
   apply_types{ 'poly_ty; 'ty_list } =
   `"((" slot{'poly_ty} `") " slot{'ty_list} `")"

dform num_params_df : except_mode[src] ::
   num_params{ 'ty } =
   bf["num_params"] `"(" slot{'ty} `")"

dform unpack_exists_df : except_mode[src] ::
   unpack_exists{ 'ty; 'var; 'num } =
   bf["unpack"] exists `"[" slot{'num} `"](" slot{'ty} `"," slot{'var} `")"
