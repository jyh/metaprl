doc <:doc<
   @module[Mfir_util]

   The @tt[Mfir_util] module defines terms and rewrites for working
   with the @MetaPRL representation of the FIR.

   @docoff
   ------------------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.  Additional
   information about the system is available at
   http://www.metaprl.org/

   Copyright (C) 2002 Brian Emre Aydemir, Caltech

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

   Author: Brian Emre Aydemir
   @email{emre@cs.caltech.edu}
   @end[license]
>>

doc <:doc<
   @parents
>>

extends Mfir_bool
extends Mfir_int
extends Mfir_list
extends Mfir_int_set
extends Mfir_ty
extends Mfir_exp
extends Mfir_sequent

doc docoff

open Basic_tactics
open Mfir_bool
open Mfir_int
open Mfir_int_set

(**************************************************************************
 * Declarations.
 **************************************************************************)

doc <:doc<
   @terms
   @modsubsection{Offset type}

   The term @tt[offset] represents the type of offset atoms, atoms
   that are used to index aggregate data.
>>

declare offset


doc <:doc<
   @modsubsection{Type application}

   If @tt[poly_ty] is a parametrized type definition or quantified type, then
   @tt[do_tyApply] instantiates it at the types in the list @tt[ty_list].
>>

declare apply_types{ 'poly_ty; 'ty_list }


doc <:doc<
   @modsubsection{Definition extraction}

   (Documentation incomplete.)
>>

(* XXX: documentation needs to be completed. *)

declare get_core{ 'num; 'poly_ty }


doc <:doc<
   @modsubsection{Type projection}

   (Documentation incomplete.)
>>

(* XXX: documentation needs to be completed. *)

declare project_in_bounds{ 'num; 'ty }


doc <:doc<
   @modsubsection{Existential unpacking}

   The term @tt[instantiate_tyExists] is used to instantiate
   an existential type @tt[ty] using type projections (@hrefterm[tyProject])
   of @tt[var], starting at @tt[num].
>>

declare unpack_exists{ 'ty; 'var; 'num }


doc <:doc<
   @modsubsection{Union of match cases}

   (Documentation incomplete.)
>>

(* XXX: documentation needs to be completed. *)

declare union_cases{ 'set; 'cases }


doc <:doc<
   @modsubsection{Conversions}

   (Documentation incomplete.)
>>

(* XXX: documentation needs to be completed. *)

declare index_of_subscript{ 'atom }
declare ty_of_mutable_ty{ 'mutable_ty }


(**************************************************************************
 * Rewrites.
 **************************************************************************)

doc <:doc<
   @rewrites
   @modsubsection{Type application}

   Instantiating a parameterized type definition or quantified type
   at a given list of types is straightforward.
>>

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

doc docoff

let reduce_apply_types =
   firstC [reduce_apply_types_base;
           reduce_apply_types_ind_poly;
           reduce_apply_types_ind_all;
           reduce_apply_types_ind_exists]

let resource reduce += [
   << apply_types{ 'ty; nil } >>,
      reduce_apply_types
]


doc <:doc<
   @modsubsection{Definition extraction}

   (Documentation incomplete.)
>>

(* XXX: documentation needs to be completed. *)

prim_rw reduce_get_core_main :
   get_core{ number[i:n]; 'ty } <-->
   (if int_eq{ number[i:n]; 0 } then
      'ty
   else if int_gt{ number[i:n]; 0 } then
      get_core{ (number[i:n] -@ 1); apply_types{ 'ty; (it ::nil) } }
   else
      get_core{ number[i:n]; 'ty })

doc docoff

let reduce_get_core =
   reduce_get_core_main thenC
   (addrC [Subterm 1] reduce_int_eq) thenC
   reduce_ifthenelse thenC
   (tryC ((addrC [Subterm 1] reduce_int_gt) thenC reduce_ifthenelse))

let resource reduce += [
   << get_core{ number[i:n]; 'ty } >>, reduce_get_core
]


doc <:doc<
   @modsubsection{Type projection}

   (Documentation incomplete.)
>>

(* XXX: documentation needs to be completed. *)

prim_rw reduce_project_in_bounds_main :
   project_in_bounds{ number[i:n]; tyExists{ t. 'ty['t] } } <-->
   (if int_lt{ number[i:n]; 0 } then
      "false"
   else if int_eq{ number[i:n]; 0 } then
      "true"
   else
      project_in_bounds{ (number[i:n] -@ 1); 'ty[it] })

doc <:doc<
   @docoff
>>

let reduce_project_in_bounds =
   reduce_project_in_bounds_main thenC
   (addrC [Subterm 1] reduce_int_lt) thenC
   reduce_ifthenelse thenC
   (tryC ((addrC [Subterm 1] reduce_int_eq) thenC reduce_ifthenelse))

let resource reduce += [
   << project_in_bounds{ number[i:n]; tyExists{ t. 'ty['t] } } >>,
      reduce_project_in_bounds
]


doc <:doc<
   @modsubsection{Existential unpacking}

   The following rewrites are the basis for reducing
   << unpack_exists{ 'ty; 'var; 'num } >>. The following two
   rewrites are combined into the @tt[reduce_instantiate_tyExists]
   conversional in order to control the order of their application.
>>

(*
 * BUG: I really should not be using orelseC to control how
 * the following rewrites are applied.
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

doc <:doc<
   @docoff
>>

let reduce_unpack_exists =
   (  reduce_unpack_exists_aux2 thenC
      (repeatC reduce_apply_types) thenC
      reduce_add
   )
   orelseC
   (reduce_unpack_exists_aux1)

let resource reduce += [
   << unpack_exists{ 'ty; 'var; 'num } >>,
      reduce_unpack_exists
]


doc <:doc<
   @modsubsection{Union of match cases}

   Taking the union of the sets in a list of match cases is straightforward.
>>

prim_rw reduce_union_cases_base :
   union_cases{ 'set; nil } <-->
   'set

prim_rw reduce_union_cases_ind :
   union_cases{ 'set; cons{ matchCase{ 'case; 'exp }; 'tail } } <-->
   union_cases{ union{ 'set; 'case }; 'tail }

doc <:doc<
   @docoff
>>

let reduce_union_cases =
   reduce_union_cases_base orelseC
   (  reduce_union_cases_ind thenC
      (addrC [Subterm 1] (repeatC reduce_union))
   )

let resource reduce += [
   << union_cases{ 'set; 'cases } >>, reduce_union_cases
]


doc <:doc<
   @modsubsection{Conversions}

   Raw integer subscripts represent byte offsets, while integer
   subscripts represent logical offsets.  Byte offsets must be aligned
   on four byte boundaries.  If this is not the case, then the result
   of converting the subscript to a (logical) index is $-1$, which is
   an invalid index.
>>

prim_rw reduce_index_of_subscript_atomInt :
   index_of_subscript{ atomInt{ number[i:n] } } <-->
   number[i:n]

prim_rw reduce_index_of_subscript_atomRawInt :
   index_of_subscript{ atomRawInt[32, "signed"]{ number[i:n] } } <-->
   ifthenelse{ int_eq{ 0; rem{ number[i:n]; 4 } };
      rem{ number[i:n]; 4 };
      . -1 }

doc <:doc<
   @docoff
>>

let reduce_index_of_subscript =
   reduce_index_of_subscript_atomInt orelseC
   (  reduce_index_of_subscript_atomRawInt thenC
      (addrC [Subterm 1; Subterm 2] reduce_rem) thenC
      (addrC [Subterm 1] reduce_int_eq) thenC
      reduce_ifthenelse thenC
      (tryC reduce_rem)
   )

let resource reduce += [
   << index_of_subscript{ 'atom } >>, reduce_index_of_subscript
]


doc <:doc<

   Converting a mutable type << mutable_ty{ 'ty; 'flag } >> to
   a plain type << 'ty >> is straightforward.
>>

prim_rw reduce_ty_of_mutable_ty :
   ty_of_mutable_ty{ mutable_ty{ 'ty; 'flag } } <-->
   'ty

doc <:doc<
   @docoff
>>

let resource reduce += [
   << ty_of_mutable_ty{ mutable_ty{ 'ty; 'flag } } >>,
      reduce_ty_of_mutable_ty
]


(**************************************************************************
 * Display forms.
 **************************************************************************)

dform offset_df : except_mode[src] ::
   offset =
   bf["offset"]

dform apply_types_df : except_mode[src] ::
   apply_types{ 'poly_ty; 'ty_list } =
   `"(" slot{'poly_ty} `" " slot{'ty_list} `")"

dform get_core_df : except_mode[src] ::
   get_core{ 'num; 'ty } =
   bf["core"] `"[" slot{'num} `"](" slot{'ty} `")"

dform project_in_bounds_df : except_mode[src] ::
   project_in_bounds{ 'num; 'ty } =
   bf["project_in_bounds"] `"[" slot{'num} `"](" slot{'ty} `")"

dform unpack_exists_df : except_mode[src] ::
   unpack_exists{ 'ty; 'var; 'num } =
   bf["unpack"] `"[" slot{'num} `"](" slot{'ty} `"," slot{'var} `")"

dform union_cases_df : except_mode[src] ::
   union_cases{ 'set; 'cases } =
   `"(" slot{'set} cup sub{it["cases"]} slot{'cases} `")"

dform index_of_subscript_df : except_mode[src] ::
   index_of_subscript{ 'atom } =
   `"(" bf["index"] leftarrow bf["sub"] `")(" slot{'atom} `")"

dform ty_of_mutable_ty_df : except_mode[src] ::
   ty_of_mutable_ty{ 'mutable_ty } =
   `"(" bf["ty"] leftarrow bf["mty"] `")(" slot{'mutable_ty} `")"
