(*!
 * @begin[doc]
 * @module[Mfir_int]
 *
 * The @tt[Mfir_int] module defines integers and operations on integers.
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

extends Mfir_bool

(*!
 * @docoff
 *)

open Base_meta
open Top_conversionals
open Mfir_bool


(**************************************************************************
 * Declarations.
 **************************************************************************)

(*!
 * @begin[doc]
 * @terms
 *
 * The term @tt{number[i:n]} represents the integer $i$.
 * @end[doc]
 *)

declare number[i:n]


(*!
 * @begin[doc]
 *
 * Basic arithmetic operations can be applied to integers.
 * @end[doc]
 *)

declare add{ 'num1; 'num2 }
declare sub{ 'num1; 'num2 }
declare mul{ 'num1; 'num2 }
declare div{ 'num1; 'num2 }
declare rem{ 'num1; 'num2 }
declare minus{ 'num }

declare int_min{ 'num1; 'num2 }
declare int_max{ 'num1; 'num2 }


(*!
 * @begin[doc]
 *
 * Integers can be compared using the following six binary operators.
 * @end[doc]
 *)

declare int_eq{ 'num1; 'num2 }
declare int_neq{ 'num1; 'num2 }
declare int_lt{ 'num1; 'num2 }
declare int_le{ 'num1; 'num2 }
declare int_gt{ 'num1; 'num2 }
declare int_ge{ 'num1; 'num2 }


(**************************************************************************
 * Rewrites.
 **************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 *
 * The arithmetic and comparison operators above can be rewritten to numbers
 * and booleans using meta operations from the @tt[Base_meta] module.  These
 * rewrites are straightforward, and we omit an explicit listing of them.
 * @end[doc]
 *)

(*!
 * @docoff
 *)

(*
 * Intermediate term for arithmetic operations.
 *)

declare numeral{ 'num }


(*
 * Define auxilary rewrites.
 *)

prim_rw reduce_add_aux :
   add{ number[i:n]; number[j:n] } <-->
   numeral{ meta_sum[i:n, j:n] }

prim_rw reduce_sub_aux :
   sub{ number[i:n]; number[j:n] } <-->
   numeral{ meta_diff[i:n, j:n] }

prim_rw reduce_mul_aux :
   mul{ number[i:n]; number[j:n] } <-->
   numeral{ meta_prod[i:n, j:n] }

prim_rw reduce_div_aux :
   div{ number[i:n]; number[j:n] } <-->
   numeral{ meta_quot[i:n, j:n] }

prim_rw reduce_rem_aux :
   rem{ number[i:n]; number[j:n] } <-->
   numeral{ meta_rem[i:n, j:n] }

prim_rw reduce_minus_aux :
   minus{ number[i:n] } <-->
   numeral{ meta_diff[0:n, i:n] }

prim_rw reduce_numeral :
   numeral{ meta_num[i:n] } <-->
   number[i:n]

prim_rw reduce_int_eq_aux :
   int_eq{ number[i:n]; number[j:n] } <-->
   meta_eq[i:n, j:n]{ "true"; "false" }

prim_rw reduce_int_neq_aux :
   int_neq{ number[i:n]; number[j:n] } <-->
   meta_eq[i:n, j:n]{ "false"; "true" }

prim_rw reduce_int_lt_aux :
   int_lt{ number[i:n]; number[j:n] } <-->
   meta_lt[i:n, j:n]{ "true"; "false" }

prim_rw reduce_int_le_aux :
   int_le{ number[i:n]; number[j:n] } <-->
   meta_lt[j:n, i:n]{ "false"; "true" }

prim_rw reduce_int_gt_aux :
   int_gt{ number[i:n]; number[j:n] } <-->
   meta_lt[j:n, i:n]{ "true"; "false" }

prim_rw reduce_int_ge_aux :
   int_ge{ number[i:n]; number[j:n] } <-->
   meta_lt[i:n, j:n]{ "false"; "true" }


(*
 * Define the actual rewrites.
 *)

let reduce_add =
   reduce_add_aux thenC (addrC [0] reduce_meta_sum) thenC reduce_numeral

let reduce_sub =
   reduce_sub_aux thenC (addrC [0] reduce_meta_diff) thenC reduce_numeral

let reduce_mul =
   reduce_mul_aux thenC (addrC [0] reduce_meta_prod) thenC reduce_numeral

let reduce_div =
   reduce_div_aux thenC (addrC [0] reduce_meta_quot) thenC reduce_numeral

let reduce_rem =
   reduce_rem_aux thenC (addrC [0] reduce_meta_rem) thenC reduce_numeral

let reduce_minus =
   reduce_minus_aux thenC (addrC [0] reduce_meta_diff) thenC reduce_numeral

let reduce_int_eq =
   reduce_int_eq_aux thenC reduce_meta_eq_num

let reduce_int_neq =
   reduce_int_neq_aux thenC reduce_meta_eq_num

let reduce_int_lt =
   reduce_int_lt_aux thenC reduce_meta_lt_num

let reduce_int_le =
   reduce_int_le_aux thenC reduce_meta_lt_num

let reduce_int_gt =
   reduce_int_gt_aux thenC reduce_meta_lt_num

let reduce_int_ge =
   reduce_int_ge_aux thenC reduce_meta_lt_num


(*
 * Add the above rewrites to the reduce resource.
 *)

let resource reduce += [
   << add{ 'num1; 'num2 } >>, reduce_add;
   << sub{ 'num1; 'num2 } >>, reduce_sub;
   << mul{ 'num1; 'num2 } >>, reduce_mul;
   << div{ 'num1; 'num2 } >>, reduce_div;
   << rem{ 'num1; 'num2 } >>, reduce_rem;
   << minus{ 'num } >>, reduce_minus;
   << numeral{ 'num } >>, reduce_numeral;
   << int_eq{ 'num1; 'num2 } >>, reduce_int_eq;
   << int_neq{ 'num1; 'num2 } >>, reduce_int_neq;
   << int_lt{ 'num1; 'num2 } >>, reduce_int_lt;
   << int_le{ 'num1; 'num2 } >>, reduce_int_le;
   << int_gt{ 'num1; 'num2 } >>, reduce_int_gt;
   << int_ge{ 'num1; 'num2 } >>, reduce_int_ge
]


(*
 * The reductions for min/max are here since they depend on the
 * less-than relation.
 *)

prim_rw reduce_int_min_aux :
   int_min{ number[i:n]; number[j:n] } <-->
   ifthenelse{ int_lt{ number[i:n]; number[j:n] }; number[i:n]; number[j:n] }

prim_rw reduce_int_max_aux :
   int_max{ number[i:n]; number[j:n] } <-->
   ifthenelse{ int_lt{ number[i:n]; number[j:n] }; number[j:n]; number[i:n] }

let reduce_int_min =
   reduce_int_min_aux thenC
   (addrC [0] reduce_int_lt) thenC
   reduce_ifthenelse

let reduce_int_max =
   reduce_int_max_aux thenC
   (addrC [0] reduce_int_lt) thenC
   reduce_ifthenelse

let resource reduce += [
   << int_min{ number[i:n]; number[j:n] } >>, reduce_int_min;
   << int_max{ number[i:n]; number[j:n] } >>, reduce_int_max
]


(**************************************************************************
 * Display forms.
 **************************************************************************)

(*
 * Numbers.
 *)

dform number_df : except_mode[src] ::
   number[i:n] =
   slot[i:n]


(*
 * Operations.
 *)

dform add_df : except_mode[src] ::
   add{ 'num1; 'num2 } =
   `"(" slot{'num1} `"+" slot{'num2} `")"

dform sub_df : except_mode[src] ::
   sub{ 'num1; 'num2 } =
   `"(" slot{'num1} `"-" slot{'num2} `")"

dform mul_df : except_mode[src] ::
   mul{ 'num1; 'num2 } =
   `"(" slot{'num1} `"*" slot{'num2} `")"

dform div_df : except_mode[src] ::
   div{'num1; 'num2 } =
   `"(" slot{'num1} `"/" slot{'num2} `")"

dform rem_df : except_mode[src] ::
   rem{ 'num1; 'num2 } =
   `"(" slot{'num1} `"%" slot{'num2} `")"

dform minus_df : except_mode[src] ::
   minus{ 'num } =
   `"(-" slot{'num} `")"

dform int_min_df : except_mode[src] ::
   int_min{ 'num1; 'num2 } =
   bf["min"] `"(" slot{'num1} `"," slot{'num2} `")"

dform int_max_df : except_mode[src] ::
   int_max{ 'num1; 'num2 } =
   bf["max"] `"(" slot{'num1} `"," slot{'num2} `")"


dform int_eq_df : except_mode[src] ::
   int_eq{ 'num1; 'num2 } =
   `"(" slot{'num1} `"=" slot{'num2} `")"

dform int_neq_df : except_mode[src] ::
   int_neq{ 'num1; 'num2 } =
   `"(" slot{'num1} neq slot{'num2} `")"

dform int_lt_df : except_mode[src] ::
   int_lt{ 'num1; 'num2 } =
   `"(" slot{'num1} `"<" slot{'num2} `")"

dform int_le_df : except_mode[src] ::
   int_le{ 'num1; 'num2 } =
   `"(" slot{'num1} le slot{'num2} `")"

dform int_gt_df : except_mode[src] ::
   int_gt{ 'num1; 'num2 } =
   `"(" slot{'num1} `">" slot{'num2} `")"

dform int_ge_df : except_mode[src] ::
   int_ge{ 'num1; 'num2 } =
   `"(" slot{'num1} ge slot{'num2} `")"
