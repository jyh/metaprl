(*!
 * @begin[doc]
 * @module[Mfir_basic]
 *
 * The @tt[Mfir_basic] module declares basic terms needed to
 * support the @MetaPRL representation of the FIR.
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

extends Base_theory

open Base_meta
open Top_conversionals

(**************************************************************************
 * Declarations.
 **************************************************************************)

(*!
 * @begin[doc]
 * @terms
 * @modsubsection{Booleans}
 *
 * The FIR theory uses meta-booleans to express simple judgments and
 * conditionals.  The logical operators here are classical, not constructive.
 * @end[doc]
 *)

declare "true"
declare "false"
declare "or"{ 'bool1; 'bool2 }
declare "and"{ 'bool1; 'bool2 }
declare "not"{ 'boolean }
declare ifthenelse{ 'test; 'true_case; 'false_case }

(*!
 * @begin[doc]
 * @modsubsection{Integers}
 *
 * The term @tt{number[i:n]} represents the integer $i$.  The term
 * @tt[numeral] takes a @tt[number] term as a subterm.  It is used as an
 * intermediate representation for the arithmetic operations below.
 * @end[doc]
 *)

declare number[i:n]
declare numeral{ 'num }

(*!
 * @begin[doc]
 *
 * Basic arithmetic operations can be applied to integers, along with unary
 * negation (@tt[minus]).
 * @end[doc]
 *)

declare add{ 'num1; 'num2 }
declare sub{ 'num1; 'num2 }
declare mul{ 'num1; 'num2 }
declare div{ 'num1; 'num2 }
declare rem{ 'num1; 'num2 }
declare minus{ 'num }

(*!
 * @begin[doc]
 *
 * Basic binary comparison operators can also be applied to integers.  The
 * rewrites below can rewrite the comparisons to either @tt["\"true\""] or
 * @tt["\"false\""].
 * @end[doc]
 *)

declare int_eq{ 'num1; 'num2 }
declare int_neq{ 'num1; 'num2 }
declare int_lt{ 'num1; 'num2 }
declare int_le{ 'num1; 'num2 }
declare int_gt{ 'num1; 'num2 }
declare int_ge{ 'num1; 'num2 }

(*!
 * @begin[doc]
 * @modsubsection{Lists}
 *
 * Lists are used in the FIR to encode entities whose arities may vary.  The
 * term @tt[nil] is the empty list, and the term @tt[cons] adds a term
 * @tt[elt] to the list @tt[tail].
 * @end[doc]
 *)

declare nil
declare cons{ 'elt; 'tail }

(*!
 * @begin[doc]
 * @modsubsection{Integer sets}
 *
 * The FIR uses integer sets in pattern matching expressions (see
 * @hrefterm[matchExp]), and to designate a subset of the cases of a union
 * type (see @hrefterm[tyUnion]).  An integer set is represented as a list of
 * closed intervals.
 *
 * The term @tt[interval] represents a closed interval.  The term @tt[intset]
 * consists of a list of intervals.  In this case, the end points of each
 * interval are interpreted as signed, 31-bit integers.  The term
 * @tt[rawintset] is similar, except the end points of each interval are
 * interpreted as integers with the specified precision and signedness (see
 * @hrefterm[tyRawInt]).
 * @end[doc]
 *)

declare interval{ 'left; 'right }
declare intset{ 'interval_list }
declare rawintset[precision:n, sign:s]{ 'interval_list }

(*!
 * @begin[doc]
 *
 * The term @tt[member] is used to determine whether or not a number @tt[num]
 * is in a set or interval @tt[set].  The rewrites below will reduce a
 * @tt[member] term to either @tt["\"true\""] or @tt["\"false\""].
 * @end[doc]
 *)

declare member{ 'num; 'set }

(*!
 * @begin[doc]
 *
 * The term @tt[intset_max] is the set of all 31-bit, signed integers.
 * @end[doc]
 *)

declare intset_max

(*!
 * @begin[doc]
 *
 * The term @tt[enum_max] is the set of allowed values for the parameter of
 * @hrefterm[tyEnum].
 * @end[doc]
 *)

declare enum_max

(**************************************************************************
 * Rewrites.
 **************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 * @modsubsection{Conditionals}
 *
 * The logical connectives are treated in a classical fashion. Rewriting of
 * ``if-then-else'' expressions is a straightforward case analysis on the
 * test.  All of these rewrites are added to the @tt[reduce] resource.
 * @end[doc]
 *)

prim_rw reduce_and :
   "and"{ 'bool1; 'bool2 } <-->
   ifthenelse{ 'bool1; 'bool2; "false" }

prim_rw reduce_or :
   "or"{ 'bool1; 'bool2 } <-->
   ifthenelse{ 'bool1; "true"; 'bool2 }

prim_rw reduce_not :
   "not"{ 'boolean } <-->
   ifthenelse{ 'boolean; "false"; "true" }

prim_rw reduce_ifthenelse_true :
   ifthenelse{ "true"; 'true_case; 'false_case } <-->
   'true_case

prim_rw reduce_ifthenelse_false :
   ifthenelse{ "false"; 'true_case; 'false_case } <-->
   'false_case

(*!
 * @docoff
 *)

let resource reduce += [
   << "and"{ 'bool1; 'bool2 } >>, reduce_and;
   << "or"{ 'bool1; 'bool2 } >>, reduce_or;
   << "not"{ 'boolean } >>, reduce_not;
   << ifthenelse{ "true"; 'true_case; 'false_case } >>,
      reduce_ifthenelse_true;
   << ifthenelse{ "false"; 'true_case; 'false_case } >>,
      reduce_ifthenelse_false
]

(*!
 * @begin[doc]
 * @modsubsection{Arithmetic}
 *
 * Integer arithmetic and comparison is rewritten using meta operations from
 * the @tt[Base_meta] module.  The rewrites are added to the @tt[reduce]
 * resource.  They are straightforward, and we omit an explicit listing of
 * them.
 * @end[doc]
 *)

(*!
 * @docoff
 *)

(* Define auxilary rewrites. *)

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

(* Define the actual rewrites. *)

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


(* Add the above rewrites to the reduce resource. *)

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

(*!
 * @begin[doc]
 * @modsubsection{Set membership}
 *
 * Set and interval membership is a straightforward comparison against
 * each of the intervals in a set and the endpoints of an interval.
 * Recall that intervals are closed.
 * @end[doc]
 *)

prim_rw reduce_member_interval :
   member{ 'num; interval{ 'left; 'right } } <-->
   "and"{ int_le{ 'left; 'num }; int_le{ 'num; 'right } }

prim_rw reduce_member_intset_ind :
   member{ 'num; intset{cons{'head; 'tail}} } <-->
   "or"{ member{'num; 'head}; member{'num; intset{'tail}} }

prim_rw reduce_member_intset_base :
   member{ 'num; intset{nil} } <-->
   "false"

prim_rw reduce_member_rawintset_ind :
   member{ 'num; rawintset[p:n, s:s]{cons{'head; 'tail}} } <-->
   "or"{ member{'num; 'head}; member{'num; rawintset[p:n, s:s]{'tail}} }

prim_rw reduce_member_rawintset_base :
   member{ 'num; rawintset[p:n, s:s]{nil} } <-->
   "false"

(*!
 * @begin[doc]
 *
 * Set constants can be rewritten into their actual values.
 * @end[doc]
 *)

prim_rw reduce_intset_max :
   intset_max <-->
   intset{ cons{ interval{. -1073741824; 1073741823}; nil } }

prim_rw reduce_enum_max :
   enum_max <-->
   intset{ cons{ interval{ 0; 2048 }; nil } }

(*!
 * @docoff
 *)

let resource reduce += [
   << member{ 'num; interval{ 'left; 'right } } >>,
      reduce_member_interval;
   << member{ 'num; intset{cons{'head; 'tail}} } >>,
      reduce_member_intset_ind;
   << member{ 'num; intset{nil} } >>,
      reduce_member_intset_base;
   << member{ 'num; rawintset[p:n, s:s]{cons{'head; 'tail}} } >>,
      reduce_member_rawintset_ind;
   << member{ 'num; rawintset[p:n, s:s]{nil} } >>,
      reduce_member_rawintset_base;
   << intset_max >>,
      reduce_intset_max;
   << enum_max >>,
      reduce_enum_max
]

(**************************************************************************
 * Display forms.
 **************************************************************************)

(*
 * Booleans.
 *)

dform true_df : except_mode[src] ::
   "true" =
   bf["true"]

dform false_df : except_mode[src] ::
   "false" =
   bf["false"]

dform or_df : except_mode[src] ::
   "or"{ 'bool1; 'bool2 } =
   `"(" slot{'bool1} vee space slot{'bool2} `")"

dform and_df : except_mode[src] ::
   "and"{ 'bool1; 'bool2 } =
   `"(" slot{'bool1} wedge space slot{'bool2} `")"

dform not_df : except_mode[src] ::
   "not"{ 'boolean } =
   tneg slot{'boolean}

dform ifthenelse_df : except_mode[src] ::
   ifthenelse{ 'test; 'true_case; 'false_case } =
   pushm[0] szone push_indent bf["if"] hspace
      szone slot{'test} ezone popm hspace
      push_indent bf["then"] hspace
      szone slot{'true_case} ezone popm hspace
      push_indent bf["else"] hspace
      szone slot{'false_case} ezone popm
      ezone popm

(*
 * Integers.
 *)

dform number_df : except_mode[src] ::
   number[i:n] =
   slot[i:n]

dform numeral_df : except_mode[src] ::
   numeral{ 'num } =
   bf["numeral"] `"(" slot{'num} `")"

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

(*
 * Lists.
 * nil terminated lists are displayed [elt_1; ... ; elt_n].
 * Non-nil terminated lists are displayed elt_1 :: ... :: elt_n.
 * The long term names below reduce the risk of collision with
 * other term names.
 *)

declare mfir_list_search{ 'examined; 'remaining }
declare mfir_list_semicolons{ 'elts }
declare mfir_list_semicolons{ 'last_elt; 'first_elts }
declare mfir_list_colons{ 'elts }
declare mfir_list_colons{ 'last_elt; 'first_elts }

(* Empty list. *)
dform nil_df : except_mode[src] ::
   nil =
   `"[]"

(* Search for nil entry. *)
dform cons_df : except_mode[src] ::
   cons{'elt; 'tail} =
   mfir_list_search{cons{'elt; nil}; 'tail}
dform mfir_list_search_df1 :
   mfir_list_search{'examined; cons{'head; 'tail}} =
   mfir_list_search{cons{'head; 'examined}; 'tail}

(* Found a nil terminator, so use bracket notation. *)
dform mfir_list_search_df2 :
   mfir_list_search{'examined; nil} =
   `"[" mfir_list_semicolons{'examined} `"]"

(* No nil terminator, so use :: notation. *)
dform mfir_list_search_df3 :
   mfir_list_search{'examined; 'last_elt} =
   mfir_list_colons{'examined} `" :: " slot{'last_elt}

(* Reverse entries and separate with ;. *)
dform mfir_list_semicolons_df1 :
   mfir_list_semicolons{cons{'last_elt; nil}} =
   slot{'last_elt}
dform mfir_list_semicolons_df2 :
   mfir_list_semicolons{cons{'last_elt; 'first_elts}} =
   mfir_list_semicolons{'first_elts} `"; " slot{'last_elt}

(* Reverse entries and separate with ::. *)
dform mfir_list_colons_df1 :
   mfir_list_colons{cons{'last_elt; nil}} =
   slot{'last_elt}
dform colons_df2 :
   mfir_list_colons{cons{'last_elt; 'first_elts}} =
   mfir_list_colons{'first_elts} `" :: " slot{'last_elt}

(*
 * Integer sets.
 *)

dform interval_df : except_mode[src] ::
   interval{ 'left; 'right } =
   `"[" slot{'left} `"," slot{'right} `"]"

dform intset_df : except_mode[src] ::
   intset{ 'interval_list } =
   bf["intset"] `" " slot{'interval_list}

dform rawintset_df : except_mode[src] ::
   rawintset[precision:n, sign:s]{ 'interval_list } =
   bf["rawintset"] sub{slot[precision:n]} sup{slot[sign:s]} `" "
      slot{'interval_list}

dform member_df : except_mode[src] ::
   member{ 'num; 'set } =
   slot{'num} member slot{'set}

dform intset_max_df : except_mode[src] ::
   intset_max =
   bf["intset_max"]

dform enum_max_df : except_mode[src] ::
   enum_max =
   bf["enum_max"]
