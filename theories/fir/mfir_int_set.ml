(*!
 * @begin[doc]
 * @module[Mfir_int_set]
 *
 * The @tt[Mfir_int_set] module implements sets of integers.
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
extends Mfir_int
extends Mfir_list

open Base_meta
open Top_conversionals


(**************************************************************************
 * Declarations.
 **************************************************************************)

(*!
 * @begin[doc]
 * @terms
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
 * @tt[rawintset] is similar to @tt[intset], except that the end points of
 * each interval are interpreted as raw integers with the specified precision
 * and signedness (see @hrefterm[tyRawInt] for a description of raw integers).
 * @end[doc]
 *)

declare interval{ 'left; 'right }
declare intset{ 'interval_list }
declare rawintset[precision:n, sign:s]{ 'interval_list }

(*!
 * @begin[doc]
 * @modsubsection{Set operations}
 *
 * The term @tt[member] is used to determine whether or not a number @tt[num]
 * is in a set or interval @tt[s].  The term @tt[subset] is used to determine
 * whether or not @tt[smaller_set] is a subset of @tt[larger_set].  The term
 * @tt[set_eq] is used to test two sets for equality.
 * @end[doc]
 *)

declare member{ 'num; 's }
declare subset{ 'smaller_set; 'larger_set }
declare set_eq{ 'set1; 'set2 }

(*!
 * @begin[doc]
 *
 * The term @tt[singleton] represents an integer set whose only member is $i$.
 * @end[doc]
 *)

declare singleton{ 'i }

(*!
 * @begin[doc]
 * @modsubsection{Constants}
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

(*!
 * @begin[doc]
 *
 * The term @tt[rawintset_max] is the set of allowed values for raw integers
 * with the specified precision and signedness.
 * @end[doc]
 *)

declare rawintset_max[precision:n, sign:s]

(*!
 * @docoff
 *)


(**************************************************************************
 * Rewrites.
 **************************************************************************)

(*
 * The following five rewrites are documented below (sorta).
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
 * @rewrites
 * @modsubsection{Set operations}
 *
 * The set (interval) membership relation $<< member{ 'i; 's } >>$
 * can be rewritten into a series of comparisons against the intervals
 * (endpoints) of $s$.  The rewrites are straightforward, and we omit
 * an explicit listing of them.
 *
 * The set subset relation is limited to cases when the larger set is
 * specified as exactly one interval, and both sets are integer sets.
 * @end[doc]
 *)

(* BUG: Really limitted form of the subset relation. *)

prim_rw reduce_subset_base :
   subset{ intset{ nil }; intset{ 'intervals } } <-->
   "true"

prim_rw reduce_subset_ind :
   subset{ intset{ cons{ interval{'i; 'j}; 'tail } };
           intset{ cons{ interval{'n; 'm}; nil } } } <-->
   "and"{ int_le{ 'n; 'i };
   "and"{ int_le{ 'j; 'm };
          subset{ intset{ 'tail };
                  intset{ cons{ interval{'n; 'm}; nil } } } } }

(*!
 * @begin[doc]
 *
 * Set equality is currently limited to testing whether or not two
 * integer sets are specified in exactly the same way.
 * @end[doc]
 *)

(* BUG: Really unintelligent form of equality being used here. *)

prim_rw reduce_set_eq :
   set_eq{ intset{ 'intervals }; intset{ 'intervals } } <-->
   "true"

(*!
 * @begin[doc]
 *
 * Singleton sets can be rewritten into actual integer sets.
 * @end[doc]
 *)

prim_rw reduce_singleton :
   singleton{ 'i } <-->
   intset{ cons{ interval{ 'i; 'i }; nil } }

(*!
 * @begin[doc]
 *
 * Set constants can be rewritten into their actual values.  These rewrites
 * are straightforward, and we omit an explicit listing of them.
 * @end[doc]
 *)

(*!
 * @docoff
 *)

prim_rw reduce_intset_max :
   intset_max <-->
   intset{ cons{ interval{. -1073741824; 1073741823}; nil } }

prim_rw reduce_enum_max :
   enum_max <-->
   intset{ cons{ interval{ 0; 2048 }; nil } }

prim_rw reduce_rawintset_max_u8 :
   rawintset_max[8, "unsigned"] <-->
   intset{ cons{ interval{ 0; 255 }; nil } }

prim_rw reduce_rawintset_max_s8 :
   rawintset_max[8, "signed"] <-->
   intset{ cons{ interval{. -128; 127 }; nil } }

prim_rw reduce_rawintset_max_u16 :
   rawintset_max[16, "unsigned"] <-->
   intset{ cons{ interval{ 0; 65536 }; nil } }

prim_rw reduce_rawintset_max_s16 :
   rawintset_max[16, "signed"] <-->
   intset{ cons{ interval{. -32768; 32767 }; nil } }

prim_rw reduce_rawintset_max_u32 :
   rawintset_max[32, "unsigned"] <-->
   intset{ cons{ interval{ 0; 4294967296}; nil } }

prim_rw reduce_rawintset_max_s32 :
   rawintset_max[32, "signed"] <-->
   intset{ cons{ interval{. -2147483648; 2147483647 }; nil } }

prim_rw reduce_rawintset_max_u64 :
   rawintset_max[64, "unsigned"] <-->
   intset{ cons{ interval{ 0; 18446744073709551616 }; nil } }

prim_rw reduce_rawintset_max_s64 :
   rawintset_max[64, "signed"] <-->
   intset{cons{interval{. -9223372036854775808; 9223372036854775807}; nil}}

(*!
 * @docoff
 *)

let resource reduce += [

   (* Set operations. *)

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

   << subset{ intset{ nil }; intset{ 'intervals } } >>,
      reduce_subset_base;
   << subset{ intset{ cons{ interval{'i; 'j}; 'tail } };
              intset{ cons{ interval{'n; 'm}; nil } } } >>,
      reduce_subset_ind;
   << set_eq{ intset{ 'intervals }; intset{ 'intervals } } >>,
      reduce_set_eq;
   << singleton{ 'i } >>,
      reduce_singleton;

   (* Constants. *)

   << intset_max >>,
      reduce_intset_max;
   << enum_max >>,
      reduce_enum_max;
   << rawintset_max[8, "unsigned"] >>,
      reduce_rawintset_max_u8;
   << rawintset_max[8, "signed"] >>,
      reduce_rawintset_max_s8;
   << rawintset_max[16, "unsigned"] >>,
      reduce_rawintset_max_u16;
   << rawintset_max[16, "signed"] >>,
      reduce_rawintset_max_s16;
   << rawintset_max[32, "unsigned"] >>,
      reduce_rawintset_max_u32;
   << rawintset_max[32, "signed"] >>,
      reduce_rawintset_max_s32;
   << rawintset_max[64, "unsigned"] >>,
      reduce_rawintset_max_u64;
   << rawintset_max[64, "signed"] >>,
      reduce_rawintset_max_s64
]


(**************************************************************************
 * Display forms.
 **************************************************************************)

(*
 * Integer sets.
 *)

dform interval_df : except_mode[src] ::
   interval{ 'left; 'right } =
   `"[" slot{'left} `"," slot{'right} `"]"

dform intset_df : except_mode[src] ::
   intset{ 'interval_list } =
   bf["intset"] `" " slot{'interval_list}

dform rawintset_df1 : except_mode[src] ::
   rawintset[precision:n, sign:s]{ 'interval_list } =
   bf["rawintset"] sub{slot[precision:n]} sup{it[sign:s]} `" "
      slot{'interval_list}

dform rawintset_df2 : except_mode[src] ::
   rawintset[precision:n, "signed"]{ 'interval_list } =
   bf["rawintset"] sub{slot[precision:n]} sup{bf["signed"]} `" "
      slot{'interval_list}

dform rawintset_df3 : except_mode[src] ::
   rawintset[precision:n, "unsigned"]{ 'interval_list } =
   bf["rawintset"] sub{slot[precision:n]} sup{bf["unsigned"]} `" "
      slot{'interval_list}

(*
 * Set operations.
 *)

dform member_df : except_mode[src] ::
   member{ 'num; 'set } =
   slot{'num} member slot{'set}

dform subset_df : except_mode[src] ::
   subset{ 'smaller_set; 'larger_set } =
   slot{'smaller_set} subseteq slot{'larger_set}

dform set_eq : except_mode[src] ::
   set_eq{ 'set1; 'set2 } =
   slot{'set1} `"=" slot{'set2}

dform singleton_df : except_mode[src] ::
   singleton{ 'i } =
   `"{" slot{'i} `"}"

(*
 * Constants.
 *)

dform intset_max_df : except_mode[src] ::
   intset_max =
   bf["intset_max"]

dform enum_max_df : except_mode[src] ::
   enum_max =
   bf["enum_max"]

dform rawintset_max_df1 : except_mode[src] ::
   rawintset_max[precision:n, sign:s] =
   bf["rawintset_max"] sub{slot[precision:n]} sup{it[sign:s]}

dform rawintset_max_df2 : except_mode[src] ::
   rawintset_max[precision:n, "signed"] =
   bf["rawintset_max"] sub{slot[precision:n]} sup{bf["signed"]}

dform rawintset_max_df3 : except_mode[src] ::
   rawintset_max[precision:n, "unsigned"] =
   bf["rawintset_max"] sub{slot[precision:n]} sup{bf["unsigned"]}
