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

open Top_conversionals
open Mfir_bool
open Mfir_int


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
 * type (see @hrefterm[tyUnion]).  An integer set is represented as a sorted
 * list of closed intervals (the first interval in a set contains the
 * least values of the set).
 *
 * The term @tt[interval] represents a closed interval.  The left endpoint
 * should be less then or equal to the right endpoint.  The term @tt[intset]
 * consists of a sorted list of intervals.  The parameters are tags to
 * indicate the precision and signedness of the endpoints of each interval.
 * These tags are ignored in the set operations below.
 * @end[doc]
 *)

declare interval{ 'left; 'right }
declare intset[precision:n, sign:s]{ 'interval_list }

(*!
 * @begin[doc]
 * @modsubsection{Set operations}
 *
 * The term @tt[member] is used to determine whether or not a number @tt[num]
 * is in a set or interval @tt[s].
 * @end[doc]
 *)

declare member{ 'num; 's }

(*!
 * @begin[doc]
 *
 * The term @tt[interval_lt] is used to test if all the integers in
 * @tt[interval1] are less than the integers in @tt[interval2].
 * @end[doc]
 *)

declare interval_lt{ 'interval1; 'interval2 }

(*!
 * @begin[doc]
 *
 * The term @tt[subset] is used to determine whether or not @tt[smaller_set]
 * is a subset of @tt[larger_set].  The term @tt[set_eq] is used to test two
 * sets for equality.
 * @end[doc]
 *)

declare subset{ 'smaller_set; 'larger_set }
declare set_eq{ 'set1; 'set2 }

(*!
 * @begin[doc]
 *
 * The term @tt[singleton] represents an integer set whose only member is $i$.
 * @end[doc]
 *)

declare singleton[precision:n, sign:s]{ 'i }

(*!
 * @begin[doc]
 * @modsubsection{Constants}
 *
 * The term @tt[intset_max] is the set of all integers with the given
 * precision and signedness.  Precisions of 8, 16, 31, 32, and 64 are
 * currently supported.  The signedness may be ``signed'' or ``unsigned''.
 * @end[doc]
 *)

declare intset_max[precision:n, sign:s]

(*!
 * @begin[doc]
 *
 * The term @tt[enum_max] is the set of allowed values for the parameter of
 * @hrefterm[tyEnum].
 * @end[doc]
 *)

declare enum_max

(*!
 * @docoff
 *)


(**************************************************************************
 * Rewrites.
 **************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 * @modsubsection{Set operations}
 *
 * The set (interval) membership relation $<< member{ 'i; 's } >>$
 * can be rewritten into a series of comparisons against the intervals
 * (endpoints) of $s$.
 * @end[doc]
 *)

prim_rw reduce_member_interval :
   member{ number[i:n]; interval{ number[l:n]; number[r:n] } } <-->
   "and"{ int_le{ number[l:n]; number[i:n] };
          int_le{ number[i:n]; number[r:n] } }

prim_rw reduce_member_intset_ind :
   member{ number[i:n]; intset[p:n, str:s]{cons{'head; 'tail}} } <-->
   "or"{ member{number[i:n]; 'head};
         member{number[i:n]; intset[p:n, str:s]{'tail}} }

prim_rw reduce_member_intset_base :
   member{ number[i:n]; intset[p:n, str:s]{nil} } <-->
   "false"

(*!
 * @docoff
 *)

let reduce_member_interval_actual =
   reduce_member_interval thenC
   (addrC [0] reduce_int_le) thenC
   (addrC [1] reduce_int_le) thenC
   reduce_and thenC
   reduce_ifthenelse

let reduce_member =
   reduce_member_interval_actual orelseC
   reduce_member_intset_base orelseC
   (  reduce_member_intset_ind thenC
      (addrC [0] reduce_member_interval_actual) thenC
      reduce_or thenC
      reduce_ifthenelse
   )

(*!
 * @begin[doc]
 *
 * Comparing two intervals is straightforward.
 * @end[doc]
 *)

prim_rw reduce_interval_lt_aux :
   interval_lt{ interval{ number[i:n]; number[j:n] };
                interval{ number[m:n]; number[n:n] } } <-->
   int_lt{ number[j:n]; number[m:n] }

(*!
 * @docoff
 *)

let reduce_interval_lt =
   reduce_interval_lt_aux thenC reduce_int_lt

(*!
 * @begin[doc]
 *
 * The subset relation depends on the two sets (intervals) being
 * well-formed.
 * @end[doc]
 *)

prim_rw reduce_subset_interval_aux :
   subset{ interval{ number[i:n]; number[j:n] };
           interval{ number[n:n]; number[m:n] } } <-->
   "and"{ int_le{ number[n:n]; number[i:n] };
          int_le{ number[j:n]; number[m:n] } }

prim_rw reduce_subset_base1 :
   subset{ intset[p1:n, s1:s]{ nil }; intset[p2:n, s2:s]{ 'intervals } } <-->
   "true"

prim_rw reduce_subset_base2 :
   subset{ intset[p1:n, s1:s]{cons{'a; 'b}}; intset[p2:n, s2:s]{nil} } <-->
   "false"

prim_rw reduce_subset_ind :
   subset{ intset[p1:n, s1:s]{ cons{ 'head1; 'tail1 } };
           intset[p2:n, s2:s]{ cons{ 'head2; 'tail2 } } } <-->
   ifthenelse{ interval_lt{ 'head2; 'head1 };
      subset{ intset[p1:n, s1:s]{ cons{ 'head1; 'tail1 } };
              intset[p2:n, s2:s]{ 'tail2 } };
      ifthenelse{ subset{ 'head1; 'head2 };
         subset{ intset[p1:n, s1:s]{ 'tail1 };
                 intset[p2:n, s2:s]{ cons{ 'head2; 'tail2 } } };
         "false"
      }
   }

(*!
 * @docoff
 *)

let reduce_subset_interval =
   reduce_subset_interval_aux thenC
   (addrC [0] reduce_int_le) thenC
   (addrC [1] reduce_int_le) thenC
   reduce_and thenC
   reduce_ifthenelse

let reduce_subset =
   reduce_subset_interval orelseC
   reduce_subset_base1 orelseC
   reduce_subset_base2 orelseC
   (  reduce_subset_ind thenC
      (addrC [0] reduce_interval_lt) thenC
      reduce_ifthenelse thenC
      (tryC (addrC [0] reduce_subset_interval)) thenC
      (tryC reduce_ifthenelse)
   )

(*!
 * @begin[doc]
 *
 * Set equality is defined in the usual way.
 * @end[doc]
 *)

prim_rw reduce_set_eq_aux :
   set_eq{ 'set1; 'set2 } <-->
   "and"{ subset{ 'set1; 'set2 }; subset{ 'set2; 'set1 } }

(*!
 * @docoff
 *)

let reduce_set_eq =
   reduce_set_eq_aux thenC
   (addrC [0] (repeatC reduce_subset)) thenC
   reduce_and thenC
   reduce_ifthenelse thenC
   (tryC (repeatC reduce_subset))

(*!
 * @begin[doc]
 *
 * Singleton sets can be rewritten into actual integer sets.
 * @end[doc]
 *)

prim_rw reduce_singleton :
   singleton[precision:n, sign:s]{ 'i } <-->
   intset[precision:n, sign:s]{ cons{ interval{ 'i; 'i }; nil } }

(*!
 * @begin[doc]
 * @modsubsection{Constants}
 *
 * Set constants can be rewritten into their actual values.  These rewrites
 * are straightforward, and we omit an explicit listing of them.
 * @end[doc]
 *)

(*!
 * @docoff
 *)

prim_rw reduce_enum_max :
   enum_max <-->
   intset[32, "signed"]{ cons{ interval{ 0; 2048 }; nil } }

prim_rw reduce_intset_max_u8 :
   intset_max[8, "unsigned"] <-->
   intset[8, "unsigned"]{ cons{ interval{ 0; 255 }; nil } }

prim_rw reduce_intset_max_s8 :
   intset_max[8, "signed"] <-->
   intset[8, "signed"]{ cons{ interval{. -128; 127 }; nil } }

prim_rw reduce_intset_max_u16 :
   intset_max[16, "unsigned"] <-->
   intset[16, "unsigned"]{ cons{ interval{ 0; 65536 }; nil } }

prim_rw reduce_intset_max_s16 :
   intset_max[16, "signed"] <-->
   intset[16, "signed"]{ cons{ interval{. -32768; 32767 }; nil } }

prim_rw reduce_intset_max_u31 :
   intset_max[31, "unsigned"] <-->
   intset[31, "unsigned"]{ cons{ interval{ 0; 2147483647 }; nil } }

prim_rw reduce_intset_max_s31 :
   intset_max[31, "signed"] <-->
   intset[31, "signed"]{ cons{ interval{. -1073741824; 1073741823}; nil } }

prim_rw reduce_intset_max_u32 :
   intset_max[32, "unsigned"] <-->
   intset[32, "unsigned"]{ cons{ interval{ 0; 4294967296}; nil } }

prim_rw reduce_intset_max_s32 :
   intset_max[32, "signed"] <-->
   intset[32, "signed"]{ cons{ interval{. -2147483648; 2147483647 }; nil } }

prim_rw reduce_intset_max_u64 :
   intset_max[64, "unsigned"] <-->
   intset[64, "unsigned"]{ cons{ interval{ 0; 18446744073709551616 }; nil } }

prim_rw reduce_intset_max_s64 :
   intset_max[64, "signed"] <-->
   intset[64, "signed"]{cons{interval{. -9223372036854775808; 9223372036854775807}; nil}}

let reduce_intset_max =
   reduce_intset_max_u8 orelseC
   reduce_intset_max_s8 orelseC
   reduce_intset_max_u16 orelseC
   reduce_intset_max_s16 orelseC
   reduce_intset_max_u31 orelseC
   reduce_intset_max_s31 orelseC
   reduce_intset_max_u32 orelseC
   reduce_intset_max_s32 orelseC
   reduce_intset_max_u64 orelseC
   reduce_intset_max_s64

let resource reduce += [

   (* Set operations. *)

   << member{ 'num; 'set } >>,
      reduce_member;
   << subset{ 'set1; 'set2 } >>,
      reduce_subset;
   << set_eq{ 'set1; 'set2 } >>,
      reduce_set_eq;
   << singleton[precision:n, sign:s]{ 'i } >>,
      reduce_singleton;

   (* Constants. *)

   << intset_max[precision:n, sign:s] >>,
      reduce_intset_max;
   << enum_max >>,
      reduce_enum_max

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

dform intset_df1 : except_mode[src] ::
   intset[precision:n, sign:s]{ 'interval_list } =
   bf["intset"] sub{slot[precision:n]} sup{it[sign:s]} `" "
      slot{'interval_list}

dform intset_df2 : except_mode[src] ::
   intset[precision:n, "signed"]{ 'interval_list } =
   bf["intset"] sub{slot[precision:n]} sup{bf["signed"]} `" "
      slot{'interval_list}

dform intset_df3 : except_mode[src] ::
   intset[precision:n, "unsigned"]{ 'interval_list } =
   bf["intset"] sub{slot[precision:n]} sup{bf["unsigned"]} `" "
      slot{'interval_list}

(*
 * Set operations.
 *)

dform member_df : except_mode[src] ::
   member{ 'num; 'set } =
   slot{'num} member slot{'set}

dform interval_lt_df : except_mode[src] ::
   interval_lt{ 'interval1; 'interval2 } =
   slot{'interval1} `"<" slot{'interval2}

dform subset_df : except_mode[src] ::
   subset{ 'smaller_set; 'larger_set } =
   slot{'smaller_set} subseteq slot{'larger_set}

dform set_eq : except_mode[src] ::
   set_eq{ 'set1; 'set2 } =
   slot{'set1} `"=" slot{'set2}

dform singleton_df1 : except_mode[src] ::
   singleton[precision:n, sign:s]{ 'i } =
   `"{" slot{'i} `"}" sub{slot[precision:n]} sup{it[sign:s]}

dform singleton_df2 : except_mode[src] ::
   singleton[precision:n, "signed"]{ 'i } =
   `"{" slot{'i} `"}" sub{slot[precision:n]} sup{bf["signed"]}

dform singleton_df3 : except_mode[src] ::
   singleton[precision:n, "unsigned"]{ 'i } =
   `"{" slot{'i} `"}" sub{slot[precision:n]} sup{bf["unsigned"]}

(*
 * Constants.
 *)

dform intset_max_df1 : except_mode[src] ::
   intset_max[precision:n, sign:s] =
   bf["intset_max"] sub{slot[precision:n]} sup{it[sign:s]}

dform intset_max_df2 : except_mode[src] ::
   intset_max[precision:n, "signed"] =
   bf["intset_max"] sub{slot[precision:n]} sup{bf["signed"]}

dform intset_max_df3 : except_mode[src] ::
   intset_max[precision:n, "unsigned"] =
   bf["intset_max"] sub{slot[precision:n]} sup{bf["unsigned"]}

dform enum_max_df : except_mode[src] ::
   enum_max =
   bf["enum_max"]
