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

(*
 * NOTE: To make this file remotely readable, I've gone ahead and made
 * lines that are _much_ longer than 80 characters.
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
 * least values of the set).  Sets are assumed to be ``normalized''; in
 * addition to being sorted, no two intervals in a set should overlap,
 * and it should never be the case that two adjacent intervals are of the
 * form $[a,i],[i+1,b]$.
 *
 * The term @tt[interval] represents a closed interval.  The left endpoint
 * should be less then or equal to the right endpoint.  The term @tt[intset]
 * consists of a sorted list of intervals.  The parameters are tags to
 * indicate the precision and signedness of the endpoints of each interval.
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
 * The term @tt[normalize] is used to normalize a set.  It does normalize
 * an abitrary set (see the rewrites below).
 * @end[doc]
 *)

declare normalize{ 'set }

(*!
 * @begin[doc]
 * The term @tt[subset] is used to determine whether or not @tt[smaller_set]
 * is a subset of @tt[larger_set].  The term @tt[set_eq] is used to test two
 * sets for equality.  The term @tt[union] takes the union of two sets.
 * @end[doc]
 *)

declare subset{ 'smaller_set; 'larger_set }
declare set_eq{ 'set1; 'set2 }
declare union{ 'set1; 'set2 }

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
 * @begin[doc]
 * @modsubsection{Auxiliary terms}
 *
 * The following terms are not available outside the @tt[Mfir_int_set] module.
 * They are used internally to express the computations represented by the
 * above set operations.
 *
 * The term @tt[interval_lt] is used to determine if all the members of
 * @tt[interval1] are less than the members of @tt[interval2].
 * @end[doc]
 *)

declare interval_lt{ 'interval1; 'interval2 }

(*!
 * @begin[doc]
 *
 * The next two terms are used in computing the union of two sets.
 * @end[doc]
 *)

declare union_aux{ 'interval; 'head1; 'tail1; 'head2; 'tail2 }
declare union_interval{ 'interval1; 'interval2 }

(*!
 * @docoff
 *)


(**************************************************************************
 * Rewrites.
 **************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 * @modsubsection{Interval operations}
 *
 * Rewriting of interval operations is straightforward.
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
 * @modsubsection{Set membership}
 *
 * The @tt[reduce_member] conversional reduces the set membership relation
 * $<< member{ 'i; 'set } >>$ to either $<< "true" >>$ or $<< "false" >>$,
 * using the rewrites below.
 * @end[doc]
 *)

prim_rw reduce_member_interval_aux :
   member{ number[i:n]; interval{ number[l:n]; number[r:n] } } <-->
   "and"{ int_le{ number[l:n]; number[i:n] };
          int_le{ number[i:n]; number[r:n] } }

prim_rw reduce_member_intset_base :
   member{ number[i:n]; intset[p:n, s:s]{nil} } <-->
   "false"

prim_rw reduce_member_intset_ind :
   member{ number[i:n];
           intset[p:n, s:s]{ cons{ interval{number[j:n]; number[k:n]}; 'tail } } }
   <-->
   "or"{ member{ number[i:n]; interval{ number[j:n]; number[k:n] } };
         member{ number[i:n]; intset[p:n, s:s]{ 'tail } } }

(*!
 * @docoff
 *)

let reduce_member_interval =
   reduce_member_interval_aux thenC
   (addrC [0] reduce_int_le) thenC
   (addrC [1] reduce_int_le) thenC
   reduce_and thenC
   reduce_ifthenelse

let reduce_member =
   reduce_member_intset_base orelseC
   (  reduce_member_intset_ind thenC
      (addrC [0] reduce_member_interval) thenC
      reduce_or thenC
      reduce_ifthenelse
   )

let resource reduce += [
   << member{ number[i:n]; intset[p:n, s:s]{ 'intervals } } >>, reduce_member
]

(*!
 * @begin[doc]
 *
 * Set normalization is limited to combining intervals of the form
 * $[a,i],[i+1,b]$.  Other ``normalization'' propertiers of integer sets are
 * assumed to already hold.  The rewrites below are combined into the
 * @tt[reduce_normalize] conversional.  Only well-formed sets can be
 * normalized.
 * @end[doc]
 *)

prim_rw reduce_normalize_aux :
   normalize{ intset[p:n, s:s]{ 'intervals } } <-->
   intset[p:n, s:s]{ normalize{ 'intervals } }

prim_rw reduce_normalize_base1 :
   normalize{ nil } <-->
   nil

prim_rw reduce_normalize_base2 :
   normalize{ cons{ interval{ number[i:n]; number[j:n] }; nil } } <-->
   cons{ interval{ number[i:n]; number[j:n] }; nil }

prim_rw reduce_normalize_ind :
   normalize{ cons{ interval{ number[i:n]; number[j:n] };
              cons{ interval{ number[m:n]; number[n:n] }; 'tail } } } <-->
      ifthenelse{ int_eq{ (number[j:n] +@ 1); number[m:n] };
         normalize{ cons{ interval{ number[i:n]; number[n:n] }; 'tail } };
         cons{ interval{ number[i:n]; number[j:n] };
               normalize{ cons{ interval{ number[m:n]; number[n:n] }; 'tail } } } }

(*!
 * @docoff
 *)

let reduce_normalize_intervals =
   reduce_normalize_base1 orelseC
   reduce_normalize_base2 orelseC
   (  reduce_normalize_ind thenC
      (addrC [0; 0] reduce_add) thenC
      (addrC [0] reduce_int_eq) thenC
      reduce_ifthenelse
   )

let reduce_normalize =
   reduce_normalize_aux thenC
   (addrC [0] (repeatC (higherC reduce_normalize_intervals)))

let resource reduce += [
   << normalize{ intset[p:n, s:s]{ 'intervals } } >>, reduce_normalize
]

(*!
 * @begin[doc]
 *
 * The @tt[reduce_subset] conversional uses the rewrites below to reduce
 * $<< subset{ 'set1; 'set2 } >>$, where $<< 'set1 >>$ and $<< 'set2 >>$ must
 * both be well-formed sets.
 * @end[doc]
 *)

prim_rw reduce_subset_interval_aux :
   subset{ interval{ number[i:n]; number[j:n] };
           interval{ number[n:n]; number[m:n] } } <-->
   "and"{ int_le{ number[n:n]; number[i:n] };
          int_le{ number[j:n]; number[m:n] } }

prim_rw reduce_subset_base1 :
   subset{ intset[p:n, s:s]{ nil }; intset[p:n, s:s]{ 'intervals } } <-->
   "true"

prim_rw reduce_subset_base2 :
   subset{ intset[p:n, s:s]{cons{'a; 'b}}; intset[p:n, s:s]{nil} } <-->
   "false"

prim_rw reduce_subset_ind :
   subset{ intset[p:n, s:s]{ cons{ interval{ number[i:n]; number[j:n] }; 'tail1 } };
           intset[p:n, s:s]{ cons{ interval{ number[m:n]; number[n:n] }; 'tail2 } } }
   <-->
   ifthenelse{ interval_lt{ interval{ number[m:n]; number[n:n] };
                            interval{ number[i:n]; number[j:n] } };
      subset{ intset[p:n, s:s]{ cons{ interval{ number[i:n]; number[j:n] }; 'tail1 } };
              intset[p:n, s:s]{ 'tail2 } };
      ifthenelse{ subset{ interval{ number[i:n]; number[j:n] };
                          interval{ number[m:n]; number[n:n] } };
         subset{ intset[p:n, s:s]{ 'tail1 };
                 intset[p:n, s:s]{ cons{ interval{ number[m:n]; number[n:n] }; 'tail2 } } };
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

let resource reduce += [
   << subset{ 'set1; 'set2 } >>, reduce_subset
]

(*!
 * @begin[doc]
 *
 * ...
 * @end[doc]
 *)

prim_rw reduce_union_start :
   union{ intset[p:n, s:s]{ 'intervals1 }; intset[p:n, s:s]{ 'intervals2 } } <-->
   normalize{ intset[p:n, s:s]{ union{ 'intervals1; 'intervals2 } } }

prim_rw reduce_union_base1 :
   union{ nil; 'intervals } <-->
   'intervals

prim_rw reduce_union_base2 :
   union{ cons{ 'a; 'b }; nil } <-->
   cons{ 'a; 'b }

prim_rw reduce_union_ind :
   union{ cons{ 'head1; 'tail1 }; cons{ 'head2; 'tail2 } } <-->
   ifthenelse{ interval_lt{ 'head1; 'head2 };
      cons{ 'head1; union{ 'tail1; cons{ 'head2; 'tail2 } } };
      ifthenelse{ interval_lt{ 'head2; 'head1 };
         cons{ 'head2; union{ cons{ 'head1; 'tail1 }; 'tail2 } };
         union_aux{ union_interval{ 'head1; 'head2}; 'head1; 'tail1; 'head2; 'tail2 } } }

prim_rw reduce_union_interval :
   union_interval{ interval{ number[i:n]; number[j:n] };
                   interval{ number[m:n]; number[n:n] } } <-->
   interval{ int_min{ number[i:n]; number[m:n] };
             int_max{ number[j:n]; number[n:n] } }

prim_rw reduce_union_aux :
   union_aux{ 'interval; interval{ number[i:n]; number[j:n] }; 'tail1;
                         interval{ number[m:n]; number[n:n] }; 'tail2 } <-->
      ifthenelse{ int_lt{ number[j:n]; number[n:n] };
         union{ 'tail1; cons{ 'interval; 'tail2 } };
         union{ cons{ 'interval; 'tail1 }; 'tail2 } }

(*!
 * @docoff
 *)

(* XXX union auto should go here *)

let reduce_union =
   reduce_union_start

let resource reduce += [
   << union{ 'set1; 'set2 } >>, reduce_union
]

(*!
 * @begin[doc]
 *
 * Set equality is defined in the usual way.  The @tt[reduce_set_eq]
 * conversional uses the rewrite below, along with other rewrites, to avoid
 * computing $<< subset{ 'set2; 'set1 } >>$ in cases where it is not
 * necessary.
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

let resource reduce += [
   << set_eq{ 'set1; 'set2 } >>, reduce_set_eq
]

(*!
 * @begin[doc]
 *
 * Singleton sets can be rewritten into actual integer sets.
 * @end[doc]
 *)

prim_rw reduce_singleton :
   singleton[precision:n, sign:s]{ number[i:n] } <-->
   intset[precision:n, sign:s]{ cons{ interval{ number[i:n]; number[i:n] }; nil } }

(*!
 * @docoff
 *)

let resource reduce += [
   << singleton[precision:n, sign:s]{ number[i:n] } >>, reduce_singleton
]

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
   << intset_max[precision:n, sign:s] >>, reduce_intset_max;
   << enum_max >>, reduce_enum_max
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

dform normalize_df : except_mode[src] ::
   normalize{ 'set } =
   bf["normalize"] `"(" slot{'set} `")"

dform subset_df : except_mode[src] ::
   subset{ 'smaller_set; 'larger_set } =
   slot{'smaller_set} subseteq slot{'larger_set}

dform set_eq : except_mode[src] ::
   set_eq{ 'set1; 'set2 } =
   slot{'set1} `"=" slot{'set2}

dform union : except_mode[src] ::
   union{ 'set1; 'set2 } =
   `"(" slot{'set1} cup slot{'set2} `")"

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

(*
 * Auxiliary terms.
 *)

dform interval_lt_df : except_mode[src] ::
   interval_lt{ 'interval1; 'interval2 } =
   slot{'interval1} `"<" sub{it["interval"]} slot{'interval2}

dform union_aux_df : except_mode[src] ::
   union_aux{ 'interval; 'head1; 'tail1; 'head2; 'tail2 } =
   bf["union_aux"] `"(" slot{'interval} `"," slot{cons{'head1;'tail1}}
      `"," slot{cons{'head2;'tail2}} `")"

dform union_interval_df : except_mode[src] ::
   union_interval{ 'interval1; 'interval2 } =
   `"(" slot{'interval1} cup sub{it["interval"]} slot{'interval2} `")"
