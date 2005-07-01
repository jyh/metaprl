doc <:doc<
   @module[Mfir_int_set]

   The @tt[Mfir_int_set] module defines integer sets and operations on them.

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

doc docoff

open Basic_tactics
open Mfir_bool
open Mfir_int


(**************************************************************************
 * Declarations.
 **************************************************************************)

doc <:doc<
   @terms
   @modsubsection{Integer sets}

   The FIR uses integer sets in pattern matching expressions (see
   @hrefterm[matchExp]), and to designate a subset of the cases of a union
   definition.  An integer set is represented as a sorted list of closed
   intervals.  The intervals are sorted in ascending order. Sets are assumed
   to be @emph{normalized}; in addition to being sorted, no two intervals in a
   set should overlap, and it should never be the case that two adjacent
   intervals are of the form $[a,i],[i+1,b]$.

   The term @tt[interval] represents a closed interval.  The left endpoint
   should be less then or equal to the right endpoint.  The term @tt[intset]
   consists of a sorted list of intervals.  The parameters are tags to
   indicate the precision and signedness of the endpoints of each interval.
>>

declare interval{ 'left; 'right }
declare intset[precision:n, sign:s]{ 'interval_list }


doc <:doc<
   @modsubsection{Set operations}

   The term @tt[member] tests if @tt[num] is a member of the set @tt[s].
>>

declare member{ 'num; 's }


doc <:doc<

   The term @tt[normalize] is used to normalize a set by joining intervals
   of the form $[a,i],[i+1,b]$.  It performs no other actions in normalizing
   a set.
>>

declare normalize{ 'set }


doc <:doc<
   The term @tt[subset] is used to determine whether or not @tt[set1]
   is a subset of @tt[set2].  The term @tt[set_eq] is used to test two
   sets for equality.  The term @tt[union] takes the union of two sets.
>>

declare "subset"{ 'set1; 'set2 }
declare set_eq{ 'set1; 'set2 }
declare union{ 'set1; 'set2 }


doc <:doc<
   @modsubsection{Constants}

   The term @tt[intset_max] is the set of all integers with the given
   bit-precision and signedness.  Precisions of 8, 16, 31, 32, and 64 are
   currently supported.  The signedness may be ``signed'' or ``unsigned''.
   The term @tt[enum_max] is the set of allowed values for the parameter
   of @hrefterm[tyEnum]
>>

declare intset_max[precision:n, sign:s]
declare enum_max

doc <:doc<
   @docoff
>>


(**************************************
 * The following are auxiliary terms.  They are not available outside the
 * Mfir_int_set module.  They are used to simplify the reductions for
 * integer set operations.
 *)

declare interval_lt{ 'interval1; 'interval2 }
declare union_aux{ 'interval; 'h1; 't1; 'h2; 't2 }
declare union_interval{ 'interval1; 'interval2 }

doc <:doc<
   @docoff
>>


(**************************************************************************
 * Rewrites.
 **************************************************************************)

doc <:doc<
   @rewrites
   @modsubsection{Interval operations}

   Rewriting of interval operations is straightforward. Note that in
   taking the union of two intervals, we assume that the two intervals
   overlap.
>>

prim_rw reduce_interval_lt_main :
   interval_lt{ interval{ number[i:n]; number[j:n] };
                interval{ number[m:n]; number[n:n] } } <-->
   int_lt{ number[j:n]; number[m:n] }

prim_rw reduce_union_interval_main :
   union_interval{ interval{ number[i:n]; number[j:n] };
                   interval{ number[m:n]; number[n:n] } } <-->
   interval{ int_min{ number[i:n]; number[m:n] };
             int_max{ number[j:n]; number[n:n] } }

prim_rw reduce_subset_interval_main :
    (interval{ number[i:n]; number[j:n] } subset
     interval{ number[n:n]; number[m:n] } ) <-->
   "and"{ int_le{ number[n:n]; number[i:n] };
          int_le{ number[j:n]; number[m:n] } }

doc <:doc<
   @docoff
>>

let reduce_interval_lt =
   reduce_interval_lt_main thenC reduce_int_lt

let reduce_union_interval =
   reduce_union_interval_main thenC
   (addrC [Subterm 1] reduce_int_min) thenC
   (addrC [Subterm 2] reduce_int_max)

let reduce_subset_interval =
   reduce_subset_interval_main thenC
   (addrC [Subterm 1] reduce_int_le) thenC
   (addrC [Subterm 2] reduce_int_le) thenC
   reduce_and thenC
   reduce_ifthenelse


doc <:doc<
   @modsubsection{Set operations}

   Testing for set membership is straightforward.
>>

prim_rw reduce_member_intset_base :
   member{ number[i:n]; intset[p:n, s:s]{nil} } <-->
   "false"

prim_rw reduce_member_intset_ind :
   member{ number[i:n];
           intset[p:n, s:s]{ (interval{number[j:n]; number[k:n]} :: 'tail) } }
   <-->
   (if "and"{ int_le{ number[j:n]; number[i:n] };
              int_le{ number[i:n]; number[k:n] } }
   then
      "true"
   else
         member{ number[i:n]; intset[p:n, s:s]{ 'tail } })

doc <:doc<
   @docoff
>>

let reduce_member =
   reduce_member_intset_base orelseC
   (  reduce_member_intset_ind thenC
      (addrC [Subterm 1; Subterm 1] reduce_int_le) thenC
      (addrC [Subterm 1; Subterm 2] reduce_int_le) thenC
      (addrC [Subterm 1] reduce_and) thenC
      (addrC [Subterm 1] reduce_ifthenelse) thenC
      reduce_ifthenelse
   )

let resource reduce += [
   << member{ number[i:n]; intset[p:n, s:s]{ 'intervals } } >>, reduce_member
]


doc <:doc<

   Set normalization is limited to combining intervals of the form
   $[a,i],[i+1,b]$.  We assume that the intervals are sorted and
   non-overlapping.
>>

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
            normalize{ cons{ interval{number[m:n]; number[n:n]}; 'tail } } } }

doc <:doc<
   @docoff
>>

let reduce_normalize_intervals =
   reduce_normalize_base1 orelseC
   reduce_normalize_base2 orelseC
   (  reduce_normalize_ind thenC
      (addrC [Subterm 1; Subterm 1] reduce_add) thenC
      (addrC [Subterm 1] reduce_int_eq) thenC
      reduce_ifthenelse
   )

let reduce_normalize =
   reduce_normalize_aux thenC
   (addrC [Subterm 1] (repeatC (higherC reduce_normalize_intervals)))

let resource reduce += [
   << normalize{ intset[p:n, s:s]{ 'intervals } } >>, reduce_normalize
]


doc <:doc<

   The @tt[reduce_subset] conversional uses the three rewrites below to reduce
   <<'set1 subset 'set2>>.  The cases in which one of the sets is
   empty are straightforward.  The case in which both sets are non-empty
   reduces to a case analysis on the first interval in each set.
>>

prim_rw reduce_subset_base1 :
   (intset[p:n, s:s]{ nil } subset intset[p:n, s:s]{ 'intervals })  <-->
   "true"

prim_rw reduce_subset_base2 :
   (intset[p:n, s:s]{cons{'a; 'b}} subset intset[p:n, s:s]{nil})  <-->
   "false"

prim_rw reduce_subset_ind :
   ( intset[p:n, s:s]{ (interval{ number[i:n]; number[j:n] } :: 't1) } subset
    intset[p:n, s:s]{ (interval{ number[m:n]; number[n:n] } :: 't2) } )
   <-->
   (if interval_lt{ interval{ number[m:n]; number[n:n] };
                    interval{ number[i:n]; number[j:n] } }
    then
     ( intset[p:n, s:s]{ (interval{number[i:n]; number[j:n]} :: 't1) } subset
       intset[p:n, s:s]{ 't2 } )
    else if  interval{ number[i:n]; number[j:n] } subset
             interval{ number[m:n]; number[n:n] }
    then
      intset[p:n, s:s]{ 't1 } subset
      intset[p:n, s:s]{ (interval{number[m:n]; number[n:n]} :: 't2) }
    else
      "false")

doc <:doc<
   @docoff
>>

let reduce_subset =
   reduce_subset_interval orelseC
   reduce_subset_base1 orelseC
   reduce_subset_base2 orelseC
   (  reduce_subset_ind thenC
      (addrC [Subterm 1] reduce_interval_lt) thenC
      reduce_ifthenelse thenC
      (tryC (addrC [Subterm 1] reduce_subset_interval)) thenC
      (tryC reduce_ifthenelse)
   )

let resource reduce += [
   << 'set1 subset 'set2  >>, reduce_subset
]


doc <:doc<

   Computing the union of two integer sets is rather involved.
   The cases in which one of the sets is empty are straightforward.
   The case in which both sets are non-empty reduces to a case
   analysis on the first interval in each set.
>>

prim_rw reduce_union_start :
   union{ intset[p:n, s:s]{ 'l1 }; intset[p:n, s:s]{ 'l2 } } <-->
   normalize{ intset[p:n, s:s]{ union{ 'l1; 'l2 } } }

prim_rw reduce_union_base1 :
   union{ nil; 'l } <-->
   'l

prim_rw reduce_union_base2 :
   union{ ('h :: 't); nil } <-->
   ('h :: 't)

prim_rw reduce_union_ind :
   union{ ('h1 :: 't1); ('h2 :: 't2) } <-->
   (if interval_lt{ 'h1; 'h2 } then
      ('h1 :: union{ 't1; ('h2 :: 't2) })
    else if interval_lt{ 'h2; 'h1 } then
      ('h2 :: union{ ('h1 :: 't1); 't2 })
    else
      union_aux{ union_interval{ 'h1; 'h2 }; 'h1; 't1; 'h2; 't2 })

prim_rw reduce_union_aux :
   union_aux{ 'l; interval{ number[i:n]; number[j:n] }; 't1;
                  interval{ number[m:n]; number[n:n] }; 't2 } <-->
   (if int_lt{ number[j:n]; number[n:n] } then
      union{ 't1; ('l :: 't2) }
   else
      union{ ('l :: 't1); 't2 })

doc <:doc<
   @docoff
>>

(*
 * I'm not taking the time and effort to make a truly intelligent
 * conversional.  It's not worth it.  --emre
 *)

let union_list = [
   reduce_union_base1;
   reduce_union_base2;
   reduce_union_ind;
   reduce_union_interval;
   reduce_union_aux;
   reduce_interval_lt;
   reduce_int_min;
   reduce_int_max;
   reduce_int_lt;
   reduce_ifthenelse
]

let reduce_union =
   reduce_union_start thenC
   (addrC [Subterm 1; Subterm 1] (repeatC (higherC (firstC union_list)))) thenC
   reduce_normalize

let resource reduce += [
   << union{ 'set1; 'set2 } >>, reduce_union
]


doc <:doc<

   Set equality is defined in the usual way.
>>

prim_rw reduce_set_eq_aux :
   set_eq{ 's1; 's2 } <-->
   "and"{. 's1 subset 's2 ; .'s2 subset 's1  }

doc <:doc<
   @docoff
>>

let reduce_set_eq =
   reduce_set_eq_aux thenC
   (addrC [Subterm 1] (repeatC reduce_subset)) thenC
   reduce_and thenC
   reduce_ifthenelse thenC
   (tryC (repeatC reduce_subset))

let resource reduce += [
   << set_eq{ 's1; 's2 } >>, reduce_set_eq
]

doc <:doc<
   @modsubsection{Constants}

   Set constants can be rewritten into their actual values.  These rewrites
   are straightforward, and we omit an explicit listing of them.
   @docoff
>>

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
   "subset"{ 'set1; 'set2 } =
   slot{'set1} subseteq slot{'set2}

dform set_eq_df : except_mode[src] ::
   set_eq{ 'set1; 'set2 } =
   slot{'set1} `"=" sub{it["set"]} slot{'set2}

dform union_df : except_mode[src] ::
   union{ 'set1; 'set2 } =
   `"(" slot{'set1} cup slot{'set2} `")"


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
   union_aux{ 'interval; 'h1; 't1; 'h2; 't2 } =
   bf["union_aux"] `"(" slot{'interval} `"," slot{cons{'h1;'t1}}
      `"," slot{cons{'h2;'t2}} `")"

dform union_interval_df : except_mode[src] ::
   union_interval{ 'interval1; 'interval2 } =
   `"(" slot{'interval1} cup sub{it["interval"]} slot{'interval2} `")"
