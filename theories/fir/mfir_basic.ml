(*!
 * @begin[doc]
 * @module[Mfir_basic]
 *
 * The @tt{Mfir_basic} module declares basic terms needed to
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
extends Mfir_comment

(**************************************************************************
 * Declarations.
 **************************************************************************)

(*!
 * @begin[doc]
 * @terms
 * @modsubsection{Integers}
 *
 * The term @tt{number@[i:n@]} represents the integer $i$.
 * @end[doc]
 *)

declare number[i:n]

(*!
 * @begin[doc]
 * @modsubsection{Lists}
 *
 * Lists are used in the FIR to encode entities whose arities may vary.  The
 * term @tt{nil} is the empty list, and the term @tt{cons} adds a term
 * @tt{elt} to the list @tt{tail}.
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
 * The term @tt{interval} represents a closed interval.  The term @tt{intset}
 * consists of a list of intervals.  In this case, the end points of each
 * interval are interpreted as signed, 31-bit integers.  The term
 * @tt{rawintset} is similar, except the end points of each interval are
 * interpreted as integers with the specified precision and signedness (see
 * @hrefterm[tyRawInt]).
 * @end[doc]
 *)

declare interval[left:n, right:n]
declare intset{ 'interval_list }
declare rawintset[precision:n, sign:s]{ 'interval_list }

(*!
 * @docoff
 *)

(**************************************************************************
 * Display forms.
 **************************************************************************)

(*
 * Integers.
 *)

dform number_df :
   number[i:n] =
   slot[i:n]

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
   interval[left:n, right:n] =
   `"[" slot[left:n] `"," slot[right:n] `"]"

dform intset_df : except_mode[src] ::
   intset{ 'interval_list } =
   mfir_bf["intset":s] `" " slot{'interval_list}

dform rawintset_df : except_mode[src] ::
   rawintset[precision:n, sign:s]{ 'interval_list } =
   mfir_bf["intset":s] sub{slot[precision:n]} sup{slot[sign:s]} `" "
      slot{'interval_list}
