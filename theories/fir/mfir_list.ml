doc <:doc<
   @spelling{th}

   @module[Mfir_list]

   The @tt[Mfir_list] module defines lists and list operations.  Lists
   are used in FIR programs to represent entities whose arity may vary.

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

open Basic_tactics
open Mfir_bool
open Mfir_int


(**************************************************************************
 * Declarations.
 **************************************************************************)

doc <:doc<
   @terms

   The term @tt[nil] is the empty list, and the term @tt[cons] adds a
   term @tt[elt] to the list @tt[tail].  Unless otherwise stated, it
   will be assumed that lists are nil-terminated.
>>

declare nil
declare cons{ 'elt; 'tail }


doc <:doc<

   The term @tt[length] returns the number of elements in a list @tt[l].
>>

declare length{ 'l }


doc <:doc<

   The term @tt[nth_elt] returns the $n$th element of a list @tt[l].
>>

declare nth_elt{ 'n; 'l }


(**************************************************************************
 * Rewrites.
 **************************************************************************)

doc <:doc<
   @rewrites

   Computing the length of a list and the $n$th element of a list
   is straightforward.
>>

prim_rw reduce_length_base {| reduce |} :
   length{ nil } <-->
   0

prim_rw reduce_length_ind {| reduce |} :
   length{ cons{ 'h; 't } } <-->
   ( 1 +@ length{ 't } )

prim_rw reduce_nth_elt_main :
   nth_elt{ number[i:n]; cons{ 'h; 't } } <-->
   ifthenelse{ int_eq{number[i:n]; 0}; 'h; nth_elt{(number[i:n] -@ 1); 't} }

doc <:doc<
   @docoff
>>

let reduce_nth_elt =
   reduce_nth_elt_main thenC
   (addrC [Subterm 1] reduce_int_eq) thenC
   reduce_ifthenelse thenC
   (tryC (addrC [Subterm 1] reduce_sub))

let resource reduce +=
   << nth_elt{ 'n; cons{ 'h; 't } } >>, wrap_reduce reduce_nth_elt

(**************************************************************************
 * Display forms.
 **************************************************************************)

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
   mfir_list_colons{'examined} `"::" slot{'last_elt}

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
   mfir_list_colons{'first_elts} `"::" slot{'last_elt}

(* List operators. *)

dform length_df : except_mode[src] ::
   length{ 'l } =
   bf["length"] `"(" slot{'l} `")"

dform nth_elt_df : except_mode[src] ::
   nth_elt{ 'n; 'l } =
   bf["nth"] `"(" slot{'n} `"," slot{'l} `")"
