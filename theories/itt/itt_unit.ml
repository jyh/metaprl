doc <:doc<
   @module[Itt_unit]

   The @tt{Itt_unit} module defines a term containing exactly
   one element, <<it>>.  The element is the same term that inhabits
   the equality (Section @refmodule[Itt_equal]) and subtype
   (Section @refmodule[Itt_subtype]) judgments.

   @docoff
   ----------------------------------------------------------------

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 1998 Jason Hickey, Cornell University

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

   Author: Jason Hickey
   @email{jyh@cs.caltech.edu}

   @end[license]
>>

doc <:doc<
   @parents
>>
extends Itt_equal
extends Itt_squash
extends Itt_struct
extends Itt_squiggle
doc docoff

extends Itt_grammar

open Lm_debug
open Lm_printf

open Basic_tactics
open Itt_equal
open Itt_struct
open Itt_squash

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_unit%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc terms
declare unit
doc docoff

(*
 * Standard term.
 *)
let unit_term = << unit >>
let unit_opname = opname_of_term unit_term
let is_unit_term = is_no_subterms_term unit_opname

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform unit_df1 : except_mode[src] :: unit = `"Unit"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @rules
   @modsubsection{Typehood and equality}

   The <<unit>> type is a member of every universe, and it
   is also a type.
>>
prim unitEquality {| intro [] |} :
   sequent { <H> >- unit in univ[i:l] } =
   it

(*
 * Is a type.
 *)
interactive unitType {| intro [] |} :
   sequent { <H> >- "type"{unit} }

doc <:doc<
   @modsubsection{Membership}
   The unique inhabitant of the <<unit>> type is the term <<it>>.
>>
prim unit_memberEquality {| intro []; squash |} :
   sequent { <H> >- it in unit } =
   it

doc <:doc<
   @modsubsection{Introduction}

   The <<unit>> type is always provable.  The proof is the unique term
   <<it>>.
>>
interactive unit_memberFormation {| intro [] |} :
   sequent { <H> >- unit }

doc <:doc<
   @modsubsection{Elimination}
   The elimination rule @tt[unitElimination] performs a case analysis
   on $x@colon @unit$.  The witness is replaced with the term <<it>>.
>>
prim unitElimination {| elim [ThinOption thinT] |} 'H :
   ('t['x] : sequent{ <H>; x: unit; <J[it]> >- 'C[it] }) -->
   sequent { <H>; x: unit; <J['x]> >- 'C['x] } =
   't[it]

doc <:doc<
   @modsubsection{Rewriting}
   Two terms in <<unit>> are always computationally equivalent.
>>
prim unitSqequal {| nth_hyp |} :
   sequent { <H> >- 'x = 'y in unit } -->
   sequent { <H> >- 'x ~ 'y } = it

doc docoff

(*
 * H >- Ui ext Unit
 * by unitFormation
 *)
interactive unitFormation :
   sequent { <H> >- univ[i:l] }

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of unit.
 *)
let resource typeinf += (unit_term, infer_univ1)

(*
 * Type of a unit object is unit.
 *)
let resource typeinf += (it_term, Typeinf.infer_const unit_term)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
