doc <:doc<
   @begin[doc]
   @module[Itt_field_e]

   This theory defines fields with decidable equality.
   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.

   Copyright (C) 1997-2004 MetaPRL Group

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

   Author: Xin Yu @email{xiny@cs.caltech.edu}
   @end[license]
>>

doc <:doc< @doc{@parents} >>
extends Itt_field2
extends Itt_intdomain_e
doc docoff
extends Itt_poly

open Lm_debug
open Lm_printf
open Tactic_type.Tacticals
open Dtactic
open Top_conversionals

open Itt_field2
open Itt_ring_e
open Itt_equal

let _ =
   show_loading "Loading Itt_field_e%t"

(************************************************************************
 * Field with Decidable Equality                                        *
 ************************************************************************)
doc <:doc<
   @begin[doc]
   @modsection{Field with decidable equality}
   @modsubsection{Rewrites}

   @end[doc]
>>
define unfold_prefieldE1 : prefieldE[i:l] <-->
   record["eq":t]{r. ('r^car -> 'r^car -> bool); prefield[i:l]}

define unfold_isFieldE1 : isFieldE{'f} <-->
   isField{'f} & eqDecidable{'f}

define unfold_fieldE1 : fieldE[i:l] <-->
   {f: prefieldE[i:l] | isFieldE{'f}}
doc docoff

let unfold_prefieldE = unfold_prefieldE1 thenC addrC [1] unfold_prefield
let unfold_isFieldE = unfold_isFieldE1 thenC addrC [0] unfold_isField thenC addrC [1] unfold_eqDecidable
let unfold_fieldE = unfold_fieldE1 thenC addrC [0] unfold_prefieldE thenC addrC [1] unfold_isFieldE

let fold_prefieldE1 = makeFoldC << prefieldE[i:l] >> unfold_prefieldE1
let fold_prefieldE = makeFoldC << prefieldE[i:l] >> unfold_prefieldE
let fold_isFieldE1 = makeFoldC << isFieldE{'f} >> unfold_isFieldE1
let fold_isFieldE = makeFoldC << isFieldE{'f} >> unfold_isFieldE
let fold_fieldE1 = makeFoldC << fieldE[i:l] >> unfold_fieldE1
let fold_fieldE = makeFoldC << fieldE[i:l] >> unfold_fieldE

let fieldEDT n = rw unfold_fieldE n thenT dT n

let resource elim +=
   [<<fieldE[i:l]>>, fieldEDT]

doc <:doc<
   @begin[doc]
   @modsubsection{Well-formedness}

   @end[doc]
>>
interactive prefieldE_wf {| intro [] |} :
   sequent { <H> >- prefieldE[i:l] Type }

interactive isFieldE_wf {| intro [] |} :
   sequent { <H> >- isField{'f} Type } -->
   sequent { <H> >- eqDecidable{'f} Type } -->
   sequent { <H> >- isFieldE{'f} Type }

interactive fieldE_wf {| intro [] |} :
   sequent { <H> >- fieldE[i:l] Type }

doc <:doc<
   @begin[doc]
   @modsubsection{Introduction and Elimination}

   @end[doc]
>>
interactive prefieldE_intro {| intro [AutoMustComplete] |} :
   sequent { <H> >- 'f in prefield[i:l] } -->
   sequent { <H> >- 'f in {"eq": 'f^car -> 'f^car -> bool} } -->
   sequent { <H> >- 'f in prefieldE[i:l] }

interactive prefieldE_equality {| intro [complete_unless_member] |} :
   sequent { <H> >- 'A = 'B in prefield[i:l] } -->
   sequent { <H> >- 'A = 'B in {"eq": 'A^car -> 'A^car -> bool} } -->
   sequent { <H> >- 'A = 'B in prefieldE[i:l] }

interactive prefieldE_elim {| elim [] |} 'H :
   sequent { <H>; f: prefield[i:l]; x: 'f^car -> 'f^car -> bool; <J['f^eq:='x]> >- 'C['f^eq:='x] } -->
   sequent { <H>; f: prefieldE[i:l]; <J['f]> >- 'C['f] }
doc docoff

interactive car_prefieldE_wf {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} prefieldE[i:l] :
   sequent { <H> >- 'f in prefieldE[i:l] } -->
   sequent { <H> >- 'f^car Type }

doc <:doc< @doc{ } >>
interactive isFieldE_intro {| intro [AutoMustComplete] |} :
   sequent { <H> >- isField{'f} } -->
   sequent { <H> >- eqDecidable{'f} } -->
   sequent { <H> >- isFieldE{'f} }

interactive isFieldE_elim1 {| elim [] |} 'H :
   sequent { <H>; x: isField{'f}; y: eqDecidable{'f}; <J['x, 'y]> >- 'C['x, 'y] } -->
   sequent { <H>; u: isFieldE{'f}; <J['u]> >- 'C['u] }

interactive isFieldE_elim2 {| elim [] |} 'H :
   sequent { <H>; x: isField{'f}; y: all x: 'f^car. all y: 'f^car. "iff"{'x = 'y in 'f^car; "assert"{'f^eq 'x 'y}}; <J['x, 'y]> >- 'C['x, 'y] } -->
   sequent { <H>; u: isFieldE{'f}; <J['u]> >- 'C['u] }

interactive fieldE_intro {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'f in prefieldE[i:l] } -->
   [main] sequent { <H> >- isFieldE{'f} } -->
   sequent { <H> >- 'f in fieldE[i:l] }

interactive fieldE_intro1 {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'f in field[i:l] } -->
   sequent { <H> >- 'f in {"eq": 'f^car -> 'f^car -> bool} } -->
   sequent { <H> >- eqDecidable{'f} } -->
   sequent { <H> >- 'f in fieldE[i:l] }

interactive fieldE_equality {| intro [AutoMustComplete] |} :
   sequent { <H> >- 'A = 'B in prefieldE[i:l] } -->
   [main] sequent { <H> >- isFieldE{'A} } -->
   sequent { <H> >- 'A = 'B in fieldE[i:l] }

interactive fieldE_elim1 {| elim [] |} 'H :
   sequent { <H>; f: prefieldE[i:l]; u: isFieldE{'f}; <J['f]> >- 'C['f] } -->
   sequent { <H>; f: fieldE[i:l]; <J['f]> >- 'C['f] }
doc docoff

(************************************************************************
 * Polynomials                                                          *
 ************************************************************************)
doc <:doc<
   @begin[doc]
   @modsection{Polynomial ring}

   @end[doc]
>>
interactive poly_field {| intro [] |} :
   [wf] sequent { <H> >- 'F in fieldE[i:l] } -->
   sequent { <H> >- poly_ring{'F} in intDomainE[i:l] }


(************************************************************************
 * DISPLAY FOfMS                                                        *
 ************************************************************************)

dform fieldE_df1 : except_mode[src] :: except_mode[prl] :: fieldE[i:l] =
   mathbbF `"ieldE" sub{slot[i:l]}

dform fieldE_df2 : mode[prl] :: fieldE[i:l] =
   `"FieldE[" slot[i:l] `"]"

dform prefieldE_df1 : except_mode[src] :: except_mode[prl] :: prefieldE[i:l] =
   `"prefieldE" sub{slot[i:l]}

dform prefieldE_df2 : mode[prl] :: prefieldE[i:l] =
   `"prefieldE[" slot[i:l] `"]"

dform isFieldE_df : except_mode[src] :: isFieldE{'F} =
   `"isFieldE(" slot{'F} `")"

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
