doc <:doc<
   @begin[doc]
   @module[Itt_ring_e]

   This theory defines rings with decidable equality.
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
extends Itt_ring2
doc docoff

open Lm_debug
open Lm_printf

open Basic_tactics

open Itt_ring2
open Itt_equal

let _ =
   show_loading "Loading Itt_ring_e%t"

(************************************************************************
 * Decidable Equality                                                   *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @modsection{Decidable Equality}
   @modsubsection{Rewrites}

   @end[doc]
>>
define unfold_eqDecidable : eqDecidable{'f} <-->
   all x: 'f^car. all y: 'f^car. "iff"{'x = 'y in 'f^car; "assert"{'f^eq 'x 'y}}
doc docoff

let fold_eqDecidable = makeFoldC << eqDecidable{'f} >> unfold_eqDecidable

(* Rules about eqDecidable *)
doc <:doc<
   @begin[doc]
   @modsection{Well-formedness, Introduction, Elimination}
   @modsubsection{Rewrites}

   @end[doc]
>>
interactive eqDecidable_wf {| intro [] |} :
   [wf] sequent { <H> >- 'f^car Type } -->
   [wf] sequent { <H>; x: 'f^car; y: 'f^car >- 'f^eq 'x 'y in bool } -->
   sequent { <H> >- eqDecidable{'f} Type }

interactive eqDecidable_intro {| intro [] |} :
   [wf] sequent { <H> >- 'f^car Type } -->
   [wf] sequent { <H>; x: 'f^car; y: 'f^car >- 'f^eq 'x 'y in bool } -->
   sequent { <H>; x: 'f^car; y: 'f^car; 'x = 'y in 'f^car >- "assert"{'f^eq 'x 'y} } -->
  [wf] sequent { <H>; x: 'f^car; y: 'f^car; "assert"{'f^eq 'x 'y} >- 'x = 'y in 'f^car } -->
   sequent { <H> >- eqDecidable{'f} }

interactive eqDecidable_elim {| elim [] |} 'H :
   sequent { <H>; u: all x: 'f^car. all y: 'f^car. "iff"{'x = 'y in 'f^car; "assert"{'f^eq 'x 'y}}; <J['u]> >- 'C['u] } -->
   sequent { <H>; u: eqDecidable{'f}; <J['u]> >- 'C['u] }
doc docoff

(************************************************************************
 * Ring with Decidable Equality                                        *
 ************************************************************************)
doc <:doc<
   @begin[doc]
   @modsection{Ring with decidable equality}
   @modsubsection{Rewrites}

   @end[doc]
>>
define unfold_preringE1 : preringE[i:l] <-->
   record["eq":t]{r. ('r^car -> 'r^car -> bool); prering[i:l]}

define unfold_isRingE1 : isRingE{'f} <-->
   isRing{'f} & eqDecidable{'f}

define unfold_ringE1 : ringE[i:l] <-->
   {f: preringE[i:l] | isRingE{'f}}
doc docoff

let unfold_preringE = unfold_preringE1 thenC addrC [Subterm 2] unfold_prering
let unfold_isRingE = unfold_isRingE1 thenC addrC [Subterm 1] unfold_isRing thenC addrC [Subterm 2] unfold_eqDecidable
let unfold_ringE = unfold_ringE1 thenC addrC [Subterm 1] unfold_preringE thenC addrC [Subterm 2] unfold_isRingE

let fold_preringE1 = makeFoldC << preringE[i:l] >> unfold_preringE1
let fold_preringE = makeFoldC << preringE[i:l] >> unfold_preringE
let fold_isRingE1 = makeFoldC << isRingE{'f} >> unfold_isRingE1
let fold_isRingE = makeFoldC << isRingE{'f} >> unfold_isRingE
let fold_ringE1 = makeFoldC << ringE[i:l] >> unfold_ringE1
let fold_ringE = makeFoldC << ringE[i:l] >> unfold_ringE

let ringEDT n = rw unfold_ringE n thenT dT n

let resource elim +=
   [<<ringE[i:l]>>, ringEDT]

doc <:doc<
   @begin[doc]
   @modsubsection{Well-formedness}

   @end[doc]
>>
interactive preringE_wf {| intro [] |} :
   sequent { <H> >- preringE[i:l] Type }

interactive isRingE_wf {| intro [] |} :
   [wf] sequent { <H> >- isRing{'f} Type } -->
   [wf] sequent { <H> >- eqDecidable{'f} Type } -->
   sequent { <H> >- isRingE{'f} Type }

interactive ringE_wf {| intro [] |} :
   sequent { <H> >- ringE[i:l] Type }

doc <:doc<
   @begin[doc]
   @modsubsection{Introduction and Elimination}

   @end[doc]
>>
interactive preringE_intro {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'f in prering[i:l] } -->
   [wf] sequent { <H> >- 'f in {"eq": 'f^car -> 'f^car -> bool} } -->
   sequent { <H> >- 'f in preringE[i:l] }

interactive preringE_equality {| intro [complete_unless_member] |} :
   [wf] sequent { <H> >- 'A = 'B in prering[i:l] } -->
   [wf] sequent { <H> >- 'A = 'B in {"eq": 'A^car -> 'A^car -> bool} } -->
   sequent { <H> >- 'A = 'B in preringE[i:l] }

interactive preringE_elim {| elim [] |} 'H :
   sequent { <H>; f: prering[i:l]; x: 'f^car -> 'f^car -> bool; <J['f^eq:='x]> >- 'C['f^eq:='x] } -->
   sequent { <H>; f: preringE[i:l]; <J['f]> >- 'C['f] }
doc docoff

interactive car_preringE_wf {| intro [AutoMustComplete; intro_typeinf <<'f>>] |} preringE[i:l] :
   [wf] sequent { <H> >- 'f in preringE[i:l] } -->
   sequent { <H> >- 'f^car Type }

doc docon
interactive isRingE_intro {| intro [AutoMustComplete] |} :
   sequent { <H> >- isRing{'f} } -->
   sequent { <H> >- eqDecidable{'f} } -->
   sequent { <H> >- isRingE{'f} }

interactive isRingE_elim1 {| elim [] |} 'H :
   sequent { <H>; x: isRing{'f}; y: eqDecidable{'f}; <J['x, 'y]> >- 'C['x, 'y] } -->
   sequent { <H>; u: isRingE{'f}; <J['u]> >- 'C['u] }

interactive isRingE_elim2 {| elim [] |} 'H :
   sequent { <H>; x: isRing{'f}; y: all x: 'f^car. all y: 'f^car. "iff"{'x = 'y in 'f^car; "assert"{'f^eq 'x 'y}}; <J['x, 'y]> >- 'C['x, 'y] } -->
   sequent { <H>; u: isRingE{'f}; <J['u]> >- 'C['u] }

interactive ringE_intro {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'f in preringE[i:l] } -->
   [main] sequent { <H> >- isRingE{'f} } -->
   sequent { <H> >- 'f in ringE[i:l] }

interactive ringE_intro1 {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'f in ring[i:l] } -->
   [wf] sequent { <H> >- 'f in {"eq": 'f^car -> 'f^car -> bool} } -->
   sequent { <H> >- eqDecidable{'f} } -->
   sequent { <H> >- 'f in ringE[i:l] }

interactive ringE_equality {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'A = 'B in preringE[i:l] } -->
   [main] sequent { <H> >- isRingE{'A} } -->
   sequent { <H> >- 'A = 'B in ringE[i:l] }

interactive ringE_elim1 {| elim [] |} 'H :
   sequent { <H>; f: preringE[i:l]; u: isRingE{'f}; <J['f]> >- 'C['f] } -->
   sequent { <H>; f: ringE[i:l]; <J['f]> >- 'C['f] }
doc docoff

(************************************************************************
 * DISPLAY FOfMS                                                        *
 ************************************************************************)

dform eqDecidable_df : except_mode[src] :: eqDecidable{'F} =
   `"eqDecidable(" slot{'F} `")"

dform eq_df1 : except_mode[src] :: except_mode[prl] :: parens :: ('F^eq 'a 'b)
 =
   slot["le"]{'a} `"=" sub{'F} slot["le"]{'b}

dform eq_df2 : mode[prl] :: parens :: ('F^eq 'a 'b) =
   slot["le"]{'a} `" " slot{'F} `".eq " slot["le"]{'b}

dform ringE_df1 : except_mode[src] :: except_mode[prl] :: ringE[i:l] =
   mathbbR `"ingE" sub{slot[i:l]}

dform ringE_df2 : mode[prl] :: ringE[i:l] =
   `"RingE[" slot[i:l] `"]"

dform preringE_df1 : except_mode[src] :: except_mode[prl] :: preringE[i:l] =
   `"preringE" sub{slot[i:l]}

dform preringE_df2 : mode[prl] :: preringE[i:l] =
   `"preringE[" slot[i:l] `"]"

dform isRingE_df : except_mode[src] :: isRingE{'F} =
   `"isRingE(" slot{'F} `")"

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
