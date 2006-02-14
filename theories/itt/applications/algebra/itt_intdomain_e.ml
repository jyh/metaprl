doc <:doc<
   @module[Itt_intdomain_e]

   This theory defines integral domains with decidable equality.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2004-2006 MetaPRL Group

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

doc <:doc< @parents >>
extends Itt_intdomain
extends Itt_ring_uce
extends Itt_labels
doc docoff
extends Itt_poly

open Lm_debug
open Lm_printf

open Basic_tactics

open Itt_intdomain
open Itt_ring_uce
open Itt_ring_e

let _ =
   show_loading "Loading Itt_intdomain_e%t"

(************************************************************************
 * Commutative intDomain with Decidable Equality                             *
 ************************************************************************)
doc <:doc<
   @modsection{Commutative integral domain with decidable equality}
   @modsubsection{Rewrites}

>>
define unfold_isIntDomainE1 : isIntDomainE{'f} <-->
   isIntDomain{'f} & eqDecidable{'f}

define unfold_intDomainE1 : intDomainE[i:l] <-->
   {f: preunitringE[i:l] | isIntDomainE{'f}}
doc docoff

let unfold_isIntDomainE = unfold_isIntDomainE1 thenC addrC [Subterm 1] unfold_isIntDomain thenC addrC [Subterm 2] unfold_eqDecidable
let unfold_intDomainE = unfold_intDomainE1 thenC addrC [Subterm 1] unfold_preunitringE thenC addrC [Subterm 2] unfold_isIntDomainE

let fold_isIntDomainE1 = makeFoldC << isIntDomainE{'f} >> unfold_isIntDomainE1
let fold_isIntDomainE = makeFoldC << isIntDomainE{'f} >> unfold_isIntDomainE
let fold_intDomainE1 = makeFoldC << intDomainE[i:l] >> unfold_intDomainE1
let fold_intDomainE = makeFoldC << intDomainE[i:l] >> unfold_intDomainE

let intDomainEDT n = rw unfold_intDomainE n thenT dT n

let resource elim +=
   [<<intDomainE[i:l]>>, wrap_elim intDomainEDT]

doc <:doc<
   @modsubsection{Well-formedness}

>>
interactive isIntDomainE_wf {| intro [] |} :
   [wf] sequent { <H> >- isIntDomain{'f} Type } -->
   [wf] sequent { <H> >- isCommutative{'f} Type } -->
   [wf] sequent { <H> >- eqDecidable{'f} Type } -->
   sequent { <H> >- isIntDomainE{'f} Type }

interactive intDomainE_wf {| intro [] |} :
   sequent { <H> >- intDomainE[i:l] Type }

doc <:doc<
   @modsubsection{Introduction and Elimination}

>>
interactive isIntDomainE_intro {| intro [AutoMustComplete] |} :
   sequent { <H> >- isIntDomain{'f} } -->
   sequent { <H> >- eqDecidable{'f} } -->
   sequent { <H> >- isIntDomainE{'f} }

interactive isIntDomainE_elim1 {| elim [] |} 'H :
   sequent { <H>; u: isIntDomainE{'f}; x: isIntDomain{'f}; y: eqDecidable{'f}; <J['u]> >- 'C['u] } -->
   sequent { <H>; u: isIntDomainE{'f}; <J['u]> >- 'C['u] }

interactive isIntDomainE_elim {| elim [] |} 'H :
   sequent { <H>; u: isIntDomainE{'f};
      u1: all x: 'f^car. all y: 'f^car. all z: 'f^car. (('x *['f] 'y) *['f] 'z = 'x *['f] ('y *['f] 'z) in 'f^car);
      u2: all x: 'f^car. all y: 'f^car. all z: 'f^car. (('x +['f] 'y) +['f] 'z = 'x +['f] ('y +['f] 'z) in 'f^car);
      v2: all x: 'f^car. ('f^"0" +['f] 'x = 'x in 'f^car);
      w2: all x: 'f^car. ('f^neg 'x) +['f] 'x = 'f^"0" in 'f^car;
      u3: all x: 'f^car. all y: 'f^car. ('x +['f] 'y = 'y +['f] 'x in 'f^car);
      u4: all x: 'f^car. all y: 'f^car. all z: 'f^car. (('x +['f] 'y) *['f] 'z = ('x *['f] 'z) +['f] ('y *['f] 'z) in 'f^car);
      u5: all x: 'f^car. all y: 'f^car. all z: 'f^car. ('x *['f] ('y +['f] 'z) = ('x *['f] 'y) +['f] ('x *['f] 'z) in 'f^car);
      u6: all x: 'f^car. (('f^"1" *['f] 'x = 'x in 'f^car) & ('x *['f] 'f^"1" = 'x in 'f^car));
      u7: all x: 'f^car. all y: 'f^car. ('x *['f] 'y = 'y *['f] 'x in 'f^car);
      u8: 'f^"0" <> 'f^"1" in 'f^car;
      u9: all a: 'f^car. all b: 'f^car. ('a <> 'f^"0" in 'f^car & 'b <> 'f^"0" in 'f^car & 'a *['f] 'b = 'f^"0" in 'f^car => "false");
      u10: all x: 'f^car. all y: 'f^car. "iff"{'x = 'y in 'f^car; "assert"{'f^eq 'x 'y}};
      <J['u]> >- 'C['u] } -->
   sequent { <H>; u: isIntDomainE{'f}; <J['u]> >- 'C['u] }

interactive intDomainE_intro {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'f in preunitringE[i:l] } -->
   [main] sequent { <H> >- isIntDomainE{'f} } -->
   sequent { <H> >- 'f in intDomainE[i:l] }

interactive intDomainE_equality {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'A = 'B in preunitringE[i:l] } -->
   [main] sequent { <H> >- isIntDomainE{'A} } -->
   sequent { <H> >- 'A = 'B in intDomainE[i:l] }

interactive intDomainE_elim1 {| elim [] |} 'H :
   sequent { <H>; f: preunitringE[i:l]; u: isIntDomainE{'f}; <J['f]> >- 'C['f] } -->
   sequent { <H>; f: intDomainE[i:l]; <J['f]> >- 'C['f] }

interactive intDomainE_elim {| elim [] |} 'H :
   sequent { <H>;
       f: {car: univ[i:l]; "*": ^car -> ^car -> ^car; "+": ^car -> ^car -> ^car; "0": ^car; neg: ^car -> ^car; "1": ^car; "eq": ^car -> ^car -> bool};
      u1: all x: 'f^car. all y: 'f^car. all z: 'f^car. (('x *['f] 'y) *['f] 'z = 'x *['f] ('y *['f] 'z) in 'f^car);
      u2: all x: 'f^car. all y: 'f^car. all z: 'f^car. (('x +['f] 'y) +['f] 'z = 'x +['f] ('y +['f] 'z) in 'f^car);
      v2: all x: 'f^car. ('f^"0" +['f] 'x = 'x in 'f^car);
      w2: all x: 'f^car. ('f^neg 'x) +['f] 'x = 'f^"0" in 'f^car;
      u3: all x: 'f^car. all y: 'f^car. ('x +['f] 'y = 'y +['f] 'x in 'f^car);
      u4: all x: 'f^car. all y: 'f^car. all z: 'f^car. (('x +['f] 'y) *['f] 'z = ('x *['f] 'z) +['f] ('y *['f] 'z) in 'f^car);
      u5: all x: 'f^car. all y: 'f^car. all z: 'f^car. ('x *['f] ('y +['f] 'z) = ('x *['f] 'y) +['f] ('x *['f] 'z) in 'f^car);
      u6: all x: 'f^car. (('f^"1" *['f] 'x = 'x in 'f^car) & ('x *['f] 'f^"1" = 'x in 'f^car));
      u7: all x: 'f^car. all y: 'f^car. ('x *['f] 'y = 'y *['f] 'x in 'f^car);
      u8: 'f^"0" <> 'f^"1" in 'f^car;
      u9: all a: 'f^car. all b: 'f^car. ('a <> 'f^"0" in 'f^car & 'b <> 'f^"0" in 'f^car & 'a *['f] 'b = 'f^"0" in 'f^car => "false");
      u10: all x: 'f^car. all y: 'f^car. "iff"{'x = 'y in 'f^car; "assert"{'f^eq 'x 'y}};
      <J['f]> >- 'C['f] } -->
   sequent { <H>; f: intDomainE[i:l]; <J['f]> >- 'C['f] }
doc docoff

(************************************************************************
 * Polynomials                                                          *
 ************************************************************************)
doc <:doc<
   @modsection{Polynomial ring}

>>
interactive poly_intdomain {| intro []; nth_hyp |} :
   [wf] sequent { <H> >- 'F in intDomainE[i:l] } -->
   sequent { <H> >- poly_ring{'F} in intDomainE[i:l] }
doc docoff

(************************************************************************
 * DISPLAY FOfMS                                                        *
 ************************************************************************)

dform intDomainE_df1 : except_mode[src] :: except_mode[prl] :: intDomainE[i:l] =
   mathbbU `"nitringE" sub{slot[i:l]}

dform intDomainE_df2 : mode[prl] :: intDomainE[i:l] =
   `"IntDomainE[" slot[i:l] `"]"

dform isIntDomainE_df : except_mode[src] :: isIntDomainE{'F} =
   `"isIntDomainE(" slot{'F} `")"

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
