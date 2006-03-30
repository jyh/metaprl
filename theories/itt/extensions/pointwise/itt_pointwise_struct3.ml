doc <:doc<
   @module[Itt_struct3]

   The @tt[Itt_struct3] module contains some @emph{derived} rules that
   are true under both pointwise and pairwise functionality semantics for
   sequents, but require different proofs under the two.

   @docoff
   ----------------------------------------------------------------

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2001-2006 MetaPRL Group, Cornell University and
   California Institute of Technology

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

   Author: Alexei Kopylov @email{kopylov@cs.caltech.edu}
   Modified by: Aleksey Nogin @email{nogin@cs.caltech.edu}

   @end[license]
>>

doc <:doc<
   @parents
>>
extends Itt_squash
extends Itt_ext_equal
extends Itt_struct2
extends Itt_subtype
extends Itt_pointwise

doc docoff

open Basic_tactics

open Itt_struct
open Itt_ext_equal

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(* This rule is valid both in pointwise and pairwise functionality, but the proof of this rule is
 * difirent for these functionalities
 *)

doc <:doc< @rules >>

interactive substUsingEpimorphism 'H 'B bind{y. 'f['y]} bind{x. 'g['x]}  : (* g does not depend on J *)
   [wf] sequent { <H>; x: 'A; <J['x]>; y: 'B >- 'f['y] in 'A } -->
   [wf] sequent { <H>; x: 'A; <J['x]> >-  'g['x] in 'B } -->
   [equality] sequent { <H>; x: 'A; <J['x]> >- 'f['g['x]] ~ 'x } -->
   [main] sequent { <H>; y: 'B; <J['f['y]]> >- 'C['f['y]] } -->
   sequent { <H>; x: 'A; <J['x]> >- 'C['x] }

interactive hypReplacementStrong 'H 'B :
   [assertion] sequent { <H>; x: 'A; <J['x]>; y: 'B >- 'y in 'A } -->
   [assertion] sequent { <H>; x: 'A; <J['x]> >-  'x in 'B } -->
   [main] sequent { <H>; x: 'B; <J['x]> >- 'C['x] } -->
   sequent { <H>; x: 'A; <J['x]> >- 'C['x] }

interactive hypReplacementExt 'H 'B  :
   [equality] sequent { <H>; x: 'A; <J['x]> >- ext_equal{'A;'B} } -->
   [main]  sequent { <H>; x: 'B; <J['x]> >- 'T['x] } -->
   sequent { <H>; x: 'A; <J['x]> >- 'T['x] }

doc docoff

let changeHypT t i =
   hypReplacementStrong i t

let replaceHypT t i = funT (fun p ->
   match get_univ_arg p with
      Some univ -> hypReplacement i t univ
    | None -> hypReplacementExt i t)

let replaceWithHypT j i = funT (fun p ->
   let s, t = dest_ext_equal (Sequent.nth_hyp p j) in
	hypReplacementExt i t)

let replaceWithRevHypT j i = funT (fun p ->
   let s, t = dest_ext_equal (Sequent.nth_hyp p j) in
	hypReplacementExt i s)
