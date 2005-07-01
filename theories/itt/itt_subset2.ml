doc <:doc<
   @module[Itt_subset2]

   In this theory we prove some facts about subset relation defines in Section @refmodule[Itt_subset].

   @docoff
   ----------------------------------------------------------------

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.

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

   Author:  Alexei Kopylov @email{kopylov@cs.cornell.edu}

   @end[license]
>>

doc <:doc<
   @parents
>>
extends Itt_subset
extends Itt_set
extends Itt_isect
extends Itt_union
extends Itt_bisect
extends Itt_bunion
extends Itt_ext_equal

doc docoff

open Lm_debug
open Lm_printf

open Dtactic


(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_subset2%t"

doc <:doc<
   @modsection{Sets}
  The subset relation corresponds to set type (Section @refmodule[Itt_set]) in the following way:
  <<'A subset 'B>> if and only if there is a proposition $P: <<'B -> univ[i:l]>>$, such that
  <<ext_equal{'A; {x:'B | 'P['x]}}>>.
>>

interactive set_subset {| intro [] |}  :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H>; x: 'A >- "type"{'P['x]} } -->
   sequent { <H> >- {a: 'A | 'P['a]} subset 'A }

interactive subset_set {| intro [] |}  :
   sequent { <H> >- 'A subset 'B } -->
   sequent { <H> >- ext_equal{{x: 'B | 'x in 'A subset 'B}; 'A} }

interactive subset_iff  :
   [wf] sequent { <H> >- 'A in univ[i:l] } -->
   [wf] sequent { <H> >- 'B in univ[i:l] } -->
   sequent { <H> >- iff{'A subset 'B; exst P:'B -> univ[i:l]. ext_equal{{x:'B| 'P 'x}; 'A}} }

doc <:doc<
 @modsection{Lattice}
  Subsets of a given type forms a lattice with respect to <<space subset space>> relation and intersection and union operations.

  @modsubsection{Order}
  Subset relation forms a partial order on types.
>>

interactive subset_ref {| intro [] |}  :
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- 'A subset 'A }

interactive subset_trans 'B:
   sequent { <H> >- 'A subset 'B } -->
   sequent { <H> >- 'B subset 'C } -->
   sequent { <H> >- 'A subset 'C }

interactive subset_exact:
   sequent { <H> >- 'A subset 'B } -->
   sequent { <H> >- 'B subset 'A } -->
   sequent { <H> >- ext_equal{'A;'B} }

doc <:doc<
   @modsubsection{Union and Intersection}
   Although intersection and union on types do not behave as set-theoretic union and intersection,
   they works exactly as set-theoretic union and intersection on @em{subsets} of a given type.

   Intersection of @emph{non-empty} family of subsets of a given type is subset of this type.
>>

interactive subset_isect {| intro[AutoMustComplete] |}:
   sequent { <H> >-'I } -->
   sequent { <H>; i: 'I >- 'A['i] subset 'T } -->
   sequent { <H> >- Isect i:'I. 'A['i] subset 'T }

interactive subset_bisect {| intro[AutoMustComplete] |}:
   sequent { <H> >-'A subset 'T} -->
   sequent { <H> >-'B subset 'T} -->
   sequent { <H> >- 'A isect 'B subset 'T }

doc <:doc<
   Note that if only one of types is subset of $T$ then it does not mean that their intersection is subset of $T$.
>>

interactive counterexample2 :
   sequent { <H> >- not{(bool isect top subset top)} }

doc <:doc<

   Union of a family of subsets of a given type is subset of this type.
>>

interactive subset_union {| intro[] |}:
   sequent { <H> >-"type"{'I} } -->
   sequent { <H>; i: 'I >- 'A['i] subset 'T } -->
   sequent { <H> >- Union i:'I. 'A['i] subset 'T }

interactive subset_bunion {| intro[] |}:
   sequent { <H> >-'A subset 'T}  -->
   sequent { <H> >-'B subset 'T}  -->
   sequent { <H> >- 'A bunion 'B subset 'T }

doc <:doc<
   @modsection{Monotonicity}
    Most of the type constructors are monotone with respect to <<space subset space>>.
>>

interactive prod_subset {| intro [] |} :
   sequent { <H> >- 'A subset '"A'" } -->
   sequent { <H> >- 'B subset '"B'" } -->
   sequent { <H> >- 'A * 'B subset '"A'" * '"B'" }

interactive union_subset {| intro [] |} :
   sequent { <H> >- 'A subset '"A'" } -->
   sequent { <H> >- 'B subset '"B'" } -->
   sequent { <H> >- 'A + 'B subset '"A'" + '"B'" }

doc docoff


(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
