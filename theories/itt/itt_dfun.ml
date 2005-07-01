doc <:doc<
   @begin[doc]
   @module[Itt_dfun]

   The @tt[Itt_dfun] module is @emph{derived} from the
   @hrefmodule[Itt_rfun] module.  The type $@fun{x; A; B[x]}$ is
   equivalent to the type $@rfun{f; x; A; B[x]}$, where $f$ is
   not bound in $B[x]$.  The @emph{well-founded} restriction
   for the very-dependent function type is always trivially satisfied
   (since the range type $B[x]$ never invokes $f$).
   The @tt{Itt_dfun} module derives the dependent-function
   rules.
   @end[doc]

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

   Author: Jason Hickey
   @email{jyh@cs.cornell.edu}
   @end[license]
>>

doc <:doc<
   @begin[doc]
   @parents
   @end[doc]
>>
extends Itt_equal
extends Itt_rfun
extends Itt_struct
extends Itt_void
extends Itt_unit
doc docoff

open Lm_debug
open Lm_printf

open Dtactic

open Itt_equal
open Itt_subtype
open Itt_rfun

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_dfun%t"

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @rewrites

   The @tt[unfold_dfun] gives the definition of the dependent-function space.
   @end[doc]
>>
prim_rw unfold_dfun : (x: 'A -> 'B['x]) <--> ({ f | x: 'A -> 'B['x] })

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @rules
   @modsubsection{Lemmas}

   The @tt{void_well_founded} rule is a lemma that is
   useful for proving the well-formedness of the
   dependent-function space.  The @hrefterm[void]
   type is trivially well-founded, since it has no elements.
   @end[doc]
>>
interactive void_well_founded {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- well_founded{'A; a1, a2. void} }

(*
 * @begin[doc]
 * @modsubsection{Typehood and equality}
 *
 * The dependent-function space retains the intensional type
 * equality of the very-dependent type.
 * @end[doc]
 *)
interactive functionEquality {| intro [] |} :
   [wf] sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent { <H>; a1: 'A1 >- 'B1['a1] = 'B2['a1] in univ[i:l] } -->
   sequent { <H> >- (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[i:l] }

(*
 * Typehood.
 *)
interactive functionType {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H>; a: 'A >- "type"{'B['a]} } -->
   sequent { <H> >- "type"{ a:'A -> 'B['a] } }

doc <:doc<
   @begin[doc]
   @modsubsection{Introduction}

   The propositional interpretation of the dependent-function
   is the universal quantification @hrefterm[all], $@all{a; A; B[a]}$.  The
   universal quantification is true, if it is a type,
   and $B[a]$ is true for any $a @in A$.
   @end[doc]
>>
interactive lambdaFormation {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [main] ('b['z] : sequent { <H>; a: 'A >- 'B['a] }) -->
   sequent { <H> >- a:'A -> 'B['a] }

doc <:doc<
   @begin[doc]
   @modsubsection{Membership}

   The dependent function space contains the @hrefterm[lambda] functions.
   @end[doc]
>>
interactive lambdaEquality {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H>; a1: 'A >- 'b1['a1] = 'b2['a1] in 'B['a1] } -->
   sequent { <H> >- lambda{a1. 'b1['a1]} = lambda{a2. 'b2['a2]} in a:'A -> 'B['a] }

doc <:doc<
   @begin[doc]
   @modsubsection{Extensionality}

   The dependent-function retains the extensional membership
   equality of the very-dependent function type.  This rule is
   derived from the @hrefrule[rfunctionExtensionality] rule.
   @end[doc]
>>
interactive functionExtensionality (y:'C -> 'D['y]) (z:'E -> 'F['z]) :
   [main] sequent { <H>; x: 'A >- ('f 'x) = ('g 'x) in 'B['x] } -->
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- 'f in y:'C -> 'D['y] } -->
   [wf] sequent { <H> >- 'g in z:'E -> 'F['z] } -->
   sequent { <H> >- 'f = 'g in x:'A -> 'B['x] }

doc <:doc<
   @begin[doc]
   @modsubsection{Elimination}

   The elimination rule @emph{instantiates} the function
   $f@colon @fun{x; A; B[x]}$ with an argument $a @in A$, to
   obtain a proof of $B[a]$.
   @end[doc]
>>
interactive functionElimination {| elim [] |} 'H 'a :
   [wf] sequent { <H>; f: x:'A -> 'B['x]; <J['f]> >- 'a in 'A } -->
   sequent { <H>; f: x:'A -> 'B['x]; <J['f]>; y: 'B['a]; 'y = ('f 'a) in 'B['a] >- 'T['f] } -->
   sequent { <H>; f: x:'A -> 'B['x]; <J['f]> >- 'T['f] }

doc <:doc<
   @begin[doc]
   @modsubsection{Combinator equality}

   Applications have (at least) an @emph{intensional} equality; they are
   equal if their functions and arguments are equal.
   @end[doc]
>>

interactive applyEquality {| intro[intro_typeinf <<'f1>>] |} (x:'A -> 'B['x]) :
   sequent { <H> >- 'f1 = 'f2 in x:'A -> 'B['x] } -->
   sequent { <H> >- 'a1 = 'a2 in 'A } -->
   sequent { <H> >- ('f1 'a1) = ('f2 'a2) in 'B['a1] }

doc <:doc<
   @begin[doc]
   @modsubsection{Subtyping}

   Function spaces are @emph{contravariant} in the domains, and
   @emph{covariant} in their ranges.  More specifically, the
   ranges must be pointwise covariant.

   @end[doc]
>>
interactive functionSubtype {| intro [] |} :
   ["subtype"] sequent { <H> >- 'A2 subtype 'A1 } -->
   ["subtype"] sequent { <H>; a1: 'A1 >- 'B1['a1] subtype 'B2['a1] } -->
   sequent { <H> >- a1:'A1 -> 'B1['a1]  subtype  a2:'A2 -> 'B2['a2] }
doc docoff

(*
(*
 * H; x: a1:A1 -> B1 <= a2:A2 -> B2; J[x] >- T[x]
 * by function_subtypeElimination i
 *
 * H; x: a1:A1 -> B1 <= a2:A2 -> B2; y: A2 <= A1; z: a:A2 -> B2[a] <= B1[a]; J[x] >- T[x]
 *)
interactive function_subtypeElimination {| elim [] |} 'H 'x 'y 'z 'a :
   ('t['x; 'y; 'z] : sequent { <H>;
             x: \subtype{(a1:'A1 -> 'B1['a1]); (a2:'A2 -> 'B2['a2])};
             <J['x]>;
             y: \subtype{'A2; 'A1};
             z: a:'A2 -> \subtype{'B1['a]; 'B2['a]}
             >- 'T['x]
           }) -->
   sequent { <H>; x: \subtype{(a1:'A1 -> 'B1['a1]); (a2:'A2 -> 'B2['a2])}; <J['x]> >- 'T['x] }
*)

(*
 * H; x: a1:A1 -> B1 = a2:A2 -> B2 in Ui; J[x] >- T[x]
 * by function_equalityElimination
 *
 * H; x: a1:A1 -> B1 = a2:A2 -> B2 in Ui; y: A1 = A2 in Ui; z: a:A1 -> B1[a] = B2[a] in Ui; J[x] >- T[x]
interactive function_equalityElimination {| elim [ThinOption thinT] |} 'H 'x 'y 'z 'a :
   ('t['x; 'y; 'z] : sequent { <H>;
             x: (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[i:l];
             <J['x]>;
             y: 'A1 = 'A2 in univ[i:l];
             z: a:'A1 -> ('B1['a] = 'B2['a] in univ[i:l])
             >- 'T['x]
           }) -->
   sequent { <H>; x: (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[i:l]; <J['x]> >- 'T['x] }
 *)

(*
 * H >- Ui ext a:A -> B
 * by functionFormation a A
 *
 * H >- A = A in Ui
 * H, a: A >- Ui ext B
 *)
interactive functionFormation 'A :
   [wf] sequent { <H> >- 'A in univ[i:l] } -->
   ('B['a] : sequent { <H>; a: 'A >- univ[i:l] }) -->
   sequent { <H> >- univ[i:l] }

(************************************************************************
 * EXTENSIOANLITY                                                       *
 ************************************************************************)

(*
 * Takes two arguments.
 *)
let dfun_extensionalityT = functionExtensionality

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let resource typeinf += (dfun_term, infer_univ_dep0_dep1 dest_dfun)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two function types.
 *)
let resource sub +=
   (DSubtype ([<< a1:'A1 -> 'B1['a1] >>, << a2:'A2 -> 'B2['a2] >>;
               << 'A2 >>, << 'A1 >>;
               << 'B1['a1] >>, << 'B2['a1] >>],
              functionSubtype))

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
