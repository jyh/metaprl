doc <:doc<
   @spelling{tunion}

   @begin[doc]
   @module[Itt_tunion]

   The @tt{Itt_tunion} module defines a (joint) union type
   $@tunion{x; A; B[x]}$.  The elements of the union are the
   elements of any of the types $B[x]$ for any $x @in A$.

   The membership equality is the @emph{the transitive closure of union}
   of the equalities
   in each of the cases $B[x]$.  That is, two elements are equal
   in the union if they are equal in @emph{any} of the cases.  This
   may be surprising.  For example, the type
   $$@tunion{T; @univ{i}; T @rightarrow T}$$
   may seem to contain all of the polymorphic functions
   with type $T @rightarrow T$, for any $T @in @univ{i}$.
   It does--but the union also contains the type case
   <<void -> void>>, in which all functions are equal.
   As a consequence, the union space also has the trivial
   equality, and thus it has no useful elimination form.
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
extends Itt_struct
extends Itt_struct2
extends Itt_equal
extends Itt_set
extends Itt_logic
doc <:doc< @docoff >>

open Refiner.Refiner.Term
open Refiner.Refiner.TermOp

open Dtactic
open Tactic_type.Tacticals

open Itt_struct
open Itt_equal

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @terms

   The @tt{tunion} term defines the union type.
   @end[doc]
>>

declare tunion{'A; x. 'B['x]}
doc <:doc< @docoff >>

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_tunion

dform isect_df : except_mode[src] :: parens :: "prec"[prec_tunion] :: tunion{'A; x. 'B} =
   cup slot{'x} `":" slot{'A} `"." slot{'B}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Proof of Ui
 *)
prim tunionFormation 'A :
   [wf] sequent { <H> >- 'A = 'A in univ[i:l] } -->
   ('B['x] : sequent { <H>; x: 'A >- univ[i:l] }) -->
   sequent { <H> >- univ[i:l] } =
   tunion{'A; x. 'B['x]}

doc <:doc<
   @begin[doc]
   @rules
   @modsubsection{Typehood and equality}

   The union type $@tunion{x; A; B[x]}$ is well-formed if $A$ is
   a type, and $B[a]$ is a type for any $a @in A$.
   @end[doc]
>>
prim tunionEquality {| intro [] |} :
   [wf] sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent { <H>; x: 'A1 >- 'B1['x] = 'B2['x] in univ[i:l] } -->
   sequent { <H> >- tunion{'A1; x1. 'B1['x1]} = tunion{'A2; x2. 'B2['x2] } in univ[i:l] } =
   it

prim tunionType {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H>; y: 'A >- "type"{'B['y]} } -->
   sequent { <H> >- "type"{.Union x:'A. 'B['x] } } =
   it

doc <:doc<
   @begin[doc]
   @modsubsection{Membership}

   The elements $t$ of the union type are the elements in
   any one of the branches $t @in B[a]$ for any $a @in A$.
   Two elements are equal if they are equal in @emph{any}
   of the branches $B[a]$.
   @end[doc]
>>
prim tunionMemberEquality {| intro [] |} 'a :
   [wf] sequent { <H> >- 'a = 'a in 'A } -->
   [wf] sequent { <H>; y: 'A >- "type"{'B['y]} } -->
   [wf] sequent { <H> >- 'x1 = 'x2 in 'B['a] } -->
   sequent { <H> >- 'x1 = 'x2 in Union x:'A. 'B['x]  } =
   it

doc <:doc<
   @begin[doc]
   @modsubsection{Introduction}

   The propositional interpretation of the union type
   is similar to the existential $@exists{x; A; B[x]}$.
   The union is inhabited if-and-only-if the existential
   is also inhabited.
   @end[doc]
>>
prim tunionMemberFormation {| intro [] |} 'a :
   [wf] sequent { <H> >- 'a = 'a in 'A } -->
   [wf] sequent { <H>; y: 'A >- "type"{'B['y]} } -->
   [main] ('t : sequent { <H> >- 'B['a] }) -->
   sequent { <H> >- Union x:'A. 'B['x]  } =
   't

doc <:doc<
   @begin[doc]
   @modsubsection{Elimination}

   The elimination form is weak.  The desired rule would be that if
   $x@colon @tunion{y; A; B[y]}$, then $x @in B[a]$ for some
   $a @in A$.  This rule is allowed, but only for equality goals,
   where the computational content of the proof can be omitted.
   @end[doc]
>>
prim tunionElimination {| elim [ThinOption thinT] |} 'H :
   sequent { <H>; x: tunion{'A; y. 'B['y]}; <J['x]>; w: 'A; z: 'B['w] >- 't1['z] = 't2['z] in 'C['z] } -->
   sequent { <H>; x: tunion{'A; y. 'B['y]}; <J['x]> >- 't1['x] = 't2['x] in 'C['x] } =
   it

let thinLastT n = (thinT (-1) thenT tryT (thinT n))

interactive tunionElimination_eq {| elim [ThinOption thinLastT] |} 'H :
   sequent { <H>; x: tunion{'A; y. 'B['y]}; <J['x]>; w: 'A; z: 'B['w];
                       u: 'z='x in tunion{'A; y. 'B['y]} >- squash{'C['z]} } -->
   sequent { <H>; x: tunion{'A; y. 'B['y]}; <J['x]> >- squash{'C['x]} }

interactive tunionElimination_disjoint (*{| elim [ThinOption thinLastT] |}*) 'H 'f :
   sequent { <H>; x: tunion{'A; y. 'B['y]}; <J['x]>; w: 'A; z: 'B['w];
                       u: 'z='x in tunion{'A; y. 'B['y]} >- 'f 'z = 'w in 'A } -->
   sequent { <H>; x: tunion{'A; y. 'B['y]}; <J['x]>; w: 'A; z: 'B['w];
                       u: 'z='x in tunion{'A; y. 'B['y]} >- 'C['z] } -->
   sequent { <H>; x: tunion{'A; y. 'B['y]}; <J['x]> >- 'C['x] }

doc <:doc< @docoff >>

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let tunion_term = << Union x:'A. 'B['x]  >>
let tunion_opname = opname_of_term tunion_term
let mk_tunion_term = mk_dep0_dep1_term tunion_opname
let is_tunion_term = is_dep0_dep1_term tunion_opname
let dest_tunion = dest_dep0_dep1_term tunion_opname

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
