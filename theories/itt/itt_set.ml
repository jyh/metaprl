doc <:doc< 
   @begin[doc]
   @module[Itt_set]
  
   The @tt[Itt_set] module defines a ``set'' type, or more precisely,
   it defines a type by quantified @emph{separation}.  The form of the type is
   $@set{x; T; P[x]}$, where $T$ is a type, and $P[x]$ is a type for
   any element $x @in T$.  The elements of the set type are those elements
   of $x @in T$ where the proposition $P[x]$ is true.
  
   The set type is a ``squash'' type: the type is similar to the
   dependent product $x@colon T @times P[x]$ (Section @refmodule[Itt_dprod]),
   but the proof $P[x]$ is omitted (squashed).  The set type <<{x: 'T| 'P['x]}>>
   is always a subtype of $T$.
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
   @email{jyh@cs.caltech.edu}
  
   @end[license]
>>

doc <:doc< 
   @begin[doc]
   @parents
   @end[doc]
>>
extends Itt_squash
extends Itt_equal
extends Itt_unit
extends Itt_subtype
extends Itt_struct
doc <:doc< @docoff >>

open Lm_debug
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp

open Dtactic

open Itt_equal
open Itt_subtype

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_set%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @terms
  
   The @tt{set} term defines the set type.
   @end[doc]
>>
declare set{'A; x. 'B['x]}
doc <:doc< @docoff >>

let set_term = << { a: 'A | 'B['a] } >>
let set_opname = opname_of_term set_term
let is_set_term = is_dep0_dep1_term set_opname
let dest_set = dest_dep0_dep1_term set_opname
let mk_set_term = mk_dep0_dep1_term set_opname

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform set_df1 : {x:'A | 'B} = math_set {'x; 'A; 'B}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @rules
   @modsubsection{Equality and typehood}
  
   The set type $@set{x; A; B[x]}$ is a type if $A$ is a type,
   and $B[x]$ is a type for any $x @in A$.  Equality of the set
   type is @emph{intensional}.  Two set types are equal only if their
   parts are equal. Note that it is possible to define
   an @emph{extensional} version of a set type using the @emph{intensional} one
   by applying the @hrefterm[esquash] operator to the set predicate.
   @end[doc]
>>
prim setEquality {| intro []; eqcd |} :
   [wf] sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent { <H>; x: 'A1 >- 'B1['x] = 'B2['x] in univ[i:l] } -->
   sequent { <H> >- { a1:'A1 | 'B1['a1] } = { a2:'A2 | 'B2['a2] } in univ[i:l] } =
   it

prim setType {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H>; x: 'A >- "type"{'B['x]} } -->
   sequent { <H> >- "type"{.{ a:'A | 'B['a] }} } =
   it

doc <:doc< 
   @begin[doc]
   @modsubsection{Membership}
  
   Two terms $a_1$ and $a_2$ are equal in the set type $@set{a; A; B[a]}$
   if they are equal in $A$ and also $B[a_1]$ is true.
   @end[doc]
>>
prim setMemberEquality {| intro []; eqcd |} :
   [wf] sequent { <H> >- 'a1 = 'a2 in 'A } -->
   [assertion] sequent { <H> >- squash{'B['a1]} } -->
   [wf] sequent { <H>; x: 'A >- "type"{'B['x]} } -->
   sequent { <H> >- 'a1 = 'a2 in { a:'A | 'B['a] } } =
   it

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction}
  
   A set type $@set{x; A; B[x]}$ is true if there is an element $a @in A$
   where $B[a]$ is true.
   @end[doc]
>>
interactive setMemberFormation {| intro [] |} 'a :
   [wf] sequent { <H> >- 'a = 'a in 'A } -->
   [main] sequent { <H> >- squash{'B['a]} } -->
   [wf] sequent { <H>; z: 'A >- "type"{'B['z]} } -->
   sequent { <H> >- { x:'A | 'B['x] } }

doc <:doc< 
   @begin[doc]
   @modsubsection{Elimination}
  
   An assumption with a set type $u@colon @set{x; A; B[x]}$ asserts two facts:
   that $u @in A$ and $B[u]$.  However, the proof of $B[u]$ is unavailable.  The
   $@squash{'B['u]}$ hypothesis states that $B[u]$ is true, but its proof is
   omitted.
   @end[doc]
>>
prim setElimination {| elim [] |} 'H :
   ('t['u;'i] : sequent { <H>; u: 'A; i: squash{'B['u]}; <J['u]> >- 'T['u] }) -->
   sequent { <H>; u: { x:'A | 'B['x] }; <J['u]> >- 'T['u] } =
   't['u;it]

doc <:doc< 
   @begin[doc]
   @modsubsection{Subtyping}
  
   The set type $@set{x; A; B[x]}$ is always a subtype of $A$ if
   the set type is really a type.  This rule is added to the
   @hrefresource[subtype_resource].
   @end[doc]
>>
interactive set_subtype {| intro [] |} :
   sequent { <H> >- "type"{ { a: 'A | 'B['a] } } } -->
   sequent { <H> >- \subtype{ { a: 'A | 'B['a] }; 'A } }

doc docoff

(*
 * H >- Ui ext { a:A | B }
 * by setFormation A
 *
 * H >- A = A in Ui
 * H, a: A >- Ui ext B
 *)
prim setFormation 'A :
   [wf] sequent { <H> >- 'A = 'A in univ[i:l] } -->
   ('B['a] : sequent { <H>; a: 'A >- univ[i:l] }) -->
   sequent { <H> >- univ[i:l] } =
   { a: 'A | 'B['a] }

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let resource typeinf += (set_term,  infer_univ_dep0_dep1 dest_set)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

let resource sub += (LRSubtype ([<< { a: 'A | 'B['a] } >>, << 'A >>], set_subtype))

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
