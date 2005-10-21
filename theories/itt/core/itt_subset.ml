doc <:doc<
   @module[Itt_subset]

   The @tt[Itt_subset] module provides the set-theoretic definition of
   @emph{subset}. A type $A$ is a subset of a type $B$,
   <<'A subset 'B>>, if $A$ is a subtype of $B$ and if any one of two equal
   elements in $B$ is in $A$ then another element is also in $A$
   (that is, two equal elements in $B$ are either both in $A$ or both not in $A$).
   As a corollary we have that $A$ and $B$ have the same equality on the
   elements of $A$. That is, for any two elements of $A$ if they are equal in $B$,
   then they are also equal in $A$ (see rule @hrefrule[use_superset1]).

   Not every subtype is subset. For example, <<'Z  subtype ('Z subtwo)>>
   but not <<'Z subset ('Z subtwo)>>. See also @hrefrule[counterexample1].

   The main property of <<'A subset 'B>> is that the membership in $A$ could
   be defined for all elements in $B$.

   The subset relation corresponds to set type (Section @refmodule[Itt_set]) in the following way:
   <<'A subset 'B>> if and only if there is a proposition $P: <<'B -> univ[i:l]>>$, such that
   <<ext_equal{'A; {x:'B | 'P['x]}}>> (see @hrefrule[subset_iff]).

   Type-theoretic intersection and union (Sections @refmodule[Itt_isect] and @refmodule[Itt_tunion])
   behaves on subsets of a given type  like usual intersection and union.

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

   Authors:
    Jason Hickey @email{jyh@cs.caltech.edu}
    Xin Yu @email{xiny@cs.caltech.edu},
    Alexei Kopylov @email{kopylov@cs.cornell.edu}
    An equivalent definition of "strong subtype" was in Mark Bickford's Logic of Events.

   @end[license]
>>

doc <:doc<
   @parents
>>
extends Itt_equal
extends Itt_subtype
extends Itt_struct
extends Itt_logic
extends Itt_singleton
extends Itt_squash
extends Itt_isect
extends Itt_bool
extends Itt_ext_equal

doc docoff

open Lm_debug
open Lm_printf

open Basic_tactics

open Itt_equal
open Itt_subtype
open Itt_squash

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_subset%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc<
   @modsection{Definitions}

>>

define mem : mem{'a; 'A; 'B} <--> (singleton{'a;'B} subtype 'A)

define unfold_subset : "subset"{'A; 'B} <-->
   ('A subtype 'B & all a: 'A. mem{'a; 'A; 'B})

define member : member{'a; 'A; 'B} <--> mem{'a; 'A; 'B} & 'A subset 'B & 'a in 'B

doc docoff

let fold_subset = makeFoldC << 'A subset 'B >> unfold_subset

let subset_term = << 'A subset 'B >>
let subset_opname = opname_of_term subset_term
let is_subset_term = is_dep0_dep0_term subset_opname
let dest_subset = dest_dep0_dep0_term subset_opname
let mk_subset_term = mk_dep0_dep0_term subset_opname

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform subset_df1 : except_mode[src] :: parens :: "prec"[prec_equal] :: mem{'a;'A; 'B} =
    szone pushm slot{'a} space Mpsymbols!member sub{'B} hspace slot{'A} popm ezone

dform subset_df1 : except_mode[src] :: parens :: "prec"[prec_equal] :: ('a in 'A subset 'B) =
    szone pushm slot{'a} space Mpsymbols!member hspace ('A subset 'B) popm ezone

dform subset_df1 : mode[src] :: parens :: "prec"[prec_equal] :: member{'a;'A; 'B} =
    'a `" in " 'A `" subset " 'B

dform subset_df1 : except_mode[src] :: parens :: "prec"[prec_subtype] :: ('A subset 'B) =
   slot{'A} `" " subseteq space slot{'B}

dform subset_df1 : mode[src] :: parens :: "prec"[prec_subtype] :: ('A subset 'B) =
   slot{'A} `" subset " slot{'B}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)
doc <:doc<
   @modsection{Basic Rules}
>>

interactive mem_univ {| intro [] |}  :
   sequent { <H> >- singleton{'a1; 'B1} = singleton{'a2; 'B2} in univ[i:l] } -->
   sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   sequent { <H> >- mem{'a1;'A1;'B1} = mem{'a2; 'A2; 'B2} in univ[i:l]}

interactive mem_wf {| intro [] |}  :
   sequent { <H> >- 'a in 'B } -->
   sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- "type"{mem{'a;'A;'B}} }

interactive mem_intro {| intro [] |}  :
   [wf] sequent { <H> >- 'a in 'B } -->
   sequent { <H>; b:'B; u: 'a='b in 'B >- 'b in 'A} -->
   sequent { <H> >- mem{'a;'A;'B} }

doc <:doc<
   @modsubsection{Subset}
   @modsubsection{Typehood and equality}
   Type <<'A subset 'B>> is well-formed whenever $A$ and $B$ are types.
   Two subset-types are equal if their subterms are equal and any element
   in one of the first subterm is also in the other.
>>

interactive subset_univ {| intro [] |} :
   sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   sequent { <H> >- 'B1 = 'B2 in univ[i:l] } -->
   sequent { <H> >- ('A1 subset 'B1) = ('A2 subset 'B2) in univ[i:l] }

interactive subset_wf {| intro [] |} :
   sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- "type"{'B} } -->
   sequent { <H> >- "type"{'A subset 'B} }

doc <:doc<
   @modsubsection{Introduction Rule}
>>

interactive subset_intro {| intro [AutoMustComplete] |}  :
   [wf] sequent { <H> >- 'A subtype 'B } -->
   [main] sequent { <H>; a: 'A; b: 'B; u: 'a = 'b in 'B >- 'b in 'A } -->
   sequent { <H> >- 'A subset 'B }

doc docoff

(* mem, member and subset are squash stable: *)

interactive mem_sqstable {| squash |} :
   sequent { <H> >- squash{mem{'x;'A;'B}} } -->
   sequent { <H> >- mem{'x;'A;'B} }

interactive subset_sqstable {| squash |} :
   sequent { <H> >- squash{'A subset 'B} } -->
   sequent { <H> >- 'A subset 'B }

interactive member_sqstable {| squash |} :
   sequent { <H> >- squash{'x in 'A subset 'B} } -->
   sequent { <H> >- 'x in 'A subset 'B }

doc <:doc<
   @modsubsection{Elimination Rules}

   By definition if <<'A subset 'B>> then  <<'A subtype 'B>>. (The opposite is not true --- see @hrefrule[counterexample1] below).
>>

interactive subset_is_subtype {| nth_hyp |} :
   [assertion] sequent { <H> >- 'A subset 'B } -->
   sequent { <H> >- 'A subtype 'B }

doc <:doc<
   As a corollary we have that if two element are equal in a subset then they are equal in a superset.
>>

interactive use_subset  'A :
   [assertion] sequent { <H> >- 'A subset 'B } -->
   sequent { <H> >- 'x = 'y in 'A } -->
   sequent { <H> >- 'x = 'y in 'B }

doc <:doc<
   If two elements are equal in a type $B$ then they are equal in a subtype $A$ of $B$, if at least one of them is in $A$.
>>

interactive use_superset1  'B :
   [assertion] sequent { <H> >- 'A subset 'B } -->
   sequent { <H> >- 'x in 'A } -->
   sequent { <H> >- 'x = 'y in 'B } -->
   sequent { <H> >- 'x = 'y in 'A }

interactive use_superset2  'B :
   [assertion] sequent { <H> >- 'A subset 'B } -->
   sequent { <H> >- 'y in 'A } -->
   sequent { <H> >- 'x = 'y in 'B } -->
   sequent { <H> >- 'x = 'y in 'A }

doc <:doc<
    As a corollary we have that if two element are equal in $B$ then if one of them is in $A$ then another one is also in $A$.
>>
interactive use_superset 'B 'y:
   [assertion] sequent { <H> >- 'A subset 'B } -->
   sequent { <H> >- 'y in 'A } -->
   sequent { <H> >- 'x = 'y in 'B } -->
   sequent { <H> >- 'x  in 'A }

doc <:doc<
   Note that the rule @hrefrule[subset_is_subtype] is not reversible: <<'A subtype 'B>> does not imply <<'A subset 'B>>.
   For example, any type is subtype of <<top>>, but not every type is @emph{subset} of <<top>>.
>>

interactive counterexample1 :
   sequent { <H> >- not{(bool subset top)} }

doc <:doc<
   If <<'A subset 'B>> is true, then both $A$ and $B$ are types.
>>
(* Note than if would have reverse functionality we could say that if A subset B Type then both A and B are types *)

interactive subsetTypeRight  'B :
   [main] sequent { <H> >- 'A subset 'B } -->
   sequent { <H> >- "type"{'A} }

interactive subsetTypeLeft  'A :
   [main] sequent { <H> >- 'A subset 'B }  -->
   sequent { <H> >- "type"{'B} }

doc <:doc<
   @modsubsection{Membership}
   Proposition <<'a in 'A subset 'B>> is almost equal to conjunction of
   <<'a in 'A>> and <<'A subset 'B>>, but its well-formedness is more liberal.
   Indeed, <<'a in 'A subset 'B>> is well-formed whenever <<'a in 'B>> and $A$ and $B$ are types.
>>

(* Note that we don't need this membership if we add a rule: A subset B --> x in B --> x in A Type  *)

interactive member_univ {| intro [] |} :
   sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   sequent { <H> >- 'B1 = 'B2 in univ[i:l] } -->
   sequent { <H> >- 'a1 = 'a2 in 'B1 } -->
   sequent { <H> >- 'a1 = 'a2 in 'B2 } -->
   sequent { <H>; x: 'A1 >- 'x in 'B1 } -->
   sequent { <H>; x: 'B1 >- 'x in 'B2 } -->
   sequent { <H> >- ('a1 in 'A1 subset 'B1) = ('a2 in 'A2 subset 'B2) in univ[i:l] }

interactive member_wf {| intro [] |}  :
   sequent { <H> >- 'a in 'B } -->
   sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- "type"{'a in 'A subset 'B} }

doc <:doc<
   Introduction and elimination rules reflect the fact that <<'a in 'A subset 'B>>
   if and only if <<'a in 'A>> and <<'A subset 'B>>.
>>

interactive member_intro {| intro [] |}  :
   sequent { <H> >- 'a in 'A } -->
   sequent { <H> >- 'A subset 'B } -->
   sequent { <H> >- 'a in 'A subset 'B }

interactive member_elim {| elim [] |} 'H :
   sequent { <H>; u: 'a in 'A; v: 'A subset 'B; <J> >- 'C } -->
   sequent { <H>; u: 'a in 'A subset 'B; <J> >- 'C  }

doc <:doc<
   Note that the truth of predicate <<'a in 'A subset 'B>> does not depend on $B$ whenever
   <<'A subtype 'B>> and this predicate is well-formed.
   This fact establishes a validity of introducing a binary membership <<'a in 'A>> with the liberal well-formedness rule.
>>

interactive member_doesnot_depend_on_B :
   sequent { <H> >- 'A subset '"B'" } -->
   sequent { <H>; u: 'a in 'A subset 'B >- 'a in 'A subset '"B'" }

doc docoff

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
