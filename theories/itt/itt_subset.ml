doc <:doc< 
   @spelling{Bickford}
   
   @begin[doc]
   @module[Itt_subset]
  
   The @tt[Itt_subset] module provides the set-theoretic definition of
   @emph{subset}. A type $A$ is a subset of a type $B$,
   $@subset{A; B}$, if $A$ is a subtype of $B$ and if any one of two equal
   elements in $B$ is in $A$ then another element is also in $A$
   (that is, two equal elements in $B$ are either both in $A$ or both not in $A$).
   As a corollary we have that $A$ and $B$ have the same equality on the
   elements of $A$. That is, for any two elements of $A$ if they are equal in $B$,
   then they are also equal in $A$ (see rule @hrefrule[use_superset1]).

   Not every subtype is subset. For example, $<<int  subtype (int subtwo)>>$
   but not $<<int subset (int subtwo)>>$. See also @hrefrule[counterexample1].
  
   The main property of $<<'A subset 'B>>$ is that the membership in $A$ could
   be defined for all elements in $B$.
  
   The subset relation corresponds to set type (Section @refmodule[Itt_set]) in the following way:
   $<<'A subset 'B>>$ if and only if there is a proposition $P: <<'B -> univ[i:l]>>$, such that
   $<<ext_equal{'A; {x:'B | 'P['x]}}>>$ (see @hrefrule[subset_iff]).
  
   Type-theoretic intersection and union (Sections @refmodule[Itt_isect] and @refmodule[Itt_tunion])
   behaves on subsets of a given type  like usual intersection and union.

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
  
   Authors:
    Jason Hickey @email{jyh@cs.caltech.edu}
    Xin Yu @email{xiny@cs.caltech.edu},
    Alexei Kopylov @email{kopylov@cs.cornell.edu}
    An equivalent definition of "strong subtype" was in Mark Bickford's Logic of Events. 
  
   @end[license]
>>

doc <:doc< 
   @begin[doc]
   @parents
   @end[doc]
>>
extends Itt_equal
extends Itt_subtype
extends Itt_struct
extends Itt_logic
extends Itt_singleton
extends Itt_squash
extends Itt_isect
extends Itt_bool
extends Itt_int_base
extends Itt_ext_equal

doc <:doc< @docoff >>

open Printf
open Mp_debug
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermAddr
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError
open Mp_resource
open Simple_print

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Tactic_type.Conversionals
open Mptop
open Var

open Base_dtactic
open Base_auto_tactic

open Itt_equal
open Itt_struct
open Itt_logic
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
   @begin[doc]
   @modsection{Definitions}
  
   @end[doc]
>>

define mem : mem{'a; 'A; 'B} <--> (singleton{'a;'B} subtype 'A)

define unfold_subset : "subset"{'A; 'B} <-->
   ('A subtype 'B & all a: 'A. mem{'a; 'A; 'B})

define member : member{'a; 'A; 'B} <--> mem{'a; 'A; 'B} & 'A subset 'B & 'a in 'B

doc <:doc< @docoff >>

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
    szone pushm slot{'a} space Nuprl_font!member sub{'B} hspace slot{'A} popm ezone

dform subset_df1 : except_mode[src] :: parens :: "prec"[prec_equal] :: ('a in 'A subset 'B) =
    szone pushm slot{'a} space Nuprl_font!member hspace math_subset{'A; 'B} popm ezone

dform subset_df1 : mode[src] :: parens :: "prec"[prec_equal] :: member{'a;'A; 'B} =
    'a `" in " 'A `" subset " 'B

dform subset_df1 : except_mode[src] :: parens :: "prec"[prec_subtype] :: ('A subset 'B) =
   math_subset{'A; 'B}

dform subset_df1 : mode[src] :: parens :: "prec"[prec_subtype] :: ('A subset 'B) =
   'A `" subset " 'B

(************************************************************************
 * RULES                                                                *
 ************************************************************************)
doc <:doc< 
   @begin[doc]
   @modsection{Basic Rules}
   @end[doc] 
>>

interactive mem_wf {| intro [] |}  :
   sequent [squash] { 'H >- 'a in 'B } -->
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- "type"{mem{'a;'A;'B}} }

interactive mem_intro {| intro [] |}  :
   [wf] sequent [squash] { 'H >- 'a in 'B } -->
   sequent [squash] { 'H; b:'B; u: 'a='b in 'B >- 'b in 'A} -->
   sequent ['ext] { 'H >- mem{'a;'A;'B} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Subset}
   @modsubsection{Well-formedness}
   Type $<<'A subset 'B>>$ is well-formed whenever $A$ and $B$ are types.
   @end[doc]
>>

interactive subset_wf {| intro [] |} :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{.'A subset 'B} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction Rule}
   @end[doc]
>>
      
interactive subset_intro {| intro [] |}  :
   [wf] sequent [squash] { 'H >- 'A subtype 'B } -->
   [main] sequent [squash] {'H; a: 'A; b: 'B; u: 'a = 'b in 'B >- 'b in 'A } -->
   sequent ['ext] { 'H >- 'A subset 'B }

doc <:doc< @docoff >>

(* mem, member and subset are squash stable: *)      
      
interactive subset_sqstable {| squash |} :
   sequent [squash] { 'H >- squash{'A subset 'B} } -->
   sequent ['ext] { 'H >- 'A subset 'B }

doc <:doc< 
   @begin[doc]
   @modsubsection{Elimination Rules}

   By definition if $<<'A subset 'B>>$ then  $<<'A subtype 'B>>$. (The opposite is not true --- see @hrefrule[counterexample1] below).
   @end[doc]
>>

interactive subset_is_subtype  :
   [assertion] sequent [squash] { 'H >- 'A subset 'B } -->
   sequent ['ext] { 'H >- 'A subtype 'B }

doc <:doc< 
   @begin[doc]
   As a corollary we have that if two element are equal in a subset then they are equal in a superset.
   @end[doc]
>>

interactive use_subset  'A :
   [assertion] sequent [squash] { 'H >- 'A subset 'B } -->
   sequent [squash] { 'H >- 'x = 'y in 'A } -->
   sequent ['ext] { 'H >- 'x = 'y in 'B }

doc <:doc< 
   @begin[doc]
   If two elements are equal in a type $B$ then they are equal in a subtype $A$ of $B$, if at least one of them is in $A$.
   @end[doc]
>>

interactive use_superset1  'B :
   [assertion] sequent [squash] { 'H >- 'A subset 'B } -->
   sequent [squash] { 'H >- 'x in 'A } -->
   sequent [squash] { 'H >- 'x = 'y in 'B } -->
   sequent ['ext] { 'H >- 'x = 'y in 'A }

interactive use_superset2  'B :
   [assertion] sequent [squash] { 'H >- 'A subset 'B } -->
   sequent [squash] { 'H >- 'y in 'A } -->
   sequent [squash] { 'H >- 'x = 'y in 'B } -->
   sequent ['ext] { 'H >- 'x = 'y in 'A }

doc <:doc< 
   @begin[doc]
    As a corollary we have that if two element are equal in $B$ then if one of them is in $A$ then another one is also in $A$.
   @end[doc]
>>
interactive use_superset 'B 'y:
   [assertion] sequent [squash] { 'H >- 'A subset 'B } -->
   sequent [squash] { 'H >- 'y in 'A } -->
   sequent [squash] { 'H >- 'x = 'y in 'B } -->
   sequent ['ext] { 'H >- 'x  in 'A }

doc <:doc< 
   @begin[doc]
   Note that the rule @hrefrule[subset_is_subtype] is not reversible: $<<'A subtype 'B>>$ does not imply $<<'A subset 'B>>$.
   For example, any type is subtype of $<<top>>$, but not every type is @emph{subset} of $<<top>>$.
   @end[doc]
>>

interactive counterexample1 :
   sequent ['ext] { 'H >- not{(bool subset top)} }

doc <:doc< 
   @begin[doc]
   If $<<'A subset 'B>>$ is true, then both $A$ and $B$ are types.
   @end[doc]
>>
(* Note than if would have reverse functionality we could say that if A subset B Type then both A and B are types *)
      
interactive subsetTypeRight  'B :
   [main] sequent [squash] { 'H >- 'A subset 'B } -->
   sequent ['ext] { 'H >- "type"{'A} }

interactive subsetTypeLeft  'A :
   [main] sequent [squash] { 'H >- 'A subset 'B }  -->
   sequent ['ext] { 'H >- "type"{'B} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Membership}
   Proposition $<<'a in 'A subset 'B>>$ is almost equal to conjunction of
   $<<'a in 'A>>$ and $<<'A subset 'B>>$, but its well-formedness is more liberal.
   Indeed, $<<'a in 'A subset 'B>>$ is well-formed whenever $<<'a in 'B>>$ and $A$ and $B$ are types.
   @end[doc]
>>

(* Note that we don't need this membership if we add a rule: A subset B --> x in B --> x in A Type  *)
      
interactive member_wf {| intro [] |}  :
   sequent [squash] { 'H >- 'a in 'B } -->
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- "type"{'a in 'A subset 'B} }

doc <:doc< 
   @begin[doc]
   Introduction and elimination rules reflect the fact that $<<'a in 'A subset 'B>>$
   if and only if $<<'a in 'A>>$ and $<<'A subset 'B>>$.
   @end[doc]
>>
      
interactive member_intro {| intro [] |}  :
   sequent [squash] { 'H >- 'a in 'A } -->
   sequent [squash] { 'H >- 'A subset 'B } -->
   sequent ['ext] { 'H >- 'a in 'A subset 'B }

interactive member_elim {| elim [] |} 'H :
   sequent ['ext] { 'H; u: 'a in 'A; v: 'A subset 'B; 'J >- 'C } --> 
   sequent ['ext] { 'H; u: 'a in 'A subset 'B; 'J >- 'C  }

doc <:doc< 
   @begin[doc]
   Note that the truth of predicate $<<'a in 'A subset 'B>>$ does not depend on $B$ whenever
   $<<'A subtype 'B>>$ and this predicate is well-formed.
   @end[doc]
   This fact establishes a validity of introducing a binary membership <<'a in 'A>> with the liberal well-formedness rule.
>>

interactive member_doesnot_depend_on_B  'H:
   sequent [squash] { 'H >- 'A subtype 'B } -->
   sequent [squash] { 'H >- 'A subtype '"B'" } -->
   sequent ['ext] { 'H; u: 'a in 'A subset 'B >- 'a in 'A subset '"B'" }

doc <:doc< @docoff >>
      
(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
