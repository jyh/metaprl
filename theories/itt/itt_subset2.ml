doc <:doc< 
   @begin[doc]
   @module[Itt_subset2]
  
   In this theory we prove some facts about subset relation defines in Section @refmodule[Itt_subset]. 
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
  
   Author:  Alexei Kopylov @email{kopylov@cs.cornell.edu}
  
   @end[license]
>>

doc <:doc< 
   @begin[doc]
   @parents
   @end[doc]
>>
extends Itt_subset
extends Itt_set
extends Itt_isect
extends Itt_union
extends Itt_bisect
extends Itt_bunion
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
   show_loading "Loading Itt_subset2%t"



doc <:doc< 
 @begin[doc]
   @modsection{Sets}
  The subset relation corresponds to set type (Section @refmodule[Itt_set]) in the following way:
  $<<'A subset 'B>>$ if and only if there is a proposition $P: <<'B -> univ[i:l]>>$, such that
  $<<ext_equal{'A; {x:'B | 'P['x]}}>>$.
 @end[doc]
>>


interactive set_subset {| intro [] |}  :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H; x: 'A >- "type"{'P['x]} } -->
   sequent ['ext] { 'H >- {a: 'A | 'P['a]} subset 'A }

interactive subset_set {| intro [] |}  :
   sequent [squash] { 'H >- 'A subset 'B } -->
   sequent ['ext] { 'H >- ext_equal{{x: 'B | 'x in 'A subset 'B}; 'A} }

interactive subset_iff  :
   [wf] sequent [squash] { 'H >- 'A in univ[i:l] } -->
   [wf] sequent [squash] { 'H >- 'B in univ[i:l] } -->
   sequent ['ext] {'H >- iff{'A subset 'B; exst P:'B -> univ[i:l]. ext_equal{{x:'B| 'P 'x}; 'A}} }


doc <:doc< 
 @begin[doc]
 @modsection{Lattice}
  Subsets of a given type forms a lattice with respect to $<<space subset space>>$ relation and intersection and union operations.

  @modsubsection{Order}
  Subset relation forms a partial order on types.
 @end[doc]
>>



interactive subset_ref {| intro [] |}  :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- 'A subset 'A }


interactive subset_trans 'B:
   sequent ['ext] { 'H >- 'A subset 'B } -->
   sequent ['ext] { 'H >- 'B subset 'C } -->
   sequent ['ext] { 'H >- 'A subset 'C }

 
interactive subset_exact:
   sequent ['ext] { 'H >- 'A subset 'B } -->
   sequent ['ext] { 'H >- 'B subset 'A } -->
   sequent ['ext] { 'H >- ext_equal{'A;'B} }



doc <:doc< 
   @begin[doc]
   @modsubsection{Union and Intersection}
   Although intersection and union on types do not behave as set-theoretic union and intersection,
   they works exactly as set-theoretic union and intersection on @em{subsets} of a given type.

   Intersection of @emph{non-empty} family of subsets of a given type is subset of this type.
   @end[doc]
>>

interactive subset_isect {| intro[AutoMustComplete] |}:
   sequent [squash] { 'H >-'I } -->
   sequent [squash] { 'H; i: 'I >- 'A['i] subset 'T } -->
   sequent ['ext] { 'H >- Isect i:'I. 'A['i] subset 'T }

interactive subset_bisect {| intro[AutoMustComplete] |}:
   sequent [squash] { 'H >-'A subset 'T} -->
   sequent [squash] { 'H >-'B subset 'T} -->
   sequent ['ext] { 'H >- 'A isect 'B subset 'T }

doc <:doc< 
   @begin[doc]
   Note that if only one of types is subset of $T$ then it does not mean that their intersection is subset of $T$.
   @end[doc]
>>

interactive counterexample2 :
   sequent ['ext] { 'H >- not{(bool isect top subset top)} }

doc <:doc< 
   @begin[doc]

   Union of a family of subsets of a given type is subset of this type.
   @end[doc]
>>
      
interactive subset_union {| intro[] |}:
   sequent [squash] { 'H >-"type"{'I} } -->
   sequent [squash] { 'H; i: 'I >- 'A['i] subset 'T } -->
   sequent ['ext] { 'H >- Union i:'I. 'A['i] subset 'T }

interactive subset_bunion {| intro[] |}:
   sequent [squash] { 'H >-'A subset 'T}  -->
   sequent [squash] { 'H >-'B subset 'T}  -->
   sequent ['ext] { 'H >- 'A bunion 'B subset 'T }


doc <:doc< 
   @begin[doc]
   @modsection{Monotonicity}
    Most of the type constructors are monotone with respect to $<<space subset space>>$.
   @end[doc]
>>

interactive prod_subset {| intro [] |} :
   sequent [squash] { 'H >- 'A subset '"A'" } -->
   sequent [squash] { 'H >- 'B subset '"B'" } -->
   sequent ['ext] { 'H >- 'A * 'B subset '"A'" * '"B'" } 
      
interactive union_subset {| intro [] |} :
   sequent [squash] { 'H >- 'A subset '"A'" } -->
   sequent [squash] { 'H >- 'B subset '"B'" } -->
   sequent ['ext] { 'H >- 'A + 'B subset '"A'" + '"B'" } 

doc <:doc< @docoff >>

      
(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
