doc <:doc< 
   @begin[doc]
   @module[Itt_bisect]
  
   The @tt{Itt_bisect} module derives a binary intersection
   $@bisect{A; B}$ from the intersection @hrefterm[isect] defined
   in the @hrefmodule[Itt_isect] theory, and the Boolean values
   defined in the @hrefmodule[Itt_bool] theory.
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
extends Itt_isect
extends Itt_bool
doc <:doc< @docoff >>

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Var
open Tactic_type
open Tactic_type.Tacticals

open Dtactic

open Perv

open Itt_equal
open Itt_struct


(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @terms
  
   The definition of the binary intersection $@bisect{A; B}$
   is an intersection over the Booleans.
   @end[doc]
>>
define unfold_bisect : bisect{'A; 'B} <-->
                          "isect"{bool; x. ifthenelse{'x; 'A; 'B}}
doc <:doc< @docoff >>

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_bisect

dform bisect_df : except_mode[src] :: parens :: "prec"[prec_bisect] :: bisect{'A; 'B} =
   slot["le"]{'A} `" " cap space slot{'B}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @rules
   @modsubsection{Typehood and equality}
  
   The binary intersection $@bisect{A; B}$ is well-formed if both $A$
   and $B$ are types.
   @end[doc]
>>
interactive bisectEquality {| intro []; eqcd |} :
   [wf] sequent [squash] { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { <H> >- 'B1 = 'B2 in univ[i:l] } -->
   sequent ['ext] { <H> >- bisect{'A1; 'B1} = bisect{'A2; 'B2} in univ[i:l] }

interactive bisectType {| intro [] |} :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   [wf] sequent [squash] { <H> >- "type"{'B} } -->
   sequent ['ext] { <H> >- "type"{bisect{'A; 'B}} }

doc <:doc< 
   Formation.
   @docoff
>>
interactive bisectFormation :
   sequent ['ext] { <H> >- univ[i:l] } -->
   sequent ['ext] { <H> >- univ[i:l] } -->
   sequent ['ext] { <H> >- univ[i:l] }

doc <:doc< 
   @begin[doc]
   @modsubsection{Membership}
  
   Two terms $x$ and $y$ are equal in the binary intersection
   $@bisect{A; B}$ if they are equal in both $A$ and $B$.  Put another
   way, the elements of the binary intersection are the terms that
   are members of both $A$ and $B$.
   @end[doc]
>>
interactive bisectMemberEquality {| intro []; eqcd |} :
   [wf] sequent [squash] { <H> >- 'x = 'y in 'A } -->
   [wf] sequent [squash] { <H> >- 'x = 'y in 'B } -->
   sequent ['ext] { <H> >- 'x = 'y in 'A isect 'B }

doc <:doc< 
   @begin[doc]
   @modsubsection{Elimination}
  
   The elimination rule for an assumption $x@colon @bisect{A; B}$ states that  $x$ can be replaced by
   $a @in A$ or by $b @in B$.
   @end[doc]
>>
doc <:doc< @docoff >>

interactive bisectElimination_eq 'H bind{x.bind{a,b.'C['x;'a;'b]}} :
   sequent ['ext] { <H>; x: 'A isect 'B; <J['x]>; a: 'A; u: 'a = 'x in 'A;
                                                   b: 'B; v: 'b = 'x in 'B >- 'C['x;'a;'b] } -->
   sequent ['ext] { <H>; x: 'A isect 'B; <J['x]> >- 'C['x;'x;'x] }

let bisectEliminationT = argfunT (fun n p ->
   let n = Sequent.get_pos_hyp_num p n in
   let x = Sequent.nth_binding p n in
   let x_var = mk_var_term x in
   let bind =  get_with_arg p in
      if is_bind2_term bind then
         let bind = mk_bind1_term x bind in
            bisectElimination_eq n bind
      else
         raise (RefineError
           ("bisectElimination", StringTermError ("required the bind term:",<<bind{a,b.'C['a;'b]}>>))))

let bisectEliminationT = argfunT (fun n p ->
   let n = Sequent.get_pos_hyp_num p n in
      bisectEliminationT n thenT thinIfThinningT [-3;-1;n])

let resource elim += (<<'A isect 'B>>,bisectEliminationT)

doc <:doc< >>

interactive bisectElimination 'H bind{a,b.'C['a;'b]} :
   sequent ['ext] { <H>; x: 'A isect 'B; <J['x]>; a: 'A; b: 'B >- 'C['a;'b] } -->
   sequent ['ext] { <H>; x: 'A isect 'B; <J['x]> >- 'C['x;'x] }

doc <:doc< 
   @begin[doc]
  
   The elimination rule has also two simpler forms.
   The first produces a witness that $x @in A$, and the second produces a witness
   for $x @in B$.
   @end[doc]
>>


interactive bisectEliminationLeft (*{| elim [SelectOption 1] |}*) 'H :
   sequent ['ext] { <H>; x: 'A isect 'B; <J['x]>; a: 'A; u: 'a = 'x in 'A; b: 'B; v: 'b = 'x in 'B >- 'C['a] } -->
   sequent ['ext] { <H>; x: 'A isect 'B; <J['x]> >- 'C['x] }

interactive bisectEliminationRight (*{| elim [SelectOption 2] |}*) 'H :
   sequent ['ext] { <H>; x: 'A isect 'B; <J['x]>; a: 'A; u: 'a = 'x in 'A; b: 'B; v: 'b = 'x in 'B >- 'C['b] } -->
   sequent ['ext] { <H>; x: 'A isect 'B; <J['x]> >- 'C['x] }

let bisectEliminationT = argfunT (fun n p ->
   let n = Sequent.get_pos_hyp_num p n in
   try
      let sel = get_sel_arg p in
      let r =
         if sel = 1 then bisectEliminationLeft else
         if sel = 2 then bisectEliminationRight else
            raise (RefineError ("bisectElimination", StringError ("select option is out of range ([1,2])")))
      in r n thenT thinIfThinningT [-3;-1;n]
   with RefineError _ -> 
      bisectEliminationT n)

let resource elim += (<<'A isect 'B>>,bisectEliminationT)

doc <:doc< @doc{Equality elimination.} >>

interactive bisectEqualityElim {| elim [ThinOption thinT] |} 'H :
   sequent['ext] { <H>; x: 't1 = 't2 in 'A isect 'B; u : 't1 = 't2 in 'A; v : 't1 = 't2 in 'B; <J['x]> >- 'C['x] } -->
   sequent['ext] { <H>; x: 't1 = 't2 in 'A isect 'B; <J['x]> >- 'C['x] }

doc <:doc< 
   @begin[doc]
   @modsubsection{Subtyping}
  
   The binary intersection $@bisect{A; B}$ is covariant
   in both $A$ and $B$.
   @end[doc]
>>
interactive bisectSubtypeLeft {| intro [SelectOption 1] |} :
   sequent [squash] { <H> >- "type"{'B} } -->
   sequent [squash] { <H> >- 'A  subtype 'C } -->
   sequent ['ext] { <H> >- 'A isect 'B  subtype 'C}

interactive bisectSubtypeRight {| intro [SelectOption 2] |} :
   sequent [squash] { <H> >- "type"{'A} } -->
   sequent [squash] { <H> >- 'B  subtype 'C } -->
   sequent ['ext] { <H> >- 'A isect 'B  subtype  'C }

interactive bisectSubtypeBelow {| intro [] |}:
   sequent [squash] { <H> >- 'C  subtype 'A } -->
   sequent [squash] { <H> >- 'C  subtype 'B } -->
   sequent ['ext] { <H> >- 'C  subtype   'A isect 'B}
doc <:doc< @docoff >>

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
