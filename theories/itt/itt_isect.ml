doc <:doc< 
   @begin[spelling]
   isect
   @end[spelling]
   @begin[doc]
   @module[Itt_isect]
  
   The @tt{Itt_isect} module defines the @emph{intersection}
   type $@isect{x; A; B[x]}$.  The elements of the intersection
   are the terms that inhabit $B[x]$ for @emph{every} $x @in A$.
   The intersection is similar to the function space $@fun{x; A; B[x]}$;
   the intersection is inhabited if-and-only-if there is a constant
   function in the dependent-function space.
  
   The intersection does not have a conventional
   set-theoretic interpretation.  One example is the
   type $@top @equiv @isect{x; @void; @void}$.  If the set theoretic
   interpretation of $@void$ is the empty set, the intersection
   would probably be empty.  However, in the type theory,
   the intersection contains @emph{every} term $t$ because the
   quantification is empty.
  
   Another example is the type $@isect{T; @univ{i}; T @rightarrow T}$,
   which contains all the identity functions.  The set-theoretic
   interpretation of functions as sets of ordered pairs would again
   be empty.
  
   The intersection is commonly used to express polymorphism of
   function spaces, and it is also used as an operator for
   record type concatenation.  If records are expressed as
   functions from labels ($@atom$ is commonly used for labels) to
   values, the record type $@record{l@colon T}$ denotes the
   functions that return values of type $T$ when applied to the
   label $l$.  The intersection of two record types $@record{l_1@colon T_1}
   @bigcap @record{l_2@colon T_2}$ is isomorphic to the
   record space $@record{{l_1@colon T_1; l_2@colon T_2}}$.
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
extends Itt_set
extends Itt_rfun
extends Itt_logic
extends Itt_struct2
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

open Itt_equal
open Itt_struct
open Itt_subtype
open Perv

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_isect%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @terms
  
   The @tt{isect} term denotes the intersection type.
   The @tt{top} type defines the type of all terms
   $@isect{x; @void; @void}$.
   @end[doc]
>>
declare "isect"{'A; x. 'B['x]}

prim_rw unfold_top : top <--> "isect"{void; x. void}
doc <:doc< @docoff >>

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform isect_df1 : except_mode[src] :: (Isect x: 'A. 'B) =
   cap slot{'x} `":" slot{'A} `"." slot{'B}

dform isect_df2 : mode[src] :: (Isect x: 'A. 'B) =
   `"isect " slot{'x} `":" slot{'A} `"." slot{'B}

dform top_df : except_mode[src] :: top =
   `"Top"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext Isect x: A. B[x]
 * by intersectionFormation A
 * H >- A = A in Ui
 * H, x: A >- Ui ext B[x]
 *)
prim intersectionFormation 'A :
   [wf] sequent [squash] { <H> >- 'A = 'A in univ[i:l] } -->
   ('B['x] : sequent ['ext] { <H>; x: 'A >- univ[i:l] }) -->
   sequent ['ext] { <H> >- univ[i:l] } =
   Isect x: 'A. 'B['x]

doc <:doc< 
   @begin[doc]
   @rules
   @modsubsection{Typehood and equality}
  
   The intersection $@isect{x; A; B[x]}$ is well-formed if
   $A$ is a type, and $B[x]$ is a family of types indexed by
   $x @in A$.
   @end[doc]
>>
prim intersectionEquality {| intro []; eqcd |} :
   [wf] sequent [squash] { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { <H>; y: 'A1 >- 'B1['y] = 'B2['y] in univ[i:l] } -->
   sequent ['ext] { <H> >- Isect x1: 'A1. 'B1['x1] = Isect x2: 'A2. 'B2['x2] in univ[i:l] } =
   it

prim intersectionType {| intro [] |} :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   [wf] sequent [squash] { <H>; y: 'A >- "type"{'B['y]} } -->
   sequent ['ext] { <H> >- "type"{."isect"{'A; x. 'B['x]}} } =
   it

doc <:doc< 
   @begin[doc]
   The well-formedness of the $@top$ type is derived.
   The $@top$ type is a member of every type universe.
   @end[doc]
>>
interactive topUniv {| intro [] |} :
   sequent ['ext] { <H> >- top in univ[i:l] }

interactive topType {| intro [] |} :
   sequent ['ext] { <H> >- "type"{top} }


doc <:doc< 
   @begin[doc]
   @modsubsection{Membership}
   The elements in the intersection $@isect{x; A; B[x]}$ are the
   terms $b$ that inhabit $B[z]$ for @emph{every} $a @in A$.
   The member equality of the intersection is the intersection
   of the equalities on each type $B[z]$.  That is, for two elements
   of the intersection to be equal, they must be equal in
   @emph{every} type $B[z]$.
  
   The @hrefterm[top] type contains every program.  The equality here
   is trivial; all terms are equal in $@top$.
   @end[doc]
>>
prim intersectionMemberEquality {| intro []; eqcd |} :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   [wf] sequent [squash] { <H>; z: 'A >- 'b1 = 'b2 in 'B['z] } -->
   sequent ['ext] { <H> >- 'b1 = 'b2 in Isect x: 'A. 'B['x] } =
   it

interactive topMemberEquality {| intro []; eqcd |} :
   sequent ['ext] { <H> >- 'b1 = 'b2 in top }


doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction}
  
   In general the only one way to introduce intersection is
   to show @emph{explicitly} its witness.
   The following introduction rule is @emph{derived} from the
   @hrefrule[intersectionMemberEquality].
   @end[doc]
>>

interactive intersectionMemberFormation {| intro [] |} 'b :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   [wf] sequent [squash] { <H>; z: 'A >- 'b in 'B['z] } -->
   sequent ['ext] { <H> >-  Isect x: 'A. 'B['x] }

doc <:doc< 
   @begin[doc]
   In one special case when $B$ does not depend on $x$  we can derive
   simpler rule:
   $@isect{x; A; B}$ is inhabited if we can prove $B$ with the
   @emph{squashed} hypothesis $A$ (see @hrefterm[squash]).
   @end[doc]
>>

interactive intersectionMemberFormation2 {| intro [] |} :
    [wf] sequent [squash] { <H> >- "type"{'A} } -->
    [main] sequent ['ext] { <H>; z: squash{'A} >- 'B } -->
    sequent ['ext] { <H> >- Isect x: 'A. 'B }


doc <:doc< 
   @begin[doc]
  
   Of course $@top$ is inhabited.
   @end[doc]
>>

interactive topMemberFormation {| intro [] |} :
   sequent ['ext] { <H> >-  top }



doc <:doc< 
   @begin[doc]
   @modsubsection{Elimination}
  
   The elimination form performs instantiation of the
   intersection space.  If $a @in A$, the elimination form
   instantiates the intersection assumption $x@colon @isect{y; A; B[y]}$
   to get a proof that $x @in B[a]$.
   @end[doc]
>>
prim intersectionElimination {| elim [] |} 'H 'a :
   [wf] sequent [squash] { <H>; x: Isect y: 'A. 'B['y]; <J['x]> >- 'a in 'A } -->
   [main] ('t['x; 'z] : sequent ['ext] { <H>; x: Isect y: 'A. 'B['y]; <J['x]>; z: 'B['a] >- 'T['z] }) -->
   sequent ['ext] { <H>; x: Isect y: 'A. 'B['y]; <J['x]> >- 'T['x] } =
   't['x; 'x]

doc <:doc< @docoff >>

interactive intersectionElimination_eq 'H 'a bind{x.bind{z.'T['x;'z]}}:
   [wf] sequent [squash] { <H>; x: Isect y: 'A. 'B['y]; <J['x]> >- 'a in 'A } -->
   [main] sequent ['ext] { <H>; x: Isect y: 'A. 'B['y]; <J['x]>; z: 'B['a]; v: 'z = 'x in 'B['a] >- 'T['x;'z] } -->
   sequent ['ext] { <H>; x: Isect y: 'A. 'B['y]; <J['x]> >- 'T['x;'x] }


let intersectionEliminationT = argfunT (fun n p ->
   let n = Sequent.get_pos_hyp_num p n in
   let x = Sequent.nth_binding p n in
   let x_var = mk_var_term x in
   let args=
      try get_with_args p with
        RefineError _ -> raise (RefineError ("intersectionElimination", StringError ("arguments required")))
   in
   let (a,bind) =
      match args with
         [] -> raise (RefineError ("intersectionElimination", StringError ("arguments required"))) |
         [a] -> (a, var_subst_to_bind (Sequent.concl p) x_var) |
         [a1;a2] -> if is_xbind_term a1 then (a2,a1) else
                    if is_xbind_term a2 then (a1,a2) else
                       raise (RefineError ("intersectionElimination", StringError ("need a bind term"))) |
         _ -> raise (RefineError ("intersectionElimination", StringError ("too many arguments")))
   in
   let bind = mk_bind1_term x bind in
      intersectionElimination_eq n a bind)

let intersectionEliminationT = argfunT (fun n p ->
   let n = Sequent.get_pos_hyp_num p n in
     intersectionEliminationT n thenT thinIfThinningT [-1;n])

doc <:doc< 
   @begin[doc]
   We can derive a simpler elimination rule for the case when $B$ does not contain $x$.
   @end[doc]
>>

interactive intersectionElimination2 (*{| elim [] |}*) 'H :
   [wf] sequent [squash] { <H>; x: Isect y: 'A. 'B; <J['x]> >- squash{'A} } -->
   [main] sequent ['ext] { <H>; x: Isect y: 'A. 'B; <J['x]>; z: 'B; v: 'z = 'x in 'B >- 'T['z] } -->
   sequent ['ext] { <H>; x: Isect y: 'A. 'B; <J['x]> >- 'T['x] }

let intersectionEliminationT = argfunT (fun n p ->
   let n = Sequent.get_pos_hyp_num p n in
     (intersectionElimination2 n thenT thinIfThinningT [-1;n])
       orelseT intersectionEliminationT n)

let resource elim += (<<Isect y: 'A. 'B['y]>>, intersectionEliminationT)

doc <:doc< 
   @begin[doc]
   As a corollary of elimination rule we have that if
   two terms are equal in the intersection, they are also
   equal in each of the case of the intersection.
   @end[doc]
>>

interactive intersectionMemberCaseEquality (Isect x: 'A. 'B['x]) 'a :
   [wf] sequent [squash] { <H> >- 'b1 = 'b2 in Isect x: 'A. 'B['x] } -->
   [wf] sequent [squash] { <H> >- 'a in 'A } -->
   sequent ['ext] { <H> >- 'b1 = 'b2 in 'B['a] }


doc <:doc< @doc{The elimination form of @hrefrule[intersectionMemberCaseEquality].} >>

interactive intersectionEqualityElim {| elim [] |} 'H 'a :
   [wf] sequent[squash] { <H>; u: 'b1 = 'b2 in Isect x: 'A. 'B['x]; <J['u]> >- 'a in 'A } -->
   sequent ['ext] { <H>; u: 'b1 = 'b2 in Isect x: 'A. 'B['x]; v: 'b1 = 'b2 in 'B['a]; <J['u]> >- 'C['u] } -->
   sequent ['ext] { <H>; u: 'b1 = 'b2 in Isect x: 'A. 'B['x]; <J['u]> >- 'C['u] }

doc <:doc< @docoff >>

(* We could declare intersectionMemberCaseEquality as primitive and derive intersectionElimination *)

interactive intersectionEliminationFromCaseEquality 'H 'a :
   [wf] sequent [squash] { <H>; x: Isect y: 'A. 'B['y]; <J['x]> >- 'a in 'A } -->
   [main] sequent ['ext] { <H>; x: Isect y: 'A. 'B['y]; <J['x]>; z: 'B['a] >- 'T['z] } -->
   sequent ['ext] { <H>; x: Isect y: 'A. 'B['y]; <J['x]> >- 'T['x] }

doc <:doc< 
   @begin[doc]
   @modsubsection{Subtyping}
  
   The intersection type conforms to the subtyping properties
   of the dependent-function space.  The type is @emph{contravariant}
   in the quantified type $A$, and pointwise-covariant in the
   domain type $B[a]$ for each $a @in A$.
   @end[doc]
>>
prim intersectionSubtype {| intro [] |} :
   ["subtype"] sequent [squash] { <H> >- \subtype{'A2; 'A1} } -->
   ["subtype"] sequent [squash] { <H>; a: 'A2 >- \subtype{'B1['a]; 'B2['a]} } -->
   sequent ['ext] { <H> >- \subtype{ (Isect a1:'A1. 'B1['a1]); (Isect a2:'A2. 'B2['a2]) } } =
   it

doc <:doc< 
   @begin[doc]
   The alternate subtyping rules are for cases where one of
   the types is not an intersection.  The intersection is a subtype
   of another type $T$ if @emph{one} of the cases $B[a] @subseteq T$.
   A type $T$ is a subtype of the intersection if it is a subtype
   of @emph{every} case $B[a]$ for $a @in A$.
   @end[doc]
>>
interactive intersectionSubtype2 'a :
   [wf] sequent [squash] { <H> >- 'a = 'a in 'A } -->
   [wf] sequent [squash] { <H>; y: 'A >- "type"{'B['y]} } -->
   ["subtype"] sequent [squash] { <H> >- \subtype{'B['a]; 'T} } -->
   sequent ['ext] { <H> >- \subtype{."isect"{'A; x. 'B['x]}; 'T} }

interactive intersectionSubtype3 :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   [wf] sequent [squash] { <H> >- "type"{'C} } -->
   ["subtype"] sequent [squash] { <H>; x: 'A >- \subtype{'C; 'B['x]} } -->
   sequent ['ext] { <H> >- \subtype{'C; ."isect"{'A; x. 'B['x]}} }

doc <:doc< 
   @begin[doc]
   @noindent
   @emph{Every} type is a subtype of $@top$.
   @end[doc]
>>
interactive topSubtype {| intro [] |} :
   sequent [squash] { <H> >- "type"{'T} } -->
   sequent ['ext] { <H> >- \subtype{'T; top} }
doc <:doc< @docoff >>

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let isect_term = << Isect x: 'A. 'B['x] >>
let isect_opname = opname_of_term isect_term
let is_isect_term = is_dep0_dep1_term isect_opname
let dest_isect = dest_dep0_dep1_term isect_opname
let mk_isect_term = mk_dep0_dep1_term isect_opname

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let resource typeinf += (isect_term, infer_univ_dep0_dep1 dest_isect)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two intersection types.
 *)
let resource sub +=
   (DSubtype ([<< Isect a1:'A1. 'B1['a1] >>, << Isect a2:'A2. 'B2['a2] >>;
               << 'A2 >>, << 'A1 >>;
               << 'B1['a1] >>, << 'B2['a1] >>],
              intersectionSubtype))

let d_isect_subtypeT = argfunT (fun i p ->
   if i = 0 then
      let a = get_with_arg p in
         intersectionSubtype2 a
   else
      raise (RefineError ("d_isect_subtypeT", StringError "no elimination form")))

let isect_subtype_term = << \subtype{."isect"{'A; x. 'B['x]}; 'T} >>

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
