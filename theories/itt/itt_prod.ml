doc <:doc< 
   @spelling{dprod}
  
   @begin[doc]
   @module[Itt_prod]
  
   The product type $@prod{A; B}$ is @emph{derived} from the
   dependent production module @hrefmodule[Itt_dprod].  The
   non-dependent product $@prod{A; B}$ is equivalent to
   $@prod{x; A; B}$, where $x$ is not free in $B$.
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
extends Itt_dprod
extends Itt_struct
doc <:doc< @docoff >>

open Printf
open Lm_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError
open Mp_resource

open Var
open Tactic_type.Sequent
open Tactic_type.Tacticals

open Dtactic

open Itt_equal
open Itt_subtype
open Itt_dprod
open Itt_struct

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_prod%t"

(* debug_string DebugLoad "Loading itt_prod..." *)

doc <:doc< 
   @begin[doc]
   @rewrites
   The @tt{unfold_prod} rewrite unfolds the non-dependent
   product to a dependent-product with a @emph{new} variable
   $x$.
   @end[doc]
>>
prim_rw unfold_prod : ('A * 'B) <--> (x: 'A * 'B)

doc <:doc< 
   @begin[doc]
   @rules
   @modsubsection{Typehood and equality}
  
   The product space $@prod{A; B}$ is well-formed if
   both $A$ and $B$ are types.
   @end[doc]
>>
interactive independentProductEquality {| intro []; eqcd |} :
   [wf] sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent { <H> >- 'B1 = 'B2 in univ[i:l] } -->
   sequent { <H> >- 'A1 * 'B1 = 'A2 * 'B2 in univ[i:l] }

(*
 * Typehood.
 *)
interactive independentProductType {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A1} } -->
   [wf] sequent { <H> >- "type"{'A2} } -->
   sequent { <H> >- "type"{.'A1 * 'A2} }

(*
 * H >- Ui ext A * B
 * by independentProductFormation
 * H >- Ui ext A
 * H >- Ui ext B
 *)
interactive independentProductFormation :
   ('A : sequent { <H> >- univ[i:l] }) -->
   ('B : sequent { <H> >- univ[i:l] }) -->
   sequent { <H> >- univ[i:l] }

doc <:doc< 
   @begin[doc]
   @modsubsection{Elimination}
  
   The elimination form splits the hypothesis $x@colon @prod{A; B}$ into
   its parts $u@colon A$ and $v@colon B$.
   @end[doc]
>>
interactive independentProductElimination {| elim [ThinOption thinT] |} 'H :
   sequent { <H>; z: 'A * 'B; u: 'A; v: 'B; <J['u, 'v]> >- 'T['u, 'v] } -->
   sequent { <H>; z: 'A * 'B; <J['z]> >- 'T['z] }

doc <:doc< 
   @begin[doc]
   @modsubsection{Membership}
  
   The members of the non-dependent product $@prod{A; B}$
   are the pairs $@pair{a; b}$, where $a @in A$ and $b @in B$.
   @end[doc]
>>
interactive independentPairEquality {| intro []; eqcd |} :
   [wf] sequent { <H> >- 'a1 = 'a2 in 'A } -->
   [wf] sequent { <H> >- 'b1 = 'b2 in 'B } -->
   sequent { <H> >- ('a1, 'b1) = ('a2, 'b2) in 'A * 'B }

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction}
  
   The propositional interpretation of the
   non-dependent product space $@prod{A; B}$ is the
   conjunction $@and{A; B}$.  The proposition is
   true if both $A$ and $B$ are true.
   @end[doc]
>>
interactive independentPairFormation {| intro [] |} :
   [wf] ('a : sequent { <H> >- 'A }) -->
   [wf] ('b : sequent { <H> >- 'B }) -->
   sequent { <H> >- 'A * 'B }

doc <:doc< 
   @begin[doc]
   @modsubsection{Subtyping}
  
   The product space is covariant in both parts.
   @end[doc]
>>
interactive independentProductSubtype {| intro [] |} :
   ["subtype"] sequent { <H> >- \subtype{'A1; 'A2} } -->
   ["subtype"] sequent { <H> >- \subtype{'B1; 'B2} } -->
   sequent { <H> >- \subtype{ ('A1 * 'B1); ('A2 * 'B2) } }
doc <:doc< @docoff >>

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let resource typeinf += (prod_term, infer_univ_dep0_dep0 dest_prod)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two product types.
 *)
let resource sub +=
   (DSubtype ([<< 'A1 * 'B1 >>, << 'A2 * 'B2 >>;
               << 'A1 >>, << 'A2 >>;
               << 'B1 >>, << 'B2 >>],
              dT 0))

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
