doc <:doc< 
   @begin[doc]
   @module[Czf_itt_hom]
  
   The @tt[Czf_itt_hom] module defines the @emph{homomorphism}.
   A homomorphism is a mapping $f$ from one group $g_1$ into another
   group $g_2$, which satisfies for any $a$ and $b$ in $@car{g_1}$,
   $$f(a *_1 b) = f(a) *_2 f(b)$$
  
   $f$ is a mapping from group $g_1$ into group $g_2$ means: first,
   for any $a$ in $@car{g_1}$, $f(a)$ is in $@car{g_2}$; second,
   for each $a$ in $@car{g_1}$, @emph{exactly} one element is
   assigned in $@car{g_2}$.
  
   The homomorphism is defined as follows:
  
   $$
   @begin[array, l]
   @line{@item{@hom{x; g_1; g_2; f[x]} @equiv}}
   @line{@item{@space @space @space
     @space @group{g_1}}}
   @line{@item{@space @space @space
     @wedge @group{g_2}}}
   @line{@item{@space @space @space
     @wedge @forall a@colon @set. (@mem{a; @car{g_1}} @Rightarrow @mem{f[a]; @car{g_2}})}}
   @line{@item{@space @space @space
     @wedge @forall a@colon @set. @forall b@colon @set. (@mem{a; @car{g_1}} @Rightarrow @mem{b; @car{g_1}}}}
   @line{@item{@space @space @space @space @space @space @space @space
   @Rightarrow @eq{a; b} @Rightarrow @eq{f[a]; f[b]})}}
   @line{@item{@space @space @space
     @wedge @forall a@colon @set. @forall b@colon @set. (@mem{a; @car{g_1}} @Rightarrow @mem{b; @car{g_1}}}}
   @line{@item{@space @space @space @space @space @space @space @space
   @Rightarrow @eq{f[@op{g_{1}; a; b}]; @op{g_{2}; f[a]; f[b]}})}}
   @end[array]
   $$
  
   @end[doc]
  
   ----------------------------------------------------------------
  
   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.
  
   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.
  
   Copyright (C) 2002 Xin Yu, Caltech
  
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
  
   Author: Xin Yu
   @email{xiny@cs.caltech.edu}
   @end[license]
>>

doc <:doc< @doc{@parents} >>
extends Czf_itt_group
extends Czf_itt_subgroup
extends Czf_itt_abel_group
extends Czf_itt_inv_image
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

let _ =
   show_loading "Loading Czf_itt_hom%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc< @doc{@terms} >>
declare hom{'g1; 'g2; x. 'f['x]}
doc <:doc< @docoff >>

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @rewrites
   The @tt[hom] judgment requires that $g_1$ and $g_2$ be
   groups, $f$ be a mapping from $@car{g_1}$ into $@car{g_2}$,
   and for any $a$ and $b$ in $@car{g_1}$, $f$ map
   $@op{g_{1}; a; b}$ into $@op{g_{2}; f[a]; f[b]}$.
   @end[doc]
>>
prim_rw unfold_hom : hom{'g1; 'g2; x. 'f['x]} <-->
   (group{'g1} & group{'g2} & (all a: set. (mem{'a; car{'g1}} => member{'f['a]; car{'g2}})) & (all a: set. all b: set. (mem{'a; car{'g1}} => mem{'b; car{'g1}} => eq{'a; 'b} => eq{'f['a]; 'f['b]})) & (all a: set. all b: set. (mem{'a; car{'g1}} => mem{'b; car{'g1}} => eq{'f[op{'g1; 'a; 'b}]; op{'g2; 'f['a]; 'f['b]}})))
doc <:doc< @docoff >>

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform hom_df : parens :: except_mode[src] :: hom{'g1; 'g2; x. 'f} =
   `"hom(" slot{'g1} `"; " slot{'g2} `"; " slot{'f} `")"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @rules
   @modsubsection{Well-formedness}
  
   The @tt[hom] is well-formed if $g1$ and $g2$ are labels,
   and $f[x]$ is a set for any set argument $x$.
   @end[doc]
>>
interactive hom_type {| intro [] |} :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent [squash] { 'H; x: set >- isset{'f['x]} } -->
   sequent ['ext] { 'H >- "type"{hom{'g1; 'g2; x. 'f['x]}} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction}
  
   The proposition $@hom{x; g1; g2; f[x]}$ is true if it
   is well-formed, $g1$ and $g2$ are groups, $f$ assigns
   to each element $x$ of $@car{g_1}$ exactly one element
   $b$ of $@car{g_2}$, and $f$ maps $@op{g_{1}; a; b}$
   into $@op{g_{2}; f[a]; f[b]}$ for any $a$ and $b$ in
   $@car{g_1}$.
   @end[doc]
>>
interactive hom_intro {| intro [] |} :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent ['ext] { 'H >- group{'g1} } -->
   sequent ['ext] { 'H >- group{'g2} } -->
   sequent ['ext] { 'H; x: set; y: mem{'x; car{'g1}} >- member{'f['x]; car{'g2}} } -->
   sequent ['ext] { 'H; c: set; d: set; x1: mem{'c; car{'g1}}; y1: mem{'d; car{'g1}}; u: eq{'c; 'd} >- eq{'f['c]; 'f['d]} } -->
   sequent ['ext] { 'H; e: set; g: set; x2: mem{'e; car{'g1}}; y2: mem{'g; car{'g1}} >- eq{'f[op{'g1; 'e; 'g}]; op{'g2; 'f['e]; 'f['g]}} } -->
   sequent ['ext] { 'H >- hom{'g1; 'g2; x. 'f['x]} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Functionality}
  
   The @tt[hom] judgment is functional in the function
   argument.
   @end[doc]
>>
interactive hom_fun {| intro [] |} :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent ['ext] { 'H >- group{'g1} } -->
   sequent ['ext] { 'H >- group{'g2} } -->
   sequent ['ext] { 'H; z: set; x1: set; y1: mem{'x1; car{'g1}} >- mem{'f['z; 'x1]; car{'g2}} } -->
   sequent ['ext] { 'H; z: set >- fun_set{x. 'f['x; 'z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. hom{'g1; 'g2; y. 'f['z; 'y]}} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Trivial homomorphism}
  
   For any groups $g_1$ and $g_2$, there is always at least
   one homomorphism $f@colon g_1 @rightarrow g_2$ which
   maps all elements of $@car{g_1}$ into $@id{g_2}$. This
   is called the trivial homomorphism.
   @end[doc]
>>
interactive trivial_hom1 :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent ['ext] { 'H >- group{'g1} } -->
   sequent ['ext] { 'H >- group{'g2} } -->
   sequent ['ext] { 'H; x: set; y: mem{'x; car{'g1}} >- equal{'f['x]; id{'g2}} } -->
   sequent ['ext] { 'H >- hom{'g1; 'g2; x. 'f['x]} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Theorems}
  
   Let $f@colon g_1 @rightarrow g_2$ be a group
   homomorphism of $g_1$ into $g_2$.
  
   $@space @space$
  
   If $f$ is @emph{onto}, then $g_1$ is abelian
   implies $g_2$ is abelian.
   @end[doc]
>>
(*doc <:doc< 
   @begin[doc]
  
   If $f$ is @emph{onto}, then $g_1$ is abelian
   implies $g_2$ is abelian.
   @end[doc]
  )*)
interactive hom_abel hom{'g1; 'g2; x. 'f['x]} :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent ['ext] { 'H; x: set; y: mem{'x; car{'g2}} >- exst z: set. (mem{'z; car{'g1}} & eq{'x; 'f['z]}) } -->
   sequent ['ext] { 'H >- hom{'g1; 'g2; x. 'f['x]} } -->
   sequent ['ext] { 'H >- abel{'g1} } -->
   sequent ['ext] { 'H >- abel{'g2} }
doc <:doc< @docoff >>

interactive hom_id {| intro [] |} hom{'g1; 'g2; x. 'f['x]} :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent ['ext] { 'H >- hom{'g1; 'g2; x. 'f['x]} } -->
   sequent ['ext] { 'H >- eq{'f[id{'g1}]; id{'g2}} }

doc <:doc< 
   @begin[doc]
  
     $f$ maps the identity of $g_1$ into the identity of $g_2$.
   @end[doc]
>>
interactive hom_id_elim (*{| elim [] |}*) 'H :
   sequent [squash] { 'H; u: hom{'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g1 IN label } -->
   sequent [squash] { 'H; u: hom{'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g2 IN label } -->
   sequent ['ext] { 'H; u: hom{'g1; 'g2; x. 'f['x]}; 'J['u]; v: eq{'f[id{'g1}]; id{'g2}} >- 'C['u] } -->
   sequent ['ext] { 'H; u: hom{'g1; 'g2; x. 'f['x]}; 'J['u] >- 'C['u] }
doc <:doc< @docoff >>

interactive hom_inv {| intro [] |} 'a hom{'g1; 'g2; x. 'f['x]} :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent ['ext] { 'H >- hom{'g1; 'g2; x. 'f['x]} } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g1}} } -->
   sequent ['ext] { 'H >- eq{'f[inv{'g1; 'a}]; inv{'g2; 'f['a]}} }

doc <:doc< 
   @begin[doc]
  
     $f$ maps the inverse of an element $a$ in $@car{g_1}$ into
     the inverse of $f[a]$ in $@car{g_2}$.
   @end[doc]
>>
interactive hom_inv_elim (*{| elim [] |}*) 'H 'a :
   sequent [squash] { 'H; u: hom{'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g1 IN label } -->
   sequent [squash] { 'H; u: hom{'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g2 IN label } -->
   sequent ['ext] { 'H >- hom{'g1; 'g2; x. 'f['x]} } -->
   sequent [squash] { 'H; u: hom{'g1; 'g2; x. 'f['x]}; 'J['u] >- isset{'a} } -->
   sequent ['ext] { 'H; u: hom{'g1; 'g2; x. 'f['x]}; 'J['u] >- mem{'a; car{'g1}} } -->
   sequent ['ext] { 'H; u: hom{'g1; 'g2; x. 'f['x]}; 'J['u]; v: eq{'f[inv{'g1; 'a}]; inv{'g2; 'f['a]}} >- 'C['u] } -->
   sequent ['ext] { 'H; u: hom{'g1; 'g2; x. 'f['x]}; 'J['u] >- 'C['u] }

doc <:doc< 
   @begin[doc]
  
     If $h$ is a subgroup of $g_1$, then the image of $h$ under
     $f$ is a subgroup of $g_2$.
   @end[doc]
>>
(*
 * Let f: G -> G' be a group homomorphism of G into G'.
 * If H is a subgroup of G, then f[H] is a subgroup of G'.
 *)
interactive hom_subg1 hom{'g1; 'g2; x. 'f['x]} 'h1 'h2 :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent [squash] { 'H >- 'h1 IN label } -->
   sequent [squash] { 'H >- 'h2 IN label } -->
   sequent ['ext] { 'H >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H >- hom{'g1; 'g2; x. 'f['x]} } -->
   sequent ['ext] { 'H >- subgroup{'h1; 'g1} } -->
   sequent ['ext] { 'H >- group{'h2} } -->
   sequent ['ext] { 'H >- equal{car{'h2}; sep{car{'g2}; x. "dexists"{car{'h1}; y. eq{'x; 'f['y]}}}} } -->
   sequent ['ext] { 'H; a: set; b: set; x: mem{'a; car{'h2}}; y: mem{'b; car{'h2}} >- eq{op{'h2; 'a; 'b}; op{'g2; 'a; 'b}} } -->
   sequent ['ext] { 'H >- subgroup{'h2; 'g2} }

doc <:doc< 
   @begin[doc]
  
     If $k$ is a subgroup of $g_2$, then the inverse image of
     $k$ under $f$ is a subgroup of $g_1$.
   @end[doc]
>>
(*
 * Let f: G -> G' be a group homomorphism of G into G'.
 * If H is a subgroup of G', then the inverse image of
 * H is a subgroup of G.
 *)
interactive hom_subg2 hom{'g1; 'g2; x. 'f['x]} 'h1 'h2 :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent [squash] { 'H >- 'h1 IN label } -->
   sequent [squash] { 'H >- 'h2 IN label } -->
   sequent ['ext] { 'H >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H >- hom{'g1; 'g2; x. 'f['x]} } -->
   sequent ['ext] { 'H >- subgroup{'h2; 'g2} } -->
   sequent ['ext] { 'H >- group{'h1} } -->
   sequent ['ext] { 'H >- equal{car{'h1}; inv_image{car{'g1}; x. 'f['x]; car{'h2}}} } -->
   sequent ['ext] { 'H; a: set; b: set; x: mem{'a; car{'h1}}; y: mem{'b; car{'h1}} >- eq{op{'h1; 'a; 'b}; op{'g1; 'a; 'b}} } -->
   sequent ['ext] { 'H >- subgroup{'h1; 'g1} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @tactics
  
   @begin[description]
   @item{@tactic[homIdT], @tactic[homInvT];
      The @tt[homIdT] applies the @hrefrule[hom_id_elim] rule, and
      the @tt[homInvT] tactic applies the @hrefrule[hom_inv_elim]
      rule. They infer the mapping relations of the identity and
      inverse between two groups under a homomorphism.}
   @end[description]
   @docoff
   @end[doc]
>>
let homIdT i p =
   hom_id_elim (Sequent.get_pos_hyp_num p i) p

let homInvT t i p =
   hom_inv_elim (Sequent.get_pos_hyp_num p i) t p

doc <:doc< @docoff >>
(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
