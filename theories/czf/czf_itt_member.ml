doc <:doc< 
   @begin[doc]
   @module[Czf_itt_member]
  
   The @tt{Czf_itt_member} module defines membership in a set.
   The basic definition is an existential judgment: a set $s$
   is an element of a set $@collect{x; T; f[x]}$ if there is
   some element $a@colon T$ and $@eq{s; f[a]}$.
  
   Note that equality has to be defined @emph{before} membership.
   We also prove the @emph{extensionality} judgment here; two sets
   are equal if they have the same members.
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
  
   @begin[spelling]
   memberOfT setExtT setOfT
   @end[spelling]
>>

doc <:doc< 
   @begin[doc]
   @parents
   @end[doc]
>>
extends Czf_itt_eq
doc <:doc< @docoff >>

open Refiner.Refiner.Term
open Refiner.Refiner.RefineError

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Tactic_type.Sequent
open Var

open Base_dtactic

open Itt_rfun
open Itt_logic

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @terms
  
   The @tt{member} term defines the membership judgment.
   @end[doc]
>>
declare mem{'x; 'y}
declare member{'x; 'y}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @rewrites
  
   The @tt{member} judgment is defined using the @hrefterm[set_ind]
   induction combinator.
   @end[doc]
>>
prim_rw unfold_mem : mem{'x; 'y} <-->
   set_ind{'y; T, f, g. exst t: 'T. eq{'x; .'f 't}}

interactive_rw reduce_mem : mem{'x; collect{'T; y. 'f['y]}} <-->
   (exst t: 'T. eq{'x; .'f['t]})

doc <:doc< @docoff >>
let resource reduce += << mem{'x; collect{'T; y. 'f['y]}} >>, reduce_mem

doc <:doc< @doc{nil} >>
prim_rw unfold_member : member{'x; 'y} <-->
   ((isset{'x} & isset{'y}) & mem{'x; 'y})

interactive_rw reduce_member : member{'x; collect{'T; y. 'f['y]}} <-->
   ((isset{'x} & isset{collect{'T; y. 'f['y]}}) & (exst t: 'T. eq{'x; .'f['t]}))
doc <:doc< @docoff >>

let resource reduce += << member{'x; collect{'T; y. 'f['y]}} >>, reduce_member

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform mem_df : except_mode[src] :: parens :: "prec"[prec_apply] :: mem{'x; 't} =
   slot{'x} " " Nuprl_font!member `"s" " " slot{'t}

dform member_df : except_mode[src] :: parens :: "prec"[prec_apply] :: member{'x; 't} =
   slot{'x} " " Nuprl_font!member `"S" " " slot{'t}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @rules
   @modsubsection{Well-formedness}
  
   The @tt{member} judgment is well-formed if-and-only-if its arguments are
   sets.
   @end[doc]
>>
interactive mem_type {| intro [] |} :
   ["wf"] sequent [squash] { 'H >- isset{'s1} } -->
   ["wf"] sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- "type"{mem{'s1; 's2}} }

interactive mem_equal {| intro [] |} :
   ["wf"] sequent [squash] { 'H >- isset{'s1} } -->
   ["wf"] sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- Itt_equal!equal{univ[1:l]; mem{'s1; 's2}; mem{'s1; 's2}} }

(*
 * Introduction.
 *)
interactive member_intro {| intro [] |} :
   ["wf"] sequent [squash] { 'H >- isset{'s1} } -->
   ["wf"] sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- mem{'s1; 's2} } -->
   sequent ['ext] { 'H >- member{'s1; 's2} }

(*
 * Sets contain only sets.
 *)
interactive elem_isset 'y :
   sequent ['ext] { 'H >- member{'x; 'y} } -->
   sequent ['ext] { 'H >- isset{'x} }

(*
 * Only sets have elements.
 *)
interactive set_isset 'x :
   sequent ['ext] { 'H >- member{'x; 'y} } -->
   sequent ['ext] { 'H >- isset{'y} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Functionality}
   The @tt{member} judgment is functional in both its arguments.
   The next two rules provide simple functionality judgments
   for the two set arguments.
   @end[doc]
>>
interactive mem_fun_left 's1 :
   ["wf"] sequent [squash] { 'H >- isset{'s1} } -->
   ["wf"] sequent [squash] { 'H >- isset{'s2} } -->
   ["wf"] sequent [squash] { 'H >- isset{'s3} } -->
   sequent ['ext] { 'H >- eq{'s1; 's2} } -->
   sequent ['ext] { 'H >- mem{'s1; 's3} } -->
   sequent ['ext] { 'H >- mem{'s2; 's3} }
doc <:doc< @docoff >>

let memSubstLeftT = mem_fun_left

doc <:doc< @doc{nil} >>
interactive mem_fun_right 's1 :
   ["wf"] sequent [squash] { 'H >- isset{'s1} } -->
   ["wf"] sequent [squash] { 'H >- isset{'s2} } -->
   ["wf"] sequent [squash] { 'H >- isset{'s3} } -->
   sequent ['ext] { 'H >- eq{'s1; 's2} } -->
   sequent ['ext] { 'H >- mem{'s3; 's1} } -->
   sequent ['ext] { 'H >- mem{'s3; 's2} }
doc <:doc< @docoff >>

let memSubstRightT = mem_fun_right

doc <:doc< 
   @begin[doc]
   The @tt{member_fun} rule proves the general functionality
   judgment.
   @end[doc]
>>
interactive member_fun {| intro [] |} :
   sequent ['ext] { 'H >- fun_set{z. 'f1['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. 'f2['z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. mem{'f1['z]; 'f2['z]}} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Set extensionality}
  
   Two sets are equal if-and-only-if they have the same elements.
   The proof of this theorem is straightforward.  The two membership
   goals are the functions that ``choose,'' for any element of
   one set, an equal element in the other set.  The equality judgment
   can be proved with the pair of both choice functions.
   @end[doc]
>>
interactive set_ext :
   ["wf"] sequent ['ext] { 'H >- isset{'s1} } -->
   ["wf"] sequent ['ext] { 'H >- isset{'s2} } -->
   ["main"] sequent ['ext] { 'H; x: set; y: mem{'x; 's1} >- mem{'x; 's2} } -->
   ["main"] sequent ['ext] { 'H; x: set; y: mem{'x; 's2} >- mem{'x; 's1} } -->
   sequent ['ext] { 'H >- eq{'s1; 's2} }
doc <:doc< @docoff >>

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @tactics
  
   @begin[description]
   @item{@tactic[memberOfT], @tactic[setOfT];
     The @tt{memberOfT} applies the @hrefrule[elem_isset] rule, and
     the @tt{setOfT} tactic applies the @hrefrule[set_isset] rule.
     Both tactics infer the well-formedness of a set for a membership
     or equality judgment.}
   @end[description]
   @docoff
   @end[doc]
>>
let memberOfT = elem_isset
let setOfT = set_isset

doc <:doc< 
   @begin[doc]
   @begin[description]
   @item{@tactic[setExtT];
      The @tt{setExtT} tactic refines a set-equality
      goal using the rule of @emph{extensionality} @hrefrule[set_ext].
      This rule is not added to the @hreftactic[dT] tactic for default
      reasoning because in many cases, equality judgments can be proved
      in simpler ways.}
   @end[description]
   @docoff
   @end[doc]
>>
let setExtT = set_ext

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
