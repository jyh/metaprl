doc <:doc< 
   @spelling{group_bvd}
  
   @begin[doc]
   @module[Czf_itt_group_bvd]
  
   The @tt{Czf_itt_group_bvd} module defines the @emph{group builder}
   which builds a new group $g_1$ from an existing group $g_2$ which
   shares the same operation, but has a different carrier which must
   be a subset of the underlying set of $g_2$. The same operation
   requires that $a *_1 b$ is equal to $a *_2 b$ for any $a$ and $b$
   in $g_1$. Examples of use of @tt[group_bvd] are subgroups, kernels,
   cyclic subgroups, etc.
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
extends Czf_itt_subset
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
   show_loading "Loading Czf_itt_group_bvd%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc< @doc{@terms} >>
declare group_bvd{'h; 'g; 's}
doc <:doc< @docoff >>

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @rewrites
  
   The $@groupbvd{h; g; s}$ builds a group $h$ from group $g$ which
   satisfies $@equal{@car{h}; s}$ and the operation of $h$ is the
   same as that of $g$. Here $s$ must be a subset of $@car{g}$
   @end[doc]
>>
prim_rw unfold_group_bvd : group_bvd{'h; 'g; 's} <-->
   (group{'h} & group{'g} & isset{'s} & \subset{'s; car{'g}} & equal{car{'h}; 's} & (all a: set. all b: set. (mem{'a; car{'h}} => mem{'b; car{'h}} => eq{op{'h; 'a; 'b}; op{'g; 'a; 'b}})))
doc <:doc< @docoff >>

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform group_bvd_df : parens :: except_mode[src] :: group_bvd{'h; 'g; 's} =
   `"group_builder(" slot{'h} `"; " slot{'g} `"; " slot{'s} `")"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @rules
   @modsubsection{Well-formedness}
  
   The group builder $@groupbvd{h; g; s}$ is well-formed
   if $h$ and $g$ are labels and $s$ is a set.
   @end[doc]
>>
interactive group_bvd_wf {| intro [] |} :
   sequent [squash] { <H> >- 'h IN label } -->
   sequent [squash] { <H> >- 'g IN label } -->
   sequent [squash] { <H> >- isset{'s} } -->
   sequent ['ext] { <H> >- "type"{group_bvd{'h; 'g; 's}} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction}
  
   The proposition $@groupbvd{h; g; s}$ is true if it is
   well-formed; if $h$ and $g$ are both groups; if
   $@equal{@car{h}; s}$; and if for any $a$ and $b$ $@in$
   $@car{h}$, $@op{h; a; b}$ is equal to $@op{g; a; b}$.
   @end[doc]
>>
interactive group_bvd_intro {| intro [] |} :
   sequent [squash] { <H> >- 'h IN label } -->
   sequent [squash] { <H> >- 'g IN label } -->
   sequent [squash] { <H> >- isset{'s} } -->
   sequent ['ext] { <H> >- group{'h} } -->
   sequent ['ext] { <H> >- group{'g} } -->
   sequent ['ext] { <H> >- \subset{'s; car{'g}} } -->
   sequent ['ext] { <H> >- equal{car{'h}; 's} } -->
   sequent ['ext] { <H>; a: set; b: set; x: mem{'a; car{'h}}; y: mem{'b; car{'h}} >- eq{op{'h; 'a; 'b}; op{'g; 'a; 'b}} } -->
   sequent ['ext] { <H> >- group_bvd{'h; 'g; 's} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Properties}
  
   If $h$ is built from $g$, then $@eq{@id{h}; @id{g}}$ and
   for all $a @in @car{h}$, $@eq{@inv{h; a}; @inv{g; a}}$.
   @end[doc]
>>
interactive group_bvd_id {| intro [] |} 's :
   sequent [squash] { <H> >- 'h IN label } -->
   sequent [squash] { <H> >- 'g IN label } -->
   sequent [squash] { <H> >- isset{'s} } -->
   sequent ['ext] { <H> >- group_bvd{'h; 'g; 's} } -->
   sequent ['ext] { <H> >- eq{id{'h}; id{'g}} }

interactive group_bvd_inv {| intro [] |} 's :
   sequent [squash] { <H> >- 'h IN label } -->
   sequent [squash] { <H> >- 'g IN label } -->
   sequent [squash] { <H> >- isset{'s} } -->
   sequent [squash] { <H> >- isset{'a} } -->
   sequent ['ext] { <H> >- group_bvd{'h; 'g; 's} } -->
   sequent ['ext] { <H> >- mem{'a; car{'h}} } -->
   sequent ['ext] { <H> >- eq{inv{'h; 'a}; inv{'g; 'a}} }

doc <:doc< @docoff >>
(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
