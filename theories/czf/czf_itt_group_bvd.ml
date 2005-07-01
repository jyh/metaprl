doc <:doc<
   @begin[doc]
   @module[Czf_itt_group_bvd]

   The @tt[Czf_itt_group_bvd] module defines the @emph{group builder}
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
doc docoff

open Lm_debug
open Lm_printf

open Dtactic

let _ =
   show_loading "Loading Czf_itt_group_bvd%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc< @doc{@terms} >>
declare group_bvd{'h; 'g; 's}
doc docoff

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
doc docoff

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
   sequent { <H> >- 'h IN label } -->
   sequent { <H> >- 'g IN label } -->
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- "type"{group_bvd{'h; 'g; 's}} }

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
   sequent { <H> >- 'h IN label } -->
   sequent { <H> >- 'g IN label } -->
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- group{'h} } -->
   sequent { <H> >- group{'g} } -->
   sequent { <H> >- \subset{'s; car{'g}} } -->
   sequent { <H> >- equal{car{'h}; 's} } -->
   sequent { <H>; a: set; b: set; x: mem{'a; car{'h}}; y: mem{'b; car{'h}} >- eq{op{'h; 'a; 'b}; op{'g; 'a; 'b}} } -->
   sequent { <H> >- group_bvd{'h; 'g; 's} }

doc <:doc<
   @begin[doc]
   @modsubsection{Properties}

   If $h$ is built from $g$, then $@eq{@id{h}; @id{g}}$ and
   for all $a @in @car{h}$, $@eq{@inv{h; a}; @inv{g; a}}$.
   @end[doc]
>>
interactive group_bvd_id {| intro [] |} 's :
   sequent { <H> >- 'h IN label } -->
   sequent { <H> >- 'g IN label } -->
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- group_bvd{'h; 'g; 's} } -->
   sequent { <H> >- eq{id{'h}; id{'g}} }

interactive group_bvd_inv {| intro [] |} 's :
   sequent { <H> >- 'h IN label } -->
   sequent { <H> >- 'g IN label } -->
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- group_bvd{'h; 'g; 's} } -->
   sequent { <H> >- mem{'a; car{'h}} } -->
   sequent { <H> >- eq{inv{'h; 'a}; inv{'g; 'a}} }

doc docoff
(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
