doc <:doc<
   @module[Czf_itt_set_bvd]

   The @tt[Czf_itt_set_bvd] module defines the @emph{image} of a set
   under some mapping. Image is defined as a set constructor
   $@setbvd{x; s; a[x]}$, which builds a new set from an existing
   set $s$ via some mapping $a[x]$. A set $x$ is a member of
   $@setbvd{x; s; a[x]}$ if there exists a set $y @in s$ such
   that $@eq{x; a[y]}$ is true.

   The image constructor $@setbvd{z; @collect{x; T; f[x]}; a[z]}$
   is defined as the set $@collect{y; T; a[f(y)]}$.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

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


extends Czf_itt_dall
extends Czf_itt_dexists
doc docoff

open Lm_debug
open Lm_printf

open Dtactic
open Top_conversionals

let _ =
   show_loading "Loading Czf_itt_set_bvd%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)


declare set_bvd{'s; x. 'a['x]}            (* { a(x) | x in s } *)
doc docoff

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc<
   @rewrites

   The @tt{set_bvd} term is defined by set induction.
>>
prim_rw unfold_set_bvd: set_bvd{'s; x. 'a['x]} <-->
   set_ind{'s; t, f, g. collect{'t; y. 'a['f 'y]}}

interactive_rw reduce_set_bvd {| reduce |} :
   set_bvd{collect{'T; x. 'f['x]}; x. 'a['x]} <-->
   collect{'T; y. 'a['f['y]]}
doc docoff

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform set_bvd_df : parens :: except_mode[src] :: set_bvd{'s; x. 'a} =
   pushm[0] `"{" slot{'a} mid slot{'x} " " Mpsymbols!member `"s " slot{'s} `"}" popm

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @rules
   @modsubsection{Well-formedness}

   The set builder $@setbvd{x; s; a[x]}$ is well-formed
   if $s$ is a set, and $a[x]$ is a family of sets.
>>
interactive set_bvd_isset {| intro [] |} :
   sequent { <H> >- isset{'s} } -->
   sequent { <H>; x: set >- isset{'a['x]} } -->
   sequent { <H> >- isset{set_bvd{'s; x. 'a['x]}} }

doc <:doc<
   @modsubsection{Introduction}

   A set $y$ is a member of $@setbvd{x; s; a[x]}$
   if the set builder is well-formed; if $a[x]$ is
   functional on any set argument $x$; and if
   $@dexists{z; s; @eq{y; a[z]}}$.
>>
interactive set_bvd_member_intro {| intro [] |} :
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- isset{'y} } -->
   sequent { <H>; x: set >- isset{'a['x]} } -->
   sequent { <H> >- fun_set{x. 'a['x]} } -->
   sequent { <H> >- dexists{'s; z. eq{'y; 'a['z]}} } -->
   sequent { <H> >- mem{'y; set_bvd{'s; x. 'a['x]}} }

doc <:doc<
   @modsubsection{Elimination}

   The elimination form for the set builder $@mem{y; @setbvd{x; s; a[x]}}$
   produces a witness $@mem{z; s}$ for which $@eq{y; a[z]}$.
>>
interactive set_bvd_member_elim {| elim [] |} 'H :
   sequent { <H>; x: mem{'y; set_bvd{'s; x. 'a['x]}}; <J['x]> >- isset{'y} } -->
   sequent { <H>; x: mem{'y; set_bvd{'s; x. 'a['x]}}; <J['x]> >- isset{'s} } -->
   sequent { <H>; x: mem{'y; set_bvd{'s; x. 'a['x]}}; <J['x]>; z: set >- isset{'a['z]} } -->
   sequent { <H>; x: mem{'y; set_bvd{'s; x. 'a['x]}}; <J['x]> >- fun_set{x. 'a['x]} } -->
   sequent { <H>; x: mem{'y; set_bvd{'s; x. 'a['x]}}; <J['x]>; z: set; u: mem{'z; 's}; v: eq{'y; 'a['z]} >- 'T['x] } -->
   sequent { <H>; x: mem{'y; set_bvd{'s; x. 'a['x]}}; <J['x]> >- 'T['x] }

doc <:doc<
   @modsubsection{Functionality}

   The image constructor is functional in both the set
   argument and the mapping.
>>
interactive set_bvd_fun {| intro [] |} :
   sequent { <H> >- fun_set{z. 'A['z]} } -->
   sequent { <H>; z: set >- fun_set{x. 'B['z; 'x]} } -->
   sequent { <H>; z: set >- fun_set{x. 'B['x; 'z]} } -->
   ["wf"] sequent { <H>; z: set; x: set >- isset{'B['z; 'x]} } -->
   sequent { <H> >- fun_set{z. set_bvd{'A['z]; y. 'B['z; 'y]}} }
doc docoff

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
