doc <:doc<
   @module[Czf_itt_sep]

   The @tt[Czf_itt_sep] module defines @emph{restricted separation}.
   Separation is defined as a set constructor $@sep{x; s; P[x]}$.
   The term $s$ must be a set, and $P[x]$ must be a functional,
   restricted proposition.  The elements of the separation are the
   elements of $x @in s$ for which $P[x]$ is true.

   The separation constructor is a set if $s$ is a set, and
   if $P[x]$ is @emph{restricted}.  Our formalization of
   restriction differs slightly from Aczel's account, although
   both are equivalent.  In Aczel's definition, a proposition
   $P[x]$ is restricted if it contains no @emph{unbounded}
   quantifiers $@forall s@ldots$ and $@exists s@ldots$.  In
   our construction, a predicate $P$ is restricted if it
   is a well-formed proposition in $@univ{1}$.

   The separation constructor $@sep{z; @collect{x; T; f[x]}; P[z]}$
   is defined with the product type as the set
   $@collect{z; (@prod{x; A; P[x]}); f(@fst{z})}$.

   @docoff
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

doc <:doc< @parents >>
extends Czf_itt_member
doc docoff

open Lm_debug
open Lm_printf

open Dtactic
open Top_conversionals

open Itt_logic

let _ =
   show_loading "Loading Czf_itt_sep%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc< @terms >>
declare sep{'s; x. 'P['x]}
declare restricted{'P}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc<
   @rewrites

   The @tt{sep} term is defined by set induction.
>>

prim_rw unfold_sep : sep{'s; x. 'P['x]} <-->
   set_ind{'s; T, f, g. collect{."prod"{'T; t. 'P['f 't]}; z. 'f fst{'z}}}

interactive_rw reduce_sep {| reduce |} : sep{collect{'T; x. 'f['x]}; z. 'P['z]} <-->
   collect{. "prod"{'T; t. 'P['f['t]]}; w. 'f[fst{'w}]}

doc <:doc<
   The $@restricted{P}$ predicate means that the proposition is
   well-formed in $@univ{1}$.
>>
prim_rw unfold_restricted : restricted{'P} <-->
   Itt_equal!equal{univ[1:l]; 'P; 'P}

doc docoff
let fold_restricted = makeFoldC << restricted{'P} >> unfold_restricted

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform sep_df : except_mode[src] :: sep{'s; x. 'P} =
   szone pushm[3] `"{ " slot{'x} " " Nuprl_font!member `"s " slot{'s} `" |"
   hspace slot{'P} " " `"}" popm ezone

dform restricted_df : except_mode[src] :: parens :: "prec"[prec_quant] :: restricted{'P} =
   `"<" slot{'P} `">"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Squash the restricted judgment.
 *)
interactive squash_restricted :
   sequent { <H> >- restricted{'P} } -->
   sequent { <H> >- restricted{'P} }

let squash_restrictedT = squash_restricted

doc <:doc<
   @modsubsection{Equality and membership are restricted judgments}

   The next two rules show that equality and membership
   are restricted for any @hrefterm[set] arguments.
>>
interactive eq_restricted {| intro [] |} :
   ["wf"] sequent { <H> >- isset{'s1} } -->
   ["wf"] sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- restricted{eq{'s1; 's2}} }

interactive member_restricted {| intro [] |} :
   ["wf"] sequent { <H> >- isset{'s1} } -->
   ["wf"] sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- restricted{mem{'s1; 's2}} }

doc <:doc<
   @modsubsection{Well-formedness}

   The separation $@sep{x; s; P[x]}$ is well-formed
   if $s$ is a set, and $P[x]$ is restricted and functional
   on any set argument $x$.
>>
interactive sep_isset {| intro [] |} :
   ["wf"] sequent { <H> >- isset{'s} } -->
   ["wf"] sequent { <H> >- fun_prop{z. 'P['z]} } -->
   ["wf"] sequent { <H>; z: set >- restricted{'P['z]} } -->
   sequent { <H> >- isset{.sep{'s; x. 'P['x]}} }

doc <:doc<
   @modsubsection{Introduction}

   A set $x$ is a member of $@sep{z; s; P[z]}$ if
   the separation is well-formed; if $@member{x; s}$;
   and $P[x]$.
>>
interactive sep_intro2 {| intro [] |} :
   ["wf"]   sequent { <H>; w: set >- restricted{'P['w]} } -->
   ["wf"]   sequent { <H> >- fun_prop{z. 'P['z]} } -->
   ["main"] sequent { <H> >- member{'x; 's} } -->
   ["main"] sequent { <H> >- 'P['x] } -->
   sequent { <H> >- mem{'x; sep{'s; z. 'P['z]}} }

doc <:doc<
   @modsubsection{Elimination}

   An assumption $@mem{x; @sep{y; s; P[y]}}$ implies two facts:
   $@mem{x; s}$ and $P[x]$.  The computational content of the
   predicate $P[x]$ is visible (unlike the separation ``set''
   constructor in the @Nuprl type theory module @hrefmodule[Itt_set]).
>>
interactive sep_elim {| elim [] |} 'H :
   ["wf"]   sequent { <H>; w: mem{'x; sep{'s; y. 'P['y]}}; <J['w]> >- isset{'x} } -->
   ["wf"]   sequent { <H>; w: mem{'x; sep{'s; y. 'P['y]}}; <J['w]> >- isset{'s} } -->
   ["wf"]   sequent { <H>; w: mem{'x; sep{'s; y. 'P['y]}}; <J['w]>; z: set >- restricted{'P['z]} } -->
   ["wf"]   sequent { <H>; w: mem{'x; sep{'s; y. 'P['y]}}; <J['w]> >- fun_prop{z. 'P['z]} } -->
   ["main"] sequent { <H>; w: mem{'x; sep{'s; y. 'P['y]}}; <J['w]>; u: mem{'x; 's}; v: 'P['x] >- 'T['w] } -->
   sequent { <H>; w: mem{'x; sep{'s; y. 'P['y]}}; <J['w]> >- 'T['w] }

doc <:doc<
   @modsubsection{Functionality}

   The separation constructor is functional in both the
   set argument and the proposition.
>>
interactive sep_fun {| intro [] |} :
   sequent { <H>; u: set; v: set >- restricted{'P['u; 'v]} } -->
   sequent { <H>; u: set >- fun_prop{z. 'P['z; 'u]} } -->
   sequent { <H>; u: set >- fun_prop{z. 'P['u; 'z]} } -->
   sequent { <H> >- fun_set{z. 's['z]} } -->
   sequent { <H> >- fun_set{z. sep{'s['z]; x. 'P['x; 'z]}} }
doc docoff

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
