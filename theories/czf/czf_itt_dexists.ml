doc <:doc<
   @module[Czf_itt_dexists]

   The @tt{Czf_itt_dexists} theory defines @emph{restricted}
   existential quantification.  The syntax of the operator
   is $@dexists{x; s; P[x]}$, where $s$ is a set, and $P[x]$
   is a functional proposition for any set argument $x$.
   The proposition is true if $P[a]$ is true for @emph{some} element
   $@mem{a; s}$.

   The restricted universal quantification is coded as
   an implication on the elements of $s$.

   $$@dexists{x; @collect{y; T; f[y]}; P[x]} @equiv @prod{x; T; P[x]}$$

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

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
extends Czf_itt_sep
extends Czf_itt_set_ind
doc docoff

open Lm_debug
open Lm_printf

open Dtactic
open Top_conversionals

open Itt_dfun

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc terms
declare "dexists"{'T; x. 'A['x]}
doc docoff

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc<
   @rewrites

   The existential is defined by set induction on the set
   argument as a dependent product type.
>>
prim_rw unfold_dexists : "dexists"{'s; x. 'A['x]} <-->
   set_ind{'s; T, f, g. x: 'T * 'A['f 'x]}

interactive_rw reduce_dexists {| reduce |} : "dexists"{collect{'T; x. 'f['x]}; y. 'A['y]} <-->
   (t: 'T * 'A['f['t]])
doc docoff

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform dexists_df : parens :: "prec"[prec_lambda] :: "dexists"{'s; x. 'A} =
   pushm[0] Mpsymbols!"exists" slot{'x} " " Mpsymbols!member `"s " slot{'s} `"." slot{'A} popm

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @rules
   @modsubsection{Well-formedness}

   The proposition $@dexists{x; s; P[x]}$ is well-formed
   if $s$ is a set, and $P[x]$ is a well-formed proposition
   for @emph{any} set argument $x$.
>>
interactive dexists_type {| intro [] |} :
   ["wf"] sequent { <H> >- isset{'s} } -->
   ["wf"] sequent { <H>; y: set >- "type"{'A['y]} } -->
   sequent { <H> >- "type"{."dexists"{'s; x. 'A['x]}} }

doc <:doc<
   @modsubsection{Introduction}

   The existential $@dexists{x; s; P[x]}$ is true if
   it is well-formed and if $P[a]$ is true for some
   element $@mem{a; s}$.
>>
interactive dexists_intro {| intro [] |} 'z :
   ["wf"] sequent { <H>; w: set >- "type"{'A['w]} } -->
   ["wf"] sequent { <H> >- fun_prop{x. 'A['x]} } -->
   ["main"] sequent { <H> >- member{'z; 's} } -->
   ["antecedent"] sequent { <H> >- 'A['z] } -->
   sequent { <H> >- "dexists"{'s; x. 'A['x]} }

doc <:doc<
   @modsubsection{Elimination}

   The proof of the existential $@dexists{x; s; P[x]}$ has two parts:
   an element $@mem{a; s}$, and a proof $P[a]$.  The elimination form
   produces these parts.
>>
interactive dexists_elim {| elim [] |} 'H :
   ["wf"] sequent { <H>; x: "dexists"{'s; y. 'A['y]}; <J['x]> >- isset{'s} } -->
   ["wf"] sequent { <H>; x: "dexists"{'s; y. 'A['y]}; <J['x]>; z: set >- "type"{'A['z]} } -->
   ["wf"] sequent { <H>; x: "dexists"{'s; y. 'A['y]}; <J['x]> >- fun_prop{z. 'A['z]} } -->
   ["main"] sequent { <H>;
                    x: "dexists"{'s; y. 'A['y]};
                    <J['x]>;
                    z: set;
                    v: mem{'z; 's};
                    w: 'A['z]
                    >- 'C['x]
                  } -->
   sequent { <H>; x: "dexists"{'s; y. 'A['y]}; <J['x]> >- 'C['x] }

doc <:doc<
   @modsubsection{Functionality}

   The existential is functional in both its set and proposition
   arguments.
>>
interactive dexists_fun {| intro [] |} :
   sequent { <H> >- fun_set{z. 'A['z]} } -->
   sequent { <H>; z: set >- fun_prop{x. 'B['z; 'x]} } -->
   sequent { <H>; z: set >- fun_prop{x. 'B['x; 'z]} } -->
   ["wf"] sequent { <H>; z: set; x: set >- "type"{'B['z; 'x]} } -->
   sequent { <H> >- fun_prop{z. "dexists"{'A['z]; y. 'B['z; 'y]}} }

doc <:doc<
   @modsubsection{Restriction}

   The existential is a restricted formula because it is
   a quantification over the @emph{index} type of the set
   argument.
>>
interactive dexists_res2 {| intro [] |} :
   ["wf"]   sequent { <H> >- isset{'A} } -->
   sequent { <H>; u: set >- restricted{'B['u]} } -->
   sequent { <H> >- restricted{."dexists"{'A; y. 'B['y]}} }
doc docoff

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
