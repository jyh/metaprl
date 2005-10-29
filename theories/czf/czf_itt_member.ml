doc <:doc<
   @module[Czf_itt_member]

   The @tt[Czf_itt_member] module defines membership in a set.
   The basic definition is an existential judgment: a set $s$
   is an element of a set $@collect{x; T; f[x]}$ if there is
   some element $a@colon T$ and $@eq{s; f[a]}$.

   Note that equality has to be defined @emph{before} membership.
   We also prove the @emph{extensionality} judgment here; two sets
   are equal if they have the same members.

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
extends Czf_itt_eq
doc docoff

open Dtactic
open Top_conversionals

open Itt_dfun

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc<
   @terms

   The @tt{member} term defines the membership judgment.
>>
declare mem{'x; 'y}
declare member{'x; 'y}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

doc <:doc<
   @rewrites

   The @tt{member} judgment is defined using the @hrefterm[set_ind]
   induction combinator.
>>
prim_rw unfold_mem : mem{'x; 'y} <-->
   set_ind{'y; T, f, g. exst t: 'T. eq{'x; .'f 't}}

interactive_rw reduce_mem {| reduce |} : mem{'x; collect{'T; y. 'f['y]}} <-->
   (exst t: 'T. eq{'x; .'f['t]})

prim_rw unfold_member : member{'x; 'y} <-->
   ((isset{'x} & isset{'y}) & mem{'x; 'y})

interactive_rw reduce_member {| reduce |} : member{'x; collect{'T; y. 'f['y]}} <-->
   ((isset{'x} & isset{collect{'T; y. 'f['y]}}) & (exst t: 'T. eq{'x; .'f['t]}))

doc docoff

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform mem_df : except_mode[src] :: parens :: "prec"[prec_apply] :: mem{'x; 't} =
   slot{'x} " " Mpsymbols!member `"s" " " slot{'t}

dform member_df : except_mode[src] :: parens :: "prec"[prec_apply] :: member{'x; 't} =
   slot{'x} " " Mpsymbols!member `"S" " " slot{'t}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @rules
   @modsubsection{Well-formedness}

   The @tt{member} judgment is well-formed if-and-only-if its arguments are
   sets.
>>
interactive mem_type {| intro [] |} :
   ["wf"] sequent { <H> >- isset{'s1} } -->
   ["wf"] sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- "type"{mem{'s1; 's2}} }

interactive mem_equal {| intro [] |} :
   ["wf"] sequent { <H> >- isset{'s1} } -->
   ["wf"] sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- Itt_equal!equal{univ[1:l]; mem{'s1; 's2}; mem{'s1; 's2}} }

(*
 * Introduction.
 *)
interactive member_intro {| intro [] |} :
   ["wf"] sequent { <H> >- isset{'s1} } -->
   ["wf"] sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- mem{'s1; 's2} } -->
   sequent { <H> >- member{'s1; 's2} }

(*
 * Sets contain only sets.
 *)
interactive elem_isset 'y :
   sequent { <H> >- member{'x; 'y} } -->
   sequent { <H> >- isset{'x} }

(*
 * Only sets have elements.
 *)
interactive set_isset 'x :
   sequent { <H> >- member{'x; 'y} } -->
   sequent { <H> >- isset{'y} }

doc <:doc<
   @modsubsection{Functionality}
   The @tt{member} judgment is functional in both its arguments.
   The next two rules provide simple functionality judgments
   for the two set arguments.
>>
interactive mem_fun_left 's1 :
   ["wf"] sequent { <H> >- isset{'s1} } -->
   ["wf"] sequent { <H> >- isset{'s2} } -->
   ["wf"] sequent { <H> >- isset{'s3} } -->
   sequent { <H> >- eq{'s1; 's2} } -->
   sequent { <H> >- mem{'s1; 's3} } -->
   sequent { <H> >- mem{'s2; 's3} }
doc docoff

let memSubstLeftT = mem_fun_left

doc <:doc< nil >>
interactive mem_fun_right 's1 :
   ["wf"] sequent { <H> >- isset{'s1} } -->
   ["wf"] sequent { <H> >- isset{'s2} } -->
   ["wf"] sequent { <H> >- isset{'s3} } -->
   sequent { <H> >- eq{'s1; 's2} } -->
   sequent { <H> >- mem{'s3; 's1} } -->
   sequent { <H> >- mem{'s3; 's2} }
doc docoff

let memSubstRightT = mem_fun_right

doc <:doc<
   The @tt{member_fun} rule proves the general functionality
   judgment.
>>
interactive member_fun {| intro [] |} :
   sequent { <H> >- fun_set{z. 'f1['z]} } -->
   sequent { <H> >- fun_set{z. 'f2['z]} } -->
   sequent { <H> >- fun_prop{z. mem{'f1['z]; 'f2['z]}} }

doc <:doc<
   @modsubsection{Set extensionality}

   Two sets are equal if-and-only-if they have the same elements.
   The proof of this theorem is straightforward.  The two membership
   goals are the functions that ``choose,'' for any element of
   one set, an equal element in the other set.  The equality judgment
   can be proved with the pair of both choice functions.
>>
interactive set_ext :
   ["wf"] sequent { <H> >- isset{'s1} } -->
   ["wf"] sequent { <H> >- isset{'s2} } -->
   ["main"] sequent { <H>; x: set; y: mem{'x; 's1} >- mem{'x; 's2} } -->
   ["main"] sequent { <H>; x: set; y: mem{'x; 's2} >- mem{'x; 's1} } -->
   sequent { <H> >- eq{'s1; 's2} }
doc docoff

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

doc <:doc<
   @tactics

   @begin[description]
   @item{@tactic[memberOfT], @tactic[setOfT];
     The @tt{memberOfT} applies the @hrefrule[elem_isset] rule, and
     the @tt{setOfT} tactic applies the @hrefrule[set_isset] rule.
     Both tactics infer the well-formedness of a set for a membership
     or equality judgment.}
   @end[description]
   @docoff
>>
let memberOfT = elem_isset
let setOfT = set_isset

doc <:doc<
   @begin[description]
   @item{@tactic[setExtT];
      The @tt{setExtT} tactic refines a set-equality
      goal using the rule of @emph{extensionality} @hrefrule[set_ext].
      This rule is not added to the @hreftactic[dT] tactic for default
      reasoning because in many cases, equality judgments can be proved
      in simpler ways.}
   @end[description]
   @docoff
>>
let setExtT = set_ext

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
