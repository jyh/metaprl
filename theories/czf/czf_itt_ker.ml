doc <:doc<
   @module[Czf_itt_ker]

   The @tt[Czf_itt_ker] module defines the kernel proposition
   $@ker{x; h; g1; g2; f[x]}$, in which $f$ is a homomorphism of
   $g1$ into $g2$, i.e., $@hom{x; g1; g2; f}$, and $h$ is a
   group formed by the elements of $g1$ that are mapped into
   the identity of $g2$.

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

doc <:doc< @parents >>
extends Czf_itt_hom
extends Czf_itt_coset
extends Czf_itt_normal_subgroup
doc docoff

open Lm_debug
open Lm_printf

open Dtactic

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc terms
declare ker{'h; 'g1; 'g2; x. 'f['x]}
doc docoff

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc<
   @rewrites
   The @tt[ker] judgment requires that $@hom{x; g1; g2; f[x]}$
   and $h$ be a group which has the same binary operation as
   $g1$ and the elements of whose carrier are all mapped into
   the identity of $g2$.
>>
prim_rw unfold_ker : ker{'h; 'g1; 'g2; x. 'f['x]} <-->
   (hom{'g1; 'g2; x. 'f['x]} & group{'h} & equal{car{'h}; sep{car{'g1}; x. eq{'f['x]; id{'g2}}}} & (all a: set. all b: set. (mem{'a; car{'h}} => mem{'b; car{'h}} => eq{op{'h; 'a; 'b}; op{'g1; 'a; 'b}})))
doc docoff

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform ker_df : parens :: except_mode[src] :: ker{'h; 'g1; 'g2; x. 'f} =
   `"ker(" slot{'h} `"; " slot{'g1} `"; " slot{'g2} `"; " slot{'f} `")"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @rules
   @modsubsection{Well-formedness}

   The kernel proposition $@ker{x; h; g1; g2; f[x]}$ is well-formed if
   $g1$, $g2$, and $h$ are labels, and $f[x]$ is functional in any
   set argument $x$.
>>
interactive ker_type {| intro [] |} :
   sequent { <H> >- 'g1 IN label } -->
   sequent { <H> >- 'g2 IN label } -->
   sequent { <H> >- 'h IN label } -->
   sequent { <H> >- fun_set{x. 'f['x]} } -->
   sequent { <H> >- "type"{ker{'h; 'g1; 'g2; x. 'f['x]}} }

doc <:doc<
   @modsubsection{Introduction}

   The proposition $@ker{x; h; g1; g2; f[x]}$ is true if
   $@hom{x; g1; g2; f}$ is true and $h$ is a group formed
   by the elements of group $g1$ that are mapped into $@id{g2}$.
>>
interactive ker_intro {| intro [] |} :
   sequent { <H> >- 'g1 IN label } -->
   sequent { <H> >- 'g2 IN label } -->
   sequent { <H> >- 'h IN label } -->
   sequent { <H> >- hom{'g1; 'g2; x. 'f['x]} } -->
   sequent { <H> >- group{'h} } -->
   sequent { <H> >- equal{car{'h}; sep{car{'g1}; x. eq{'f['x]; id{'g2}}}} } -->
   sequent { <H>; a: set; b: set; x: mem{'a; car{'h}}; y: mem{'b; car{'h}} >- eq{op{'h; 'a; 'b}; op{'g1; 'a; 'b}} } -->
   sequent { <H> >- ker{'h; 'g1; 'g2; x. 'f['x]} }
doc docoff

(*
 * If f is a group homomorphism of G into G', then the mapping of any
 * element in the kernel of f is equal to the identity of G'.
 *)
interactive ker_mem_id {| elim [] |} 'H 'y :
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- isset{'y} } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- 'g1 IN label } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- 'g2 IN label } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- 'h IN label } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- fun_set{x. 'f['x]} } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- mem{'y; car{'h}} } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]>; v: mem{'y; car{'g1}}; w: eq{'f['y]; id{'g2}} >- 'C['u] } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- 'C['u] }
doc docoff

interactive ker_subgroup hom{'g1; 'g2; x. 'f['x]} 'h :
   sequent { <H> >- 'g1 IN label } -->
   sequent { <H> >- 'g2 IN label } -->
   sequent { <H> >- 'h IN label } -->
   sequent { <H> >- ker{'h; 'g1; 'g2; x. 'f['x]} } -->
   sequent { <H> >- fun_set{x. 'f['x]} } -->
   sequent { <H> >- subgroup{'h; 'g1} }

doc <:doc<
   @modsubsection{Theorems}

   The kernel of a group homomorphism from $g1$ into $g2$ is a subgroup
   of $g1$.
>>
interactive ker_subgroup_elim (*{| elim [] |}*) 'H :
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- 'g1 IN label } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- 'g2 IN label } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- 'h IN label } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- fun_set{x. 'f['x]} } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]>; v: subgroup{'h; 'g1} >- 'C['u] } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- 'C['u] }
doc docoff

interactive ker_lcoset_i {| intro [] |} 'g2 :
   sequent { <H> >- 'g1 IN label } -->
   sequent { <H> >- 'g2 IN label } -->
   sequent { <H> >- 'h IN label } -->
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- mem{'a; car{'g1}} } -->
   sequent { <H> >- fun_set{x. 'f['x]} } -->
   sequent { <H> >- ker{'h; 'g1; 'g2; x. 'f['x]} } -->
   sequent { <H> >- equal{sep{car{'g1}; x. eq{'f['x]; 'f['a]}}; lcoset{'h; 'g1; 'a}} }

interactive ker_rcoset_i {| intro [] |} 'g2 :
   sequent { <H> >- 'g1 IN label } -->
   sequent { <H> >- 'g2 IN label } -->
   sequent { <H> >- 'h IN label } -->
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- mem{'a; car{'g1}} } -->
   sequent { <H> >- fun_set{x. 'f['x]} } -->
   sequent { <H> >- ker{'h; 'g1; 'g2; x. 'f['x]} } -->
   sequent { <H> >- equal{sep{car{'g1}; x. eq{'f['x]; 'f['a]}}; rcoset{'h; 'g1; 'a}} }

doc <:doc<
   If the proposition $@ker{x; h; g1; g2; f[x]}$ is true, then
   the set $@sep{x; @car{g1}; @eq{f[x]; f[a]}}$
   is equal to $@lcoset{h; g1; a}$ and $@rcoset{h; g1; a}$.
>>
interactive ker_lcoset_e (*{| elim [] |}*) 'H 'g2 'a :
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- 'g1 IN label } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- 'g2 IN label } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- 'h IN label } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- isset{'a} } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- mem{'a; car{'g1}} } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- fun_set{x. 'f['x]} } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]>; v: equal{sep{car{'g1}; x. eq{'f['x]; 'f['a]}}; lcoset{'h; 'g1; 'a}} >- 'C['u] } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- 'C['u] }

interactive ker_rcoset_e (*{| elim [] |}*) 'H 'g2 'a :
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- 'g1 IN label } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- 'g2 IN label } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- 'h IN label } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- isset{'a} } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- mem{'a; car{'g1}} } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- fun_set{x. 'f['x]} } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]>; v: equal{sep{car{'g1}; x. eq{'f['x]; 'f['a]}}; rcoset{'h; 'g1; 'a}} >- 'C['u] } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- 'C['u] }

doc <:doc<
   A group homomorphism $f$ from $g1$ into $g2$ is called a
   @emph{monomorphism} if it is @emph{one to one}; this is the
   case if and only if the kernel of $f$ equals $@sing{@id{g1}}$.
>>
interactive ker_mono1 (*{| elim [] |}*) 'H :
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- 'g1 IN label } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- 'g2 IN label } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- 'h IN label } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- fun_set{x. 'f['x]} } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- equal{car{'h}; sep{car{'g1}; x. eq{'x; id{'g1}}}} } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- all c: set.all d: set. (mem{'c; car{'g1}} => mem{'d; car{'g1}} => eq{'f['c]; 'f['d]} => eq{'c; 'd}) }

interactive ker_mono2 (*{| elim [] |}*) 'H :
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- 'g1 IN label } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- 'g2 IN label } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- 'h IN label } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- fun_set{x. 'f['x]} } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]>; c: set; d: set; v: mem{'c; car{'g1}}; w: mem{'d; car{'g1}}; z: eq{'f['c]; 'f['d]} >- eq{'c; 'd} } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- equal{car{'h}; sep{car{'g1}; x. eq{'x; id{'g1}}}} }

doc <:doc<
   The kernel of a group homomorphism $f$ from $g1$ into $g2$ is
   a normal subgroup of $g1$.
>>
interactive ker_normalSubg (*{| elim [] |}*) 'H :
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- 'g1 IN label } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- 'g2 IN label } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- 'h IN label } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- fun_set{x. 'f['x]} } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]>; v: normal_subg{'h; 'g1} >- 'C['u] } -->
   sequent { <H>; u: ker{'h; 'g1; 'g2; x. 'f['x]}; <J['u]> >- 'C['u] }
doc docoff

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

doc <:doc<
   @tactics

   @begin[description]
   @item{@tactic[kerSubgT], @tactic[kerLcosetT], @tactic[kerRcosetT], @tactic[kerNormalSubgT];
      The four @tt[ker] tactics apply the theorems for the
      @hrefterm[ker] judgment. The @tt[kerSubgT] applies the
      @hrefrule[ker_subgroup_elim] rule, the @tt[kerLcosetT]
      tactic applies the @hrefrule[ker_lcoset2] rule, the
      @tt[kerRcosetT] tactic applies the @hrefrule[ker_rcoset2]
      rule, and the @tt[kerNormalSubgT] tactic applies the
      @hrefrule[ker_normalSubg] rule.}
   @end[description]
   @docoff
>>
let kerSubgT = ker_subgroup_elim
let kerLcosetT t1 t2 i = ker_lcoset_e i t1 t2
let kerRcosetT t1 t2 i = ker_rcoset_e i t1 t2
let kerNormalSubgT = ker_normalSubg

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
