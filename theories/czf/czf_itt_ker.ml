(*!
 * @spelling{ker}
 *
 * @begin[doc]
 * @theory[Czf_itt_ker]
 *
 * The @tt{Czf_itt_ker} module defines the kernel proposition
 * $@ker{x; h; g1; g2; f}$, in which $f$ is a homomorphism of
 * $g1$ into $g2$, i.e., $@hom{x; g1; g2; f}$, and $h$ is a
 * group formed by the elements of $g1$ that are mapped into
 * the identity of $g2$.
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 2002 Xin Yu, Caltech
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * Author: Xin Yu
 * @email{xiny@cs.caltech.edu}
 * @end[license]
 *)

(*! @doc{@parents} *)
include Czf_itt_group
include Czf_itt_subgroup
include Czf_itt_group_bvd
include Czf_itt_hom
include Czf_itt_sep
include Czf_itt_inv_image
include Czf_itt_coset
include Czf_itt_normal_subgroup
(*! @docoff *)

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
   show_loading "Loading Czf_itt_ker%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*! @doc{@terms} *)
declare ker{'h; 'g1; 'g2; x. 'f['x]}
(*! @docoff *)

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 * The kernel of a homomorphism is defined by group builder.
 * @end[doc]
 *)
prim_rw unfold_ker : ker{'h; 'g1; 'g2; x. 'f['x]} <-->
   (hom{'g1; 'g2; x. 'f['x]} & group_bvd{'h; 'g1; sep{car{'g1}; x. mem{pair{'f['x]; id{'g2}}; eqG{'g2}}}})
(*! @docoff *)

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform ker_df : parens :: except_mode[src] :: ker{'h; 'g1; 'g2; x. 'f} =
   `"ker(" slot{'h} `"; " slot{'g1} `"; " slot{'g2} `"; " slot{'f} `")"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rules
 * @thysubsection{Well-formedness}
 *
 * The kernel proposition $@ker{x; h; g1; g2; f}$ is well-formed if
 * $g1$, $g2$, and $h$ are labels, and $f[x]$ is functional on any
 * set argument $x$.
 * @end[doc]
 *)
interactive ker_type {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent [squash] { 'H >- 'h IN label } -->
   sequent ['ext] { 'H >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H >- "type"{ker{'h; 'g1; 'g2; x. 'f['x]}} }

(*!
 * @begin[doc]
 * @thysubsection{Introduction}
 *
 * The kernel proposition $@ker{x; h; g1; g2; f}$ is true if the
 * homomorphism proposition $@hom{x; g1; g2; f}$ is true and $h$
 * is a group formed by the elements of group $g1$ whose mapping
 * is $@id{g2}$.
 * @end[doc]
 *)
interactive ker_intro {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent [squash] { 'H >- 'h IN label } -->
   sequent ['ext] { 'H >- hom{'g1; 'g2; x. 'f['x]} } -->
   sequent ['ext] { 'H >- group_bvd{'h; 'g1; sep{car{'g1}; x. mem{pair{'f['x]; id{'g2}}; eqG{'g2}}}} } -->
   sequent ['ext] { 'H >- ker{'h; 'g1; 'g2; x. 'f['x]} }
(*! @docoff *)

(*
 * If f is a group homomorphism of G into G', then the mapping of any
 * element in the kernel of f is equivalent with the identity of G'.
 *)
interactive ker_mem_equiv {| elim [] |} 'H 'J 'y :
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- isset{'y} } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g1 IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g2 IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'h IN label } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- mem{'y; car{'h}} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u]; v: mem{'y; car{'g1}}; w: equiv{car{'g2}; eqG{'g2}; 'f['y]; id{'g2}} >- 'C['u] } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'C['u] }

(*!
 * @begin[doc]
 * @thysubsection{Theorems}
 *
 * The kernel of a group homomorphism from $g1$ into $g2$ is a subgroup
 * of $g2$.
 * @end[doc]
 *)
interactive ker_subgroup 'H hom{'g1; 'g2; x. 'f['x]} 'h :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent [squash] { 'H >- 'h IN label } -->
   sequent ['ext] { 'H >- ker{'h; 'g1; 'g2; x. 'f['x]} } -->
   sequent ['ext] { 'H >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H >- subgroup{'h; 'g1} }

interactive ker_subgroup_elim (*{| elim [] |}*) 'H 'J :
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g1 IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g2 IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'h IN label } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u]; v: subgroup{'h; 'g1} >- 'C['u] } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'C['u] }
(*! @docoff *)

let kerSubgT i p =
   let j, k = Sequent.hyp_indices p i in
      ker_subgroup_elim j k p

(*!
 * @begin[doc]
 * If the kernel proposition $@ker{x; h; g1; g2; f}$ is true, then
 * the set $@sep{x; @car{g1}; @mem{@pair{f[x]; f[a]}; @eqG{g2}}}$
 * is equal to $@lcoset{h; g1; a}$ and $@rcoset{h; g1; a}$.
 * @end[doc]
 *)
interactive ker_lcoset_intro {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent [squash] { 'H >- 'h IN label } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g1}} } -->
   sequent ['ext] { 'H >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H >- ker{'h; 'g1; 'g2; x. 'f['x]} } -->
   sequent ['ext] { 'H >- equal{sep{car{'g1}; x. mem{pair{'f['x]; 'f['a]}; eqG{'g2}}}; lcoset{'h; 'g1; 'a}} }

interactive ker_lcoset_elim (*{| elim [] |}*) 'H 'J 'a :
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g1 IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g2 IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'h IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- isset{'a} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- mem{'a; car{'g1}} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u]; v: equal{sep{car{'g1}; x. mem{pair{'f['x]; 'f['a]}; eqG{'g2}}}; lcoset{'h; 'g1; 'a}} >- 'C['u] } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'C['u] }

interactive ker_rcoset_intro {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent [squash] { 'H >- 'h IN label } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g1}} } -->
   sequent ['ext] { 'H >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H >- ker{'h; 'g1; 'g2; x. 'f['x]} } -->
   sequent ['ext] { 'H >- equal{sep{car{'g1}; x. mem{pair{'f['x]; 'f['a]}; eqG{'g2}}}; rcoset{'h; 'g1; 'a}} }

interactive ker_rcoset_elim (*{| elim [] |}*) 'H 'J 'a :
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g1 IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g2 IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'h IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- isset{'a} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- mem{'a; car{'g1}} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u]; v: equal{sep{car{'g1}; x. mem{pair{'f['x]; 'f['a]}; eqG{'g2}}}; rcoset{'h; 'g1; 'a}} >- 'C['u] } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'C['u] }
(*! @docoff *)

let kerLcosetT t i p =
   let j, k = Sequent.hyp_indices p i in
      ker_lcoset_elim j k t p

let kerRcosetT t i p =
   let j, k = Sequent.hyp_indices p i in
      ker_rcoset_elim j k t p

(*!
 * @begin[doc]
 * A $@hom{x; g1; g2; f}$ is called a @emph{monomorphism} if it is
 * @emph{one to one}; this is the case if and only if the kernel
 * of $f$ equals ${@id{g1}}$.
 * @end[doc]
 *)
(*
 * A group homomorphism f: G1 -> G2 is a one-to-one map
 * if and only if Ker(f) = {id(g1)}.
 *)
interactive ker_monomorphism1 (*{| elim [] |}*) 'H 'J :
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g1 IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g2 IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'h IN label } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- equal{car{'h}; sep{car{'g1}; x. mem{pair{'x; id{'g1}}; eqG{'g1}}}} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- all c: set.all d: set. (mem{'c; car{'g1}} => mem{'d; car{'g1}} => equiv{car{'g2}; eqG{'g2}; 'f['c]; 'f['d]} => equiv{car{'g1}; eqG{'g1}; 'c; 'd}) }

interactive ker_monomorphism2 (*{| elim [] |}*) 'H 'J :
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g1 IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g2 IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'h IN label } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u]; c: set; d: set; u: mem{'c; car{'g1}}; v: mem{'d; car{'g1}}; w: equiv{car{'g2}; eqG{'g2}; 'f['c]; 'f['d]} >- equiv{car{'g1}; eqG{'g1}; 'c; 'd} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- equal{car{'h}; sep{car{'g1}; x. mem{pair{'x; id{'g1}}; eqG{'g1}}}} }

(*!
 * @begin[doc]
 * The ker of a $@hom{x; g1; g2; f}$ is a normal subgroup of $g1$.
 * @end[doc]
 *)
interactive ker_normalSubg (*{| elim [] |}*) 'H 'J :
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g1 IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'g2 IN label } -->
   sequent [squash] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'h IN label } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- fun_set{x. 'f['x]} } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u]; v: normal_subg{'h; 'g1} >- 'C['u] } -->
   sequent ['ext] { 'H; u: ker{'h; 'g1; 'g2; x. 'f['x]}; 'J['u] >- 'C['u] }
(*! @docoff *)

let kerNormalSubgT i p =
   let j, k = Sequent.hyp_indices p i in
      ker_normalSubg j k p

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
