(*!
 * @spelling{groupCancelLeftT groupCancelRightT uniqueInvLeftT uniqueInvRightT}
 *
 * @begin[doc]
 * @module[Czf_itt_group]
 *
 * The @tt{Czf_itt_group} module defines groups. Each group
 * is assigned a label, such as $g$. The predicate $@group{g}$
 * is used to represent "$g$ is a group". The carrier set,
 * operation, identity, and inverse of the group are defined
 * as $@car{g}$, $@op{g; a; b}$, $@id{g}$, and $@inv{g; a}$
 * respectively. @emph{Axioms} are used to describe a group,
 * such as the axioms about the closure property, the axiom
 * about associativity, the axioms about the identity and
 * inverse. Any group should satisfy these axioms; all
 * properties of groups are derived constructively from the
 * axioms of groups and the axioms of set theory.
 * @end[doc]
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
extends Itt_record_label0
extends Czf_itt_dall
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
   show_loading "Loading Czf_itt_group%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*! @doc{@terms} *)
declare group{'g}
declare car{'g}         (* The "carrier" set for the group *)
declare op{'g; 'a; 'b}
declare id{'g}
declare inv{'g; 'a}
(*! @docoff *)

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform group_df : except_mode[src] :: group{'g} =
   slot{'g} `" group"

dform car_df : except_mode[src] :: car{'g} =
   `"car(" slot{'g} `")"

dform id_df : except_mode[src] :: id{'g} =
   `"id(" slot{'g} `")"

dform op_df : parens :: except_mode[src] :: op{'g; 'a; 'b} =
   `"op(" slot{'g} `"; " slot{'a}  `"; " slot{'b} `")"

dform inv_df : parens :: except_mode[src] :: inv{'g; 'a} =
   `"inv(" slot{'g} `"; " slot{'a} `")"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @modsection{Axioms}
 *
 * The @tt{group} is defined by a set of axioms.
 *
 * @modsubsection{Well-formedness}
 *
 * The @tt[group], @tt[car], @tt[op], @tt[inv], and @tt[id]
 * are well-formed if the group argument is a label and the
 * set argument is a set (if there is any).
 * @end[doc]
 *)
interactive group_type {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- "type"{group{'g}} }

interactive car_isset {| intro[] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- isset{car{'g}} }

interactive op_isset {| intro[] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- isset{op{'g; 's1; 's2}} }

interactive id_isset {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- isset{id{'g}} }

interactive inv_isset {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- isset{inv{'g; 's1}} }

(*!
 * @begin[doc]
 * @modsubsection{Binary operation}
 *
 * Every @tt[op] is a @emph{binary operation} on @tt[car], which means:
 * first, if $a$ and $b$ are in $@car{g}$, then $@op{g; a; b}$
 * is @emph{again} in $@car{g}$; second, it assigns each ordered
 * pair exactly one element, i.e., @tt[op] is functional in its
 * set arguments.
 * @end[doc]
 *)
interactive op_closure {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- mem{'s1; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'s2; car{'g}} } -->
   sequent ['ext] { 'H >- mem{op{'g; 's1; 's2}; car{'g}} }

interactive op_fun {| intro[] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- fun_set{z. 's1['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. 's2['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. op{'g; 's1['z]; 's2['z]}} }

(*!
 * @begin[doc]
 * @modsubsection{Associativity}
 *
 * Every @tt[op] is associative.
 * @end[doc]
 *)
interactive op_assoc1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- isset{'s3} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- mem{'s1; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'s2; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'s3; car{'g}} } -->
   sequent ['ext] { 'H >- eq{op{'g; op{'g; 's1; 's2}; 's3}; op{'g; 's1; op{'g; 's2; 's3}}} }

(*!
 * @begin[doc]
 * @modsubsection{Identity}
 *
 * Each group $g$ has an identity $@id{g}$ such that
 * for any $s @in @car{g}$, $@eq{@op{g; @id{g}; s}; s}$.
 * @end[doc]
 *)
interactive id_mem {| intro[] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- mem{id{'g}; car{'g}} }

interactive id_eq1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- mem{'s; car{'g}} } -->
   sequent ['ext] { 'H >- eq{op{'g; id{'g}; 's}; 's} }

(*!
 * @begin[doc]
 * @modsubsection{Inverse}
 *
 * Every @tt[inv] is a @emph{unary operation} on @tt[car] such that
 * $@eq{@op{g; @inv{g; s}; s}; @id{g}}$ for any $a @in @car{g}$.
 * @end[doc]
 *)
interactive inv_fun {| intro[] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- fun_set{z. 's['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. inv{'g; 's['z]}} }

interactive inv_mem {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- mem{'s; car{'g}} } -->
   sequent ['ext] { 'H >- mem{inv{'g; 's}; car{'g}} }

interactive inv_id1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- mem{'s; car{'g}} } -->
   sequent ['ext] { 'H >- eq{op{'g; inv{'g; 's}; 's}; id{'g}} }

(*! @docoff *)
interactive op_assoc2 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- isset{'s3} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- mem{'s1; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'s2; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'s3; car{'g}} } -->
   sequent ['ext] { 'H >- eq{op{'g; 's1; op{'g; 's2; 's3}}; op{'g; op{'g; 's1; 's2}; 's3}} }

interactive op_eq1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- isset{'s3} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- mem{'s1; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'s2; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'s3; car{'g}} } -->
   sequent ['ext] { 'H >- eq{'s1; 's2} } -->
   sequent ['ext] { 'H >- eq{op{'g; 's3; 's1}; op{'g; 's3; 's2}} }

interactive op_eq2 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- isset{'s3} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- mem{'s1; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'s2; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'s3; car{'g}} } -->
   sequent ['ext] { 'H >- eq{'s1; 's2} } -->
   sequent ['ext] { 'H >- eq{op{'g; 's1; 's3}; op{'g; 's2; 's3}} }

(*!
 * @begin[doc]
 * @rules
 * @modsubsection{Lemmas}
 *
 * If $@group{g}$, then
 * @begin[enumerate]
 * @item{if $s$ is a member of $@car{g}$ and
 *       $@eq{@op{g; s; s}; s}$, then $s$ is the identity.}
 * @item{the left inverse is also the right inverse.}
 * @item{the left identity is also the right identity.}
 * @end[enumerate]
 * @end[doc]
 *)
interactive id_judge_elim {| elim [] |} 'H 'J :
   sequent [squash] { 'H; x: eq{op{'g; 's; 's}; 's}; 'J['x] >- isset{'s} } -->
   sequent [squash] { 'H; x: eq{op{'g; 's; 's}; 's}; 'J['x] >- 'g IN label } -->
   sequent ['ext] { 'H; x: eq{op{'g; 's; 's}; 's}; 'J['x] >- group{'g} } -->
   sequent ['ext] { 'H; x: eq{op{'g; 's; 's}; 's}; 'J['x] >- mem{'s; car{'g}} } -->
   sequent ['ext] { 'H; x: eq{op{'g; 's; 's}; 's}; 'J['x]; y: eq{'s; id{'g}} >- 'C['x] } -->
   sequent ['ext] { 'H; x: eq{op{'g; 's; 's}; 's}; 'J['x] >- 'C['x] }

interactive inv_id2 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- mem{'s; car{'g}} } -->
   sequent ['ext] { 'H >- eq{op{'g; 's; inv{'g; 's}}; id{'g}} }

interactive id_eq2 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- mem{'s; car{'g}} } -->
   sequent ['ext] { 'H >- eq{op{'g; 's; id{'g}}; 's} }

(*!
 * @begin[doc]
 * @modsubsection{Theorems}
 *
 * $@space @space$
 *
 * The left and right cancellation laws.
 * @end[doc]
 *)
(* Cancellation: a * b = a * c => b = c *)
interactive cancel1 (*{| elim [] |}*) 'H 'J :
   sequent [squash] { 'H; x: eq{op{'g; 's1; 's2}; op{'g; 's1; 's3}}; 'J['x] >- isset{'s1} } -->
   sequent [squash] { 'H; x: eq{op{'g; 's1; 's2}; op{'g; 's1; 's3}}; 'J['x] >- isset{'s2} } -->
   sequent [squash] { 'H; x: eq{op{'g; 's1; 's2}; op{'g; 's1; 's3}}; 'J['x] >- isset{'s3} } -->
   sequent [squash] { 'H; x: eq{op{'g; 's1; 's2}; op{'g; 's1; 's3}}; 'J['x] >- 'g IN label } -->
   sequent ['ext] { 'H; x: eq{op{'g; 's1; 's2}; op{'g; 's1; 's3}}; 'J['x] >- group{'g} } -->
   sequent ['ext] { 'H; x: eq{op{'g; 's1; 's2}; op{'g; 's1; 's3}}; 'J['x] >- mem{'s1; car{'g}} } -->
   sequent ['ext] { 'H; x: eq{op{'g; 's1; 's2}; op{'g; 's1; 's3}}; 'J['x] >- mem{'s2; car{'g}} } -->
   sequent ['ext] { 'H; x: eq{op{'g; 's1; 's2}; op{'g; 's1; 's3}}; 'J['x] >- mem{'s3; car{'g}} } -->
   sequent ['ext] { 'H; x: eq{op{'g; 's1; 's2}; op{'g; 's1; 's3}}; 'J['x] >- eq{'s2; 's3} }

(* Cancellation: b * a = c * a => b = c *)
interactive cancel2 (*{| elim [] |}*) 'H 'J :
   sequent [squash] { 'H; x: eq{op{'g; 's1; 's3}; op{'g; 's2; 's3}}; 'J['x] >- isset{'s1} } -->
   sequent [squash] { 'H; x: eq{op{'g; 's1; 's3}; op{'g; 's2; 's3}}; 'J['x] >- isset{'s2} } -->
   sequent [squash] { 'H; x: eq{op{'g; 's1; 's3}; op{'g; 's2; 's3}}; 'J['x] >- isset{'s3} } -->
   sequent [squash] { 'H; x: eq{op{'g; 's1; 's3}; op{'g; 's2; 's3}}; 'J['x] >- 'g IN label } -->
   sequent ['ext] { 'H; x: eq{op{'g; 's1; 's3}; op{'g; 's2; 's3}}; 'J['x] >- group{'g} } -->
   sequent ['ext] { 'H; x: eq{op{'g; 's1; 's3}; op{'g; 's2; 's3}}; 'J['x] >- mem{'s1; car{'g}} } -->
   sequent ['ext] { 'H; x: eq{op{'g; 's1; 's3}; op{'g; 's2; 's3}}; 'J['x] >- mem{'s2; car{'g}} } -->
   sequent ['ext] { 'H; x: eq{op{'g; 's1; 's3}; op{'g; 's2; 's3}}; 'J['x] >- mem{'s3; car{'g}} } -->
   sequent ['ext] { 'H; x: eq{op{'g; 's1; 's3}; op{'g; 's2; 's3}}; 'J['x] >- eq{'s1; 's2} }
(*! @docoff *)

let groupCancelLeftT i p =
   let j, k = Sequent.hyp_indices p i in
      cancel1 j k p

let groupCancelRightT i p =
   let j, k = Sequent.hyp_indices p i in
      cancel2 j k p

(*!
 * @begin[doc]
 *
 * Unique identity (left and right).
 * @end[doc]
 *)
interactive unique_id1 'H :
   sequent [squash] { 'H >- isset{'e2} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- mem{'e2; car{'g}} } -->
   sequent ['ext] { 'H >- "dall"{car{'g}; s. eq{op{'g; 'e2; 's}; 's}} } -->
   sequent ['ext] { 'H >- eq{'e2; id{'g}} }

interactive unique_id2 'H :
   sequent [squash] { 'H >- isset{'e2} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- mem{'e2; car{'g}} } -->
   sequent ['ext] { 'H >- "dall"{car{'g}; s. eq{op{'g; 's; 'e2}; 's}} } -->
   sequent ['ext] { 'H >- eq{'e2; id{'g}} }

(*!
 * @begin[doc]
 *
 * Unique inverse (left and right).
 * @end[doc]
 *)
interactive unique_inv1 {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- mem{'s; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'s2; car{'g}} } -->
   sequent ['ext] { 'H >- eq{op{'g; 's2; 's}; id{'g}} } -->
   sequent ['ext] { 'H >- eq{'s2; inv{'g; 's}} }

interactive unique_inv2 {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- mem{'s; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'s2; car{'g}} } -->
   sequent ['ext] { 'H >- eq{op{'g; 's; 's2}; id{'g}} } -->
   sequent ['ext] { 'H >- eq{'s2; inv{'g; 's}} }
(*! @docoff *)

interactive unique_inv_elim1 (*{| elim [] |}*) 'H 'J :
   sequent [squash] { 'H; x: eq{op{'g; 's2; 's}; id{'g}}; 'J['x] >- isset{'s} } -->
   sequent [squash] { 'H; x: eq{op{'g; 's2; 's}; id{'g}}; 'J['x] >- isset{'s2} } -->
   sequent [squash] { 'H; x: eq{op{'g; 's2; 's}; id{'g}}; 'J['x] >- 'g IN label } -->
   sequent ['ext] { 'H; x: eq{op{'g; 's2; 's}; id{'g}}; 'J['x] >- group{'g} } -->
   sequent ['ext] { 'H; x: eq{op{'g; 's2; 's}; id{'g}}; 'J['x] >- mem{'s; car{'g}} } -->
   sequent ['ext] { 'H; x: eq{op{'g; 's2; 's}; id{'g}}; 'J['x] >- mem{'s2; car{'g}} } -->
   sequent ['ext] { 'H; x: eq{op{'g; 's2; 's}; id{'g}}; 'J['x]; y: eq{'s2; inv{'g; 's}} >- 'C['x] } -->
   sequent ['ext] { 'H; x: eq{op{'g; 's2; 's}; id{'g}}; 'J['x] >- 'C['x] }

interactive unique_inv_elim2 (*{| elim [] |}*) 'H 'J :
   sequent [squash] { 'H; x: eq{op{'g; 's; 's2}; id{'g}}; 'J['x] >- isset{'s} } -->
   sequent [squash] { 'H; x: eq{op{'g; 's; 's2}; id{'g}}; 'J['x] >- isset{'s2} } -->
   sequent [squash] { 'H; x: eq{op{'g; 's; 's2}; id{'g}}; 'J['x] >- 'g IN label } -->
   sequent ['ext] { 'H; x: eq{op{'g; 's; 's2}; id{'g}}; 'J['x] >- group{'g} } -->
   sequent ['ext] { 'H; x: eq{op{'g; 's; 's2}; id{'g}}; 'J['x] >- mem{'s; car{'g}} } -->
   sequent ['ext] { 'H; x: eq{op{'g; 's; 's2}; id{'g}}; 'J['x] >- mem{'s2; car{'g}} } -->
   sequent ['ext] { 'H; x: eq{op{'g; 's; 's2}; id{'g}}; 'J['x]; y: eq{'s2; inv{'g; 's}} >- 'C['x] } -->
   sequent ['ext] { 'H; x: eq{op{'g; 's; 's2}; id{'g}}; 'J['x] >- 'C['x] }

let uniqueInvLeftT i p =
   let j, k = Sequent.hyp_indices p i in
      unique_inv_elim1 j k p

let uniqueInvRightT i p =
   let j, k = Sequent.hyp_indices p i in
      unique_inv_elim2 j k p

(*!
 * @begin[doc]
 *
 * Unique solution.
 * @end[doc]
 *)
(* Unique solution for a * x = b : x = a' * b *)
interactive unique_sol1 {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'a} } -->
   sequent [squash] { 'H >- isset{'b} } -->
   sequent [squash] { 'H >- isset{'x} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'b; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'x; car{'g}} } -->
   sequent ['ext] { 'H >- eq{op{'g; 'a; 'x}; 'b} } -->
   sequent ['ext] { 'H >- eq{'x; op{'g; inv{'g; 'a}; 'b}} }

(* Unique solution for y * a = b : y = b * a' *)
interactive unique_sol2 {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'a} } -->
   sequent [squash] { 'H >- isset{'b} } -->
   sequent [squash] { 'H >- isset{'y} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'b; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'y; car{'g}} } -->
   sequent ['ext] { 'H >- eq{op{'g; 'y; 'a}; 'b} } -->
   sequent ['ext] { 'H >- eq{'y; op{'g; 'b; inv{'g; 'a}}} }

(*!
 * @begin[doc]
 *
 * Inverse simplification. 
 * @end[doc]
 *)
(* (a * b)' = b' * a'  *)
interactive inv_simplify {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'a} } -->
   sequent [squash] { 'H >- isset{'b} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'b; car{'g}} } -->
   sequent ['ext] { 'H >- eq{inv{'g; op{'g; 'a; 'b}}; op{'g; inv{'g; 'b}; inv{'g; 'a}}} }
(*! @docoff *)

(* Inverse of id *)
interactive inv_of_id {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- eq{inv{'g; id{'g}}; id{'g}} }

(* e * a = a * e *)
interactive id_commut1 {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'a} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- eq{op{'g; id{'g}; 'a}; op{'g; 'a; id{'g}}} }

(* a * e = e * a *)
interactive id_commut2 {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'a} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- eq{op{'g; 'a; id{'g}}; op{'g; id{'g}; 'a}} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*!
 * @begin[doc]
 * @tactics
 *
 * @begin[description]
 * @item{@tactic[groupCancelLeftT], @tactic[groupCancelRightT], @tactic[uniqueInvLeftT], @tactic[uniqueInvRightT];
 *    The @tt{groupCancelLeftT} tactic applies the @hrefrule[cancel1]
 *    rule, which infers that $a$ and $b$ are equal from the fact that
 *    $c * a$ is equal to $c * b$.
 *    The @tt{groupCancelRightT} tactic applies the @hrefrule[cancel2]
 *    rule, which infers that $a$ and $b$ are equal from the fact
 *    that $a * c$ equals $b * c$.
 *    The @tt{uniqueInvLeftT} and @tt{uniqueInvRightT} tactics apply
 *    the @hrefrule[unique_inv_elim1] and @hrefrule[unique_inv_elim2] rules
 *    and prove $x$ is the inverse of $y$ from the fact that $y * x$ or
 *    $x * y$ is the identity respectively.}
 * @end[description]
 * @docoff
 * @end[doc]
 *)
let groupCancelLeftT i p =
   let j, k = Sequent.hyp_indices p i in
      cancel1 j k p

let groupCancelRightT i p =
   let j, k = Sequent.hyp_indices p i in
      cancel2 j k p

let uniqueInvLeftT i p =
   let j, k = Sequent.hyp_indices p i in
      unique_inv_elim1 j k p

let uniqueInvRightT i p =
   let j, k = Sequent.hyp_indices p i in
      unique_inv_elim2 j k p
(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
