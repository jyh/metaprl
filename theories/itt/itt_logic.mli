(*
 * Standard logical connectives.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 1998 Jason Hickey, Cornell University
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
 * Author: Jason Hickey
 * jyh@cs.cornell.edu
 *
 *)

extends Itt_equal
extends Itt_rfun
extends Itt_dfun
extends Itt_fun
extends Itt_dprod
extends Itt_prod
extends Itt_union
extends Itt_void
extends Itt_unit
extends Itt_struct

open Refiner.Refiner.TermType

open Tactic_type.Tacticals
open Tactic_type.Conversionals

open Auto_tactic

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

define unfold_true : "true" <--> unit
define unfold_false : "false" <--> void

define unfold_not : "not"{'a} <--> 'a -> void

define unfold_and : "and"{'a; 'b} <--> 'a * 'b
define unfold_or : "or"{'a; 'b} <--> 'a + 'b
define unfold_implies : "implies"{'a; 'b} <--> 'a -> 'b
define unfold_iff : "iff"{'a; 'b} <--> (('a -> 'b) & ('b -> 'a))
define unfold_cand : "cand"{'a; 'b} <--> "and"{'a; 'b}
define unfold_cor : "cor"{'a; 'b} <--> "or"{'a; ."cand"{."not"{'a}; 'b}}

define unfold_all : "all"{'A; x. 'B['x]} <--> x: 'A -> 'B['x]
define unfold_exists : "exists"{'A; x. 'B['x]} <--> x: 'A * 'B['x]

topval fold_true : conv
topval fold_false : conv
topval fold_not : conv
topval fold_implies : conv
topval fold_iff : conv
topval fold_and : conv
topval fold_or : conv
topval fold_cand : conv
topval fold_cor : conv
topval fold_all : conv
topval fold_exists : conv

(************************************************************************
 * DISPLAY FORMS							*
 ************************************************************************)

prec prec_iff
prec prec_implies
prec prec_and
prec prec_or
prec prec_not
prec prec_quant

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val is_false_term : term -> bool

val is_all_term : term -> bool
val dest_all : term -> string * term * term
val mk_all_term : string -> term -> term -> term

val is_exists_term : term -> bool
val dest_exists : term -> string * term * term
val mk_exists_term : string -> term -> term -> term

val is_or_term : term -> bool
val dest_or : term -> term * term
val mk_or_term : term -> term -> term

val is_and_term : term -> bool
val dest_and : term -> term * term
val mk_and_term : term -> term -> term

val is_cor_term : term -> bool
val dest_cor : term -> term * term
val mk_cor_term : term -> term -> term

val is_cand_term : term -> bool
val dest_cand : term -> term * term
val mk_cand_term : term -> term -> term

val is_implies_term : term -> bool
val dest_implies : term -> term * term
val mk_implies_term : term -> term -> term

val is_iff_term : term -> bool
val dest_iff : term -> term * term
val mk_iff_term : term -> term -> term

val is_not_term : term -> bool
val dest_not : term -> term
val mk_not_term : term -> term

(************************************************************************
 * AUTOMATION                                                           *
 ************************************************************************)

topval univCDT : tactic
topval genUnivCDT : tactic
topval instHypT : term list -> int -> tactic

val logic_prec : auto_prec

topval backThruHypT : int -> tactic
topval assumT : int -> tactic
topval backThruAssumT : int -> tactic

topval moveToConclT : int -> tactic

topval genAssumT : int list -> tactic

(* JProver for itt_logic *)
topval jproverT : tactic

(* specifies maximal multiplicity for JProver *)
topval jAutoT : int -> tactic

(* Tries various backThruHyp and backThruAssum *)
topval logicAutoT : tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)



