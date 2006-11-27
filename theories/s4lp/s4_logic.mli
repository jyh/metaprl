(*
 * S4 Gentzen style logic, connection with jprover.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/htmlman/default.html or visit http://metaprl.org/
 * for more information.
 *
 * Copyright (C) 2005-2006 MetaPRL Group, Caltech
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
 * Author: Yegor Bryukhov
 * ybryukhov@gc.cuny.edu
 *
 *)

extends Base_theory

open Basic_tactics

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)
declare default_extract
declare typeclass Concl -> Dform
declare sequent { Ignore : Term >- Concl } : Judgment
declare sequent [concl] { Ignore : Term >- Ignore } : Concl
declare sequent [boxed[i:n]] { Ignore : Term >- Ignore } : Judgment

declare "true"
declare "false"
declare "not"{'a}
declare "and"{'a; 'b}
declare "or"{'a; 'b}
declare "implies"{'a; 'b}
declare "box"[i:n]{'a}

define iform simple_box: box{'a} <--> box[0]{'a}
define iform diamond : diamond[i:n]{'a} <--> "not"{"box"[i:n]{"not"{'a}}}
define iform simple_diamond : diamond{'a} <--> diamond[0]{'a}
define iform iff : "iff"{'a; 'b} <--> "and"{'a => 'b; 'b => 'a}

(************************************************************************
 * DISPLAY FORMS							*
 ************************************************************************)

prec prec_implies
prec prec_and
prec prec_or
prec prec_not

(************************************************************************
 * RULES, used by other theories directly                               *
 ************************************************************************)
(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val is_false_term : term -> bool

val is_or_term : term -> bool
val dest_or : term -> term * term
val mk_or_term : term -> term -> term

val is_and_term : term -> bool
val dest_and : term -> term * term
val mk_and_term : term -> term -> term

val is_implies_term : term -> bool
val dest_implies : term -> term * term
val mk_implies_term : term -> term -> term

val is_not_term : term -> bool
val dest_not : term -> term
val mk_not_term : term -> term

module S4_Logic : Jlogic_sig.JLogicSig

(************************************************************************
 * AUTOMATION                                                           *
 ************************************************************************)

topval thin_nonboxedT : int -> tactic
topval prove_boxedT : tactic
topval box_introT : int -> tactic

(* S4-Prover for s4_logic *)
topval proverT : tactic
topval simple_proverT : tactic (* JProver with max multiplicity 1; used by autoT *)

(*
 * -*-
 * Local Variables:
 * End:
 * -*-
 *)
