(*
 * Partial order, linear order, etc.
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
 * Copyright (C) 2003 Yegor Bryukhov, GC CUNY
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
 * Email : ybryukhov@gc.cuny.edu
 *)

extends Itt_record

open Tactic_type.Tactic

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)
define unfold_isRelation : isRelation{'car; 'rel} <-->
	('car Type & 'rel in ('car -> 'car -> bool))

define unfold_isReflexive : isReflexive{'car; 'rel} <-->
	all a: 'car. "assert"{'rel 'a 'a}

define unfold_isIrreflexive : isIrreflexive{'car; 'rel} <-->
	all a: 'car. not{"assert"{'rel 'a 'a}}

define unfold_isAntisym : isAntisym{'car; 'rel} <-->
	all a: 'car. all b: 'car. ("assert"{'rel 'a 'b} & "assert"{'rel 'b 'a} => ('a='b in 'car))

define unfold_isTransitive : isTransitive{'car; 'rel} <-->
	all a: 'car. all b: 'car. all c: 'car. ("assert"{'rel 'a 'b} & "assert"{'rel 'b 'c} => "assert"{'rel 'a 'c})

define unfold_isPreorder1 : isPreorder{'car; 'rel} <-->
	isRelation{'car; 'rel} & isReflexive{'car; 'rel} & isTransitive{'car; 'rel}

define unfold_isUnstrictPartialOrder1 : isUnstrictPartialOrder{'car; 'rel} <-->
	isPreorder{'car; 'rel} & isAntisym{'car; 'rel}

define unfold_isStrictPartialOrder1 : isStrictPartialOrder{'car; 'rel} <-->
	isRelation{'car; 'rel} & isIrreflexive{'car; 'rel} & isTransitive{'car; 'rel}

define unfold_isLinear : isLinear{'car; 'rel} <-->
	all a: 'car. all b: 'car. ("assert"{'rel 'a 'b} or "assert"{'rel 'b 'a})

define unfold_isUnstrictTotalOrder1 : isUnstrictTotalOrder{'car; 'rel} <-->
	isUnstrictPartialOrder{'car; 'rel} & isLinear{'car; 'rel}

define unfold_isTrichotomous : isTrichotomous{'car; 'rel} <-->
	all a: 'car. all b: 'car. ("assert"{'rel 'a 'b} or "assert"{'rel 'b 'a} or 'a='b in 'car)

define unfold_isStrictTotalOrder1 : isStrictTotalOrder{'car; 'rel} <-->
	isStrictPartialOrder{'car; 'rel} & isTrichotomous{'car; 'rel}

define unfold_strict2unstrict : strict2unstrict{'rel} <-->
	lambda{a. lambda{b. bnot{'rel 'b 'a}}}

define unfold_unstrict2strict : unstrict2strict{'rel} <-->
	lambda{a. lambda{b. bnot{'rel 'b 'a}}}

define unfold_unstrict2eq : unstrict2eq{'rel} <-->
	lambda{a. lambda{b. band{'rel 'a 'b; 'rel 'b 'a}}}

define unfold_inverse_order : inverse_order{'rel} <-->
	lambda{a. lambda{b. 'rel 'b 'a}}

define unfold_max : max{'rel} <-->
	lambda{a.lambda{b.ifthenelse{'rel 'a 'b; 'b; 'a}}}

define unfold_min : min{'rel} <-->
	lambda{a.lambda{b.ifthenelse{'rel 'a 'b; 'a; 'b}}}

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

topval unfold_isPreorder : conv
topval unfold_preorder : conv
topval unfold_isUnstrictPartialOrder : conv
topval unfold_unstrictPartialOrder : conv
topval unfold_isStrictPartialOrder : conv
topval unfold_strictPartialOrder : conv

topval fold_relation : conv
topval fold_isReflexive : conv
topval fold_isTransitive : conv
topval fold_isAntisym : conv

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
