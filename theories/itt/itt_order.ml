doc <:doc<
   @begin[doc]
   @module[Itt_order]

   This theory defines ordered sets.
   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.

   Copyright (C) 2003 Yegor Bryukhov, GC CUNY

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

   Author: Yegor Bryukhov @email{ybryukhov@gc.cuny.edu}
   @end[license]
>>

doc <:doc< @doc{@parents} >>
extends Itt_bisect
(*extends Itt_subset
extends Itt_subset2
extends Itt_ext_equal*)
extends Itt_record
extends Itt_record_renaming
extends Itt_bool
extends Itt_labels
doc docoff

open Lm_debug
open Lm_printf

open Basic_tactics

open Itt_rfun

let _ =
   show_loading "Loading Itt_order%t"

(************************************************************************
 * RELATION, unstrictPartial ORDER                                              *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @modsection{Non-strict Partial Order}
   @modsubsection{Rewrites}

   @end[doc]
>>

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

doc docoff

let unfold_isPreorder = unfold_isPreorder1 thenC addrC [Subterm 1] unfold_isReflexive thenC addrC [Subterm 2] unfold_isTransitive
let unfold_isUnstrictPartialOrder = unfold_isUnstrictPartialOrder1 thenC addrC [Subterm 1] unfold_isPreorder thenC addrC [Subterm 2] unfold_isAntisym
let unfold_isStrictPartialOrder = unfold_isStrictPartialOrder1 thenC addrC [Subterm 1] unfold_isIrreflexive thenC addrC [Subterm 2] unfold_isTransitive

let fold_isReflexive = makeFoldC << isReflexive{'car; 'rel} >> unfold_isReflexive
let fold_isIrreflexive = makeFoldC << isIrreflexive{'car; 'rel} >> unfold_isIrreflexive
let fold_isTransitive = makeFoldC << isTransitive{'car; 'rel} >> unfold_isTransitive
let fold_isAntisym = makeFoldC << isAntisym{'car; 'rel} >> unfold_isAntisym
let fold_isPreorder1 = makeFoldC << isPreorder{'car; 'rel} >> unfold_isPreorder1
let fold_isUnstrictPartialOrder1 = makeFoldC << isUnstrictPartialOrder{'car; 'rel} >> unfold_isUnstrictPartialOrder1
let fold_isStrictPartialOrder1 = makeFoldC << isStrictPartialOrder{'car; 'rel} >> unfold_isStrictPartialOrder1
let fold_isLinear = makeFoldC << isLinear{'car; 'rel} >> unfold_isLinear
let fold_isTrichotomous = makeFoldC << isTrichotomous{'car; 'rel} >> unfold_isTrichotomous

let isRelationDT n = rw unfold_isRelation n thenT dT n
let isRelationDT0 = rw unfold_isRelation 0 thenT dT 0
let isReflexiveDT0 = rw unfold_isReflexive 0 thenT dT 0
let isIrreflexiveDT0 = rw unfold_isIrreflexive 0 thenT dT 0
let isAntisymDT0 = rw unfold_isAntisym 0 thenT dT 0 thenMT dT 0 thenMT dT 0 thenMT dT (-1)
let isTransitiveDT0 = rw unfold_isTransitive 0 thenT dT 0 thenMT dT 0 thenMT dT 0 thenMT dT 0 thenMT dT (-1)
let isUnstrictPartialOrderDT n = rw (unfold_isUnstrictPartialOrder1 thenC addrC [Subterm 1] unfold_isPreorder1) n thenT dT n thenT dT n thenT dT (n+1)
let isUnstrictPartialOrderDT0 = rw (unfold_isUnstrictPartialOrder1 thenC addrC [Subterm 1] unfold_isPreorder1) 0 thenT dT 0 thenLT [(dT 0 thenLT [idT;dT 0]); idT]
let isStrictPartialOrderDT n = rw unfold_isStrictPartialOrder1 n thenT dT n thenT dT (n+1)
let isStrictPartialOrderDT0 = rw unfold_isStrictPartialOrder1 0 thenT dT 0 thenLT [idT; dT 0]
let isLinearDT0 = rw unfold_isLinear 0 thenT dT 0 thenMT dT 0
let isUnstrictTotalOrderDT n = rw unfold_isUnstrictTotalOrder1 n thenT dT n
let isTrichotomousDT0 = rw unfold_isTrichotomous 0 thenMT dT 0 thenMT dT 0
let isStrictTotalOrderDT n = rw unfold_isStrictTotalOrder1 n thenT dT n

let resource elim += [
	<<isRelation{'car; 'rel}>>, isRelationDT;
	<<isReflexive{'car; 'rel}>>, rw unfold_isReflexive;
	<<isIrreflexive{'car; 'rel}>>, rw unfold_isIrreflexive;
	<<isAntisym{'car; 'rel}>>, rw unfold_isAntisym;
	<<isTransitive{'car; 'rel}>>, rw unfold_isTransitive;
	<<isUnstrictPartialOrder{'car; 'rel}>>, isUnstrictPartialOrderDT;
	<<isStrictPartialOrder{'car; 'rel}>>, isStrictPartialOrderDT;
	<<isLinear{'car; 'rel}>>, rw unfold_isLinear;
	<<isUnstrictTotalOrder{'car; 'rel}>>, isUnstrictTotalOrderDT;
	<<isTrichotomous{'car; 'rel}>>, rw unfold_isTrichotomous;
	<<isStrictTotalOrder{'car; 'rel}>>, isStrictTotalOrderDT
	]

let resource intro += [
	<<isRelation{'car; 'rel}>>, wrap_intro (isRelationDT0);
	<<isReflexive{'car; 'rel}>>, wrap_intro (isReflexiveDT0);
	<<isIrreflexive{'car; 'rel}>>, wrap_intro (isIrreflexiveDT0);
	<<isAntisym{'car; 'rel}>>, wrap_intro (isAntisymDT0);
(*	<<isTransitive{'car; 'rel}>>, wrap_intro (isTransitiveDT0);*)
	<<isUnstrictPartialOrder{'car; 'rel}>>, wrap_intro (isUnstrictPartialOrderDT0);
	<<isStrictPartialOrder{'car; 'rel}>>, wrap_intro (isStrictPartialOrderDT0);
	<<isLinear{'car; 'rel}>>, wrap_intro (isLinearDT0);
	<<isUnstrictTotalOrder{'car; 'rel}>>, wrap_intro (isUnstrictTotalOrderDT 0);
	<<isTrichotomous{'car; 'rel}>>, wrap_intro (isTrichotomousDT0);
	<<isStrictTotalOrder{'car; 'rel}>>, wrap_intro (isStrictTotalOrderDT 0)
	]

doc <:doc<
   @begin[doc]
   @modsubsection{Well-formedness}

   @end[doc]
>>

interactive isRelation_wf {| intro [] |} :
	[wf] sequent { <H> >- 'rel in 'car -> 'car -> bool } -->
	[wf] sequent { <H> >- 'car Type } -->
	sequent { <H> >- isRelation{'car; 'rel} Type }

interactive isReflexive_wf {| intro [] |} :
   sequent { <H> >- 'rel in 'car -> 'car -> bool } -->
	sequent { <H> >- isReflexive{'car; 'rel} Type }

interactive isIrreflexive_wf {| intro [] |} :
   sequent { <H> >- 'rel in 'car -> 'car -> bool } -->
	sequent { <H> >- isIrreflexive{'car; 'rel} Type }

interactive isAntisym_wf {| intro [] |} :
   sequent { <H> >- 'rel in 'car -> 'car -> bool } -->
	sequent { <H> >- isAntisym{'car; 'rel} Type }

interactive isTransitive_wf {| intro [] |} :
   sequent { <H> >- 'rel in 'car -> 'car -> bool } -->
	sequent { <H> >- isTransitive{'car; 'rel} Type }

interactive isLinear_wf {| intro [] |} :
   sequent { <H> >- 'rel in 'car -> 'car -> bool } -->
	sequent { <H> >- isLinear{'car; 'rel} Type }

interactive isTrichotomous_wf {| intro [] |} :
   sequent { <H> >- 'rel in 'car -> 'car -> bool } -->
	sequent { <H> >- isTrichotomous{'car; 'rel} Type }

interactive isPreorder_wf {| intro [] |} :
   sequent { <H> >- 'rel in 'car -> 'car -> bool } -->
	sequent { <H> >- isPreorder{'car; 'rel} Type }

interactive isUnstrictPartialOrder_wf {| intro [] |} :
   sequent { <H> >- 'rel in 'car -> 'car -> bool } -->
	sequent { <H> >- isUnstrictPartialOrder{'car; 'rel} Type }

interactive isStrictPartialOrder_wf {| intro [] |} :
   sequent { <H> >- 'rel in 'car -> 'car -> bool } -->
	sequent { <H> >- isStrictPartialOrder{'car; 'rel} Type }

interactive isUnstrictTotalOrder_wf {| intro [] |} :
   sequent { <H> >- 'rel in 'car -> 'car -> bool } -->
	sequent { <H> >- isUnstrictTotalOrder{'car; 'rel} Type }

interactive isStrictTotalOrder_wf {| intro [] |} :
   sequent { <H> >- 'rel in 'car -> 'car -> bool } -->
	sequent { <H> >- isStrictTotalOrder{'car; 'rel} Type }

interactive strict2unstrict_wf {| intro [] |} :
	sequent { <H> >- 'rel in 'car -> 'car -> bool } -->
	sequent { <H> >- strict2unstrict{'rel} in 'car -> 'car -> bool }

interactive unstrict2strict_wf {| intro [] |} :
	sequent { <H> >- 'rel in 'car -> 'car -> bool } -->
	sequent { <H> >- unstrict2strict{'rel} in 'car -> 'car -> bool }

interactive unstrict2eq_wf {| intro [] |} :
	sequent { <H> >- 'rel in 'car -> 'car -> bool } -->
	sequent { <H> >- unstrict2eq{'rel} in 'car -> 'car -> bool }

interactive unstrict2eq_wf2 {| intro [] |} 'car :
	sequent { <H> >- 'rel in 'car -> 'car -> bool } -->
	sequent { <H> >- 'a in 'car } -->
	sequent { <H> >- 'b in 'car } -->
	sequent { <H> >- (unstrict2eq{'rel} 'a 'b) in bool }

interactive inverse_order_wf {| intro [] |} :
	sequent { <H> >- 'rel in 'car -> 'car -> bool } -->
	sequent { <H> >- inverse_order{'rel} in 'car -> 'car -> bool }

interactive max_wf {| intro [] |} :
	sequent { <H> >- isRelation{'car;'rel} } -->
	sequent { <H> >- max{'rel} in 'car -> 'car -> 'car }

interactive min_wf {| intro [] |} :
	sequent { <H> >- isRelation{'car;'rel} } -->
	sequent { <H> >- max{'rel} in 'car -> 'car -> 'car }

interactive isTransitive_intro :
   [wf] sequent { <H> >- 'rel in 'car -> 'car -> bool } -->
   [wf] sequent { <H> >- 'car Type } -->
	[main] sequent { <H>; a: 'car; b: 'car; c: 'car;
		"assert"{'rel 'a 'b}; "assert"{'rel 'b 'c} >- "assert"{'rel 'a 'c} } -->
	sequent { <H> >- isTransitive{'car; 'rel} }

doc docoff

let tryReduceBetaC = tryC reduce_beta
let tryReduceBeta = rw (addrC [Subterm 1] ((addrC [Subterm 1] tryReduceBetaC) thenC tryReduceBetaC))
let isTransitiveDT0 = isTransitive_intro thenMT tryReduceBeta 0 thenMT tryReduceBeta (-1) thenMT tryReduceBeta (-2)

let resource intro += [
	<<isTransitive{'car; 'rel}>>, wrap_intro (isTransitiveDT0);
	]

doc <:doc<
   @begin[doc]
   @modsubsection{Decidability of equality for type with total order}

	For type with total order equality can be expressed via order relation.
	Since we consider decidable relations it implies decidability of equality
	for types with total order.

   @end[doc]
>>

interactive unstrict2eqIfEqual {| intro [] |} 'car :
	sequent { <H> >- isUnstrictTotalOrder{'car; 'rel} } -->
	sequent { <H> >- 'a in 'car } -->
	sequent { <H> >- 'b in 'car } -->
	sequent { <H> >- 'a = 'b in 'car } -->
	sequent { <H> >- "assert"{(unstrict2eq{'rel} 'a 'b)} }

interactive unstrict2eqThenEqual 'rel :
	sequent { <H> >- isUnstrictTotalOrder{'car; 'rel} } -->
	sequent { <H> >- 'a in 'car } -->
	sequent { <H> >- 'b in 'car } -->
	sequent { <H> >- "assert"{(unstrict2eq{'rel} 'a 'b)} } -->
	sequent { <H> >- 'a = 'b in 'car }

interactive totalOrderThenDecidableEquality 'rel :
	sequent { <H> >- isUnstrictTotalOrder{'car; 'rel} } -->
	sequent { <H> >- 'a in 'car } -->
	sequent { <H> >- 'b in 'car } -->
	sequent { <H> >- decidable{'a = 'b in 'car} }

doc <:doc<
   @begin[doc]
   @modsubsection{Non-strict (total) order @em[vs] strict (total) order}

	For totally ordered types we can express strict order via non-strict one and
	vice versa.

   @end[doc]
>>

interactive strict2unstrictTotalOrder :
	sequent { <H> >- isStrictTotalOrder{'car; 'rel} } -->
	sequent { <H> >- isUnstrictTotalOrder{'car; strict2unstrict{'rel}} }

interactive unstrict2strictTotalOrder :
	sequent { <H> >- isUnstrictTotalOrder{'car; 'rel} } -->
	sequent { <H> >- isStrictTotalOrder{'car; unstrict2strict{'rel}} }

doc <:doc<
   @begin[doc]
   @modsubsection{Inverse order inherits all properties defined here}

   @end[doc]
>>

interactive inverseRelation {| intro [] |} :
	sequent { <H> >- isRelation{'car; 'rel} } -->
	sequent { <H> >- isRelation{'car; inverse_order{'rel}} }

interactive inverseReflexive {| intro [] |} :
	sequent { <H> >- isReflexive{'car; 'rel} } -->
	sequent { <H> >- isReflexive{'car; inverse_order{'rel}} }

interactive inverseIrreflexive {| intro [] |} :
	sequent { <H> >- isIrreflexive{'car; 'rel} } -->
	sequent { <H> >- isIrreflexive{'car; inverse_order{'rel}} }

interactive inverseAntisym {| intro [] |} :
	sequent { <H> >- isAntisym{'car; 'rel} } -->
	sequent { <H> >- isAntisym{'car; inverse_order{'rel}} }

interactive inverseTransitive {| intro [] |} :
	sequent { <H> >- isTransitive{'car; 'rel} } -->
	sequent { <H> >- isTransitive{'car; inverse_order{'rel}} }

interactive inversePreorder {| intro [] |} :
	sequent { <H> >- isPreorder{'car; 'rel} } -->
	sequent { <H> >- isPreorder{'car; inverse_order{'rel}} }

interactive inverseUnstrictPartialOrder {| intro [] |} :
	sequent { <H> >- isUnstrictPartialOrder{'car; 'rel} } -->
	sequent { <H> >- isUnstrictPartialOrder{'car; inverse_order{'rel}} }

interactive inverseStrictPartialOrder {| intro [] |} :
	sequent { <H> >- isStrictPartialOrder{'car; 'rel} } -->
	sequent { <H> >- isStrictPartialOrder{'car; inverse_order{'rel}} }

interactive inverseLinear {| intro [] |} :
	sequent { <H> >- isLinear{'car; 'rel} } -->
	sequent { <H> >- isLinear{'car; inverse_order{'rel}} }

interactive inverseTrichotomous {| intro [] |} :
	sequent { <H> >- isTrichotomous{'car; 'rel} } -->
	sequent { <H> >- isTrichotomous{'car; inverse_order{'rel}} }

interactive inverseUnstrictTotalOrder {| intro [] |} :
	sequent { <H> >- isUnstrictTotalOrder{'car; 'rel} } -->
	sequent { <H> >- isUnstrictTotalOrder{'car; inverse_order{'rel}} }

interactive inverseStrictTotalOrder {| intro [] |} :
	sequent { <H> >- isStrictTotalOrder{'car; 'rel} } -->
	sequent { <H> >- isStrictTotalOrder{'car; inverse_order{'rel}} }

doc <:doc<
   @begin[doc]
   @modsubsection{Inverse order @em[vs] conversions between strict and non-strict order}

	@tt[Inverse_order] commutes with @tt[strict2unstrict], @tt[unstrict2strict].
	@tt[Unstrict2eq] absorbs @tt[inverse_order].

   @end[doc]
>>

interactive inverse_strict2unstrict 'car :
	sequent { <H> >- isRelation{'car; 'rel} } -->
	sequent { <H> >- inverse_order{strict2unstrict{'rel}} = strict2unstrict{inverse_order{'rel}} in 'car -> 'car -> bool }

interactive inverse_unstrict2strict 'car :
	sequent { <H> >- isRelation{'car; 'rel} } -->
	sequent { <H> >- inverse_order{unstrict2strict{'rel}} = unstrict2strict{inverse_order{'rel}} in 'car -> 'car -> bool }

interactive inverse_unstrict2eq 'car :
	sequent { <H> >- isRelation{'car; 'rel} } -->
	sequent { <H> >- inverse_order{unstrict2eq{'rel}} = unstrict2eq{'rel} in 'car -> 'car -> bool }

doc <:doc<
   @begin[doc]
   @modsubsection{Integers are totally ordered}

   @end[doc]
>>

interactive int_lt_boolIsStrictTotalOrder :
	sequent { <H> >- isStrictTotalOrder{int; lambda{a.lambda{b. lt_bool{'a;'b}}}} }

interactive unstrict_of_lt_bool :
	sequent { <H> >- 'a in int } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- le_bool{'a;'b}=(strict2unstrict{lambda{a.lambda{b. lt_bool{'a;'b}}}} 'a 'b) in bool }

interactive int_le_boolIsUnstrictTotalOrder :
	sequent { <H> >- isUnstrictTotalOrder{int; lambda{a.lambda{b. le_bool{'a;'b}}}} }

interactive inverse_of_lt_bool :
	sequent { <H> >- 'a in int } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- gt_bool{'a;'b}=(inverse_order{lambda{a.lambda{b. lt_bool{'a;'b}}}} 'a 'b) in bool }

interactive int_gt_boolIsStrictTotalOrder :
	sequent { <H> >- isStrictTotalOrder{int; lambda{a.lambda{b. gt_bool{'a;'b}}}} }

interactive inverse_of_le_bool :
	sequent { <H> >- 'a in int } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- ge_bool{'a;'b}=(inverse_order{lambda{a.lambda{b. le_bool{'a;'b}}}} 'a 'b) in bool }

interactive int_ge_boolIsUnstrictTotalOrder :
	sequent { <H> >- isUnstrictTotalOrder{int; lambda{a.lambda{b. ge_bool{'a;'b}}}} }

interactive maxIntro {| intro [intro_typeinf <<'a>>] |} 'car :
	[wf] sequent { <H> >- 'a in 'car } -->
	[wf] sequent { <H> >- 'b in 'car } -->
	[wf] sequent { <H> >- 'x in 'car } -->
	[wf] sequent { <H> >- isRelation{'car;'rel} } -->
	sequent { <H> >- "assert"{'rel 'a 'x} } -->
	sequent { <H> >- "assert"{'rel 'b 'x} } -->
	sequent { <H> >- "assert"{'rel (max{'rel} 'a 'b) 'x} }

interactive minIntro {| intro [intro_typeinf <<'a>>] |} 'car :
	[wf] sequent { <H> >- 'a in 'car } -->
	[wf] sequent { <H> >- 'b in 'car } -->
	[wf] sequent { <H> >- 'x in 'car } -->
	[wf] sequent { <H> >- isRelation{'car;'rel} } -->
	sequent { <H> >- "assert"{'rel 'x 'a} } -->
	sequent { <H> >- "assert"{'rel 'x 'b} } -->
	sequent { <H> >- "assert"{'rel 'x (min{'rel} 'a 'b)} }

doc <:doc<
   @begin[doc]
   @modsubsection{Record wrappers of previously defined concepts}

   @end[doc]
>>

define unfold_relation : relation[i:l, rel:t] <-->
	record[rel:t]{r. 'r^car -> 'r^car -> bool; {car: univ[i:l]} }

define unfold_preorder1 : preorder[i:l,rel:t] <-->
   { O: relation[i:l,rel:t] | isPreorder{'O^car; 'O^rel} }

define unfold_unstrictPartialOrder1 : unstrictPartialOrder[i:l,rel:t] <-->
   { O: relation[i:l,rel:t] | isUnstrictPartialOrder{'O^car; 'O^rel} }

define unfold_strictPartialOrder1 : strictPartialOrder[i:l,rel:t] <-->
   { O: relation[i:l,rel:t] | isStrictPartialOrder{'O^car; 'O^rel} }

define unfold_unstrictTotalOrder1 : unstrictTotalOrder[i:l,rel:t] <-->
   { O: unstrictPartialOrder[i:l,rel:t] | isLinear{'O^car; 'O^rel} }

define unfold_strictTotalOrder1 : strictTotalOrder[i:l,rel:t] <-->
   { O: strictPartialOrder[i:l,rel:t] | isTrichotomous{'O^car; 'O^rel} }

doc docoff

let unfold_preorder = unfold_preorder1 thenC addrC [Subterm 1] unfold_relation thenC addrC [Subterm 2] unfold_isPreorder
let unfold_unstrictPartialOrder = unfold_unstrictPartialOrder1 thenC addrC [Subterm 1] unfold_relation thenC addrC [Subterm 2] unfold_isUnstrictPartialOrder
let unfold_strictPartialOrder = unfold_strictPartialOrder1 thenC addrC [Subterm 1] unfold_relation thenC addrC [Subterm 2] unfold_isStrictPartialOrder

let fold_relation = makeFoldC << relation[i:l,rel:t] >> unfold_relation
let fold_preorder1 = makeFoldC << preorder[i:l,rel:t] >> unfold_preorder1
let fold_unstrictPartialOrder1 = makeFoldC << unstrictPartialOrder[i:l,rel:t] >> unfold_unstrictPartialOrder1
let fold_strictPartialOrder1 = makeFoldC << strictPartialOrder[i:l,rel:t] >> unfold_strictPartialOrder1
let fold_unstrictTotalOrder1 = makeFoldC << unstrictTotalOrder[i:l,rel:t] >> unfold_unstrictTotalOrder1
let fold_strictTotalOrder1 = makeFoldC << strictTotalOrder[i:l,rel:t] >> unfold_strictTotalOrder1

let unstrictPartialOrderDT n = rw unfold_unstrictPartialOrder1 n thenT dT n

let resource elim += [
   <<unstrictPartialOrder[i:l,rel:t]>>, unstrictPartialOrderDT;
	]

doc <:doc<
   @begin[doc]
   Well-formedness rules
   @end[doc]
>>
interactive relation_wf {| intro [] |} :
   sequent { <H> >- relation[i:l,rel:t] Type }

interactive relation_intro {| intro [] |} :
   sequent { <H> >- 'R in record[rel:t]{r. 'r^car -> 'r^car -> bool; {car: univ[i:l]} } } -->
   sequent { <H> >- 'R in relation[i:l,rel:t] }

interactive relation_elim {| elim [] |} 'H :
   sequent { <H>; R: record[rel:t]{r. 'r^car -> 'r^car -> bool; {car: univ[i:l]} }; <J['R]> >- 'C['R] } -->
   sequent { <H>; R: relation[i:l,rel:t]; <J['R]> >- 'C['R] }

interactive isReflexive_wf2 {| intro [intro_typeinf <<'R>>] |} relation[i:l,rel:t] :
   sequent { <H> >- 'R in relation[i:l,rel:t] } -->
	sequent { <H> >- isReflexive{'R^car; 'R^rel} Type }

interactive isIrreflexive_wf2 {| intro [intro_typeinf <<'R>>] |} relation[i:l,rel:t] :
   sequent { <H> >- 'R in relation[i:l,rel:t] } -->
	sequent { <H> >- isIrreflexive{'R^car; 'R^rel} Type }

interactive isTransitive_wf2 {| intro [intro_typeinf <<'R>>] |} relation[i:l,rel:t] :
   sequent { <H> >- 'R in relation[i:l,rel:t] } -->
	sequent { <H> >- isTransitive{'R^car; 'R^rel} Type }

interactive isPreorder_wf2 {| intro [intro_typeinf <<'R>>] |} relation[i:l,rel:t] :
   sequent { <H> >- 'R in relation[i:l,rel:t] } -->
	sequent { <H> >- isPreorder{'R^car; 'R^rel} Type }

interactive preorder_wf {| intro [] |} :
	sequent { <H> >- preorder[i:l,rel:t] Type }

interactive preorder_intro {| intro [] |} :
   sequent { <H> >- 'R in relation[i:l,rel:t] } -->
	sequent { <H> >- isPreorder{'R^car; 'R^rel} } -->
   sequent { <H> >- 'R in preorder[i:l,rel:t] }

interactive isAntisym_wf2 {| intro [intro_typeinf <<'R>>] |} relation[i:l,rel:t] :
   sequent { <H> >- 'R in relation[i:l,rel:t] } -->
	sequent { <H> >- isAntisym{'R^car; 'R^rel} Type }

interactive isUnstrictPartialOrder_wf2 {| intro [intro_typeinf <<'R>>] |} relation[i:l,rel:t] :
   sequent { <H> >- 'R in relation[i:l,rel:t] } -->
	sequent { <H> >- isUnstrictPartialOrder{'R^car; 'R^rel} Type }

interactive unstrictPartialOrder_wf {| intro [] |} :
	sequent { <H> >- unstrictPartialOrder[i:l,rel:t] Type }

interactive unstrictPartialOrder_intro {| intro [] |} :
   sequent { <H> >- 'R in relation[i:l,rel:t] } -->
	sequent { <H> >- isReflexive{'R^car; 'R^rel} } -->
	sequent { <H> >- isTransitive{'R^car; 'R^rel} } -->
	sequent { <H> >- isAntisym{'R^car; 'R^rel} } -->
   sequent { <H> >- 'R in unstrictPartialOrder[i:l,rel:t] }

interactive isStrictPartialOrder_wf2 {| intro [intro_typeinf <<'R>>] |} relation[i:l,rel:t] :
   sequent { <H> >- 'R in relation[i:l,rel:t] } -->
	sequent { <H> >- isStrictPartialOrder{'R^car; 'R^rel} Type }

interactive strictPartialOrder_wf {| intro [] |} :
	sequent { <H> >- strictPartialOrder[i:l,rel:t] Type }

interactive strictPartialOrder_intro {| intro [] |} :
   sequent { <H> >- 'R in relation[i:l,rel:t] } -->
	sequent { <H> >- isIrreflexive{'R^car; 'R^rel} } -->
	sequent { <H> >- isTransitive{'R^car; 'R^rel} } -->
   sequent { <H> >- 'R in strictPartialOrder[i:l,rel:t] }

interactive isLinear_wf2 {| intro [intro_typeinf <<'R>>] |} relation[i:l,rel:t] :
   sequent { <H> >- 'R in relation[i:l,rel:t] } -->
	sequent { <H> >- isLinear{'R^car; 'R^rel} Type }

interactive unstrictTotalOrder_intro {| intro [] |} :
   sequent { <H> >- 'R in relation[i:l,rel:t] } -->
	sequent { <H> >- isReflexive{'R^car; 'R^rel} } -->
	sequent { <H> >- isTransitive{'R^car; 'R^rel} } -->
	sequent { <H> >- isAntisym{'R^car; 'R^rel} } -->
	sequent { <H> >- isLinear{'R^car; 'R^rel} } -->
   sequent { <H> >- 'R in unstrictTotalOrder[i:l,rel:t] }

interactive isTrichotomous_wf2 {| intro [intro_typeinf <<'R>>] |} relation[i:l,rel:t] :
   sequent { <H> >- 'R in relation[i:l,rel:t] } -->
	sequent { <H> >- isTrichotomous{'R^car; 'R^rel} Type }

interactive strictTotalOrder_intro {| intro [] |} :
   sequent { <H> >- 'R in relation[i:l,rel:t] } -->
	sequent { <H> >- isIrreflexive{'R^car; 'R^rel} } -->
	sequent { <H> >- isTransitive{'R^car; 'R^rel} } -->
	sequent { <H> >- isTrichotomous{'R^car; 'R^rel} } -->
   sequent { <H> >- 'R in strictTotalOrder[i:l,rel:t] }


