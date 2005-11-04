(
doc <:doc<
   This file logs the effort of re-verifying that all the ITT Core rules are valid under the ``pairwise'' semantics of
   sequents. We assume that each rule was already found valid in the ``pointwise'' semantics.
>>

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_equal.trueIntro {| intro [] |} :
   sequent { <H> >- "true" } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_equal.equalityAxiom {| nth_hyp |} 'H :
   sequent { <H>; x: 'T; <J['x]> >- 'x in 'T } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_equal.equalityRef 'y :
   sequent { <H> >- 'x = 'y in 'T } -->
   sequent { <H> >- 'x in 'T } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_equal.equalitySym :
   sequent { <H> >- 'y = 'x in 'T } -->
   sequent { <H> >- 'x = 'y in 'T } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_equal.equalityTrans 'z :
   sequent { <H> >- 'x = 'z in 'T } -->
   sequent { <H> >- 'z = 'y in 'T } -->
   sequent { <H> >- 'x = 'y in 'T } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_equal.equalityFormation 'T :
   [main] ('a : sequent { <H> >- 'T }) -->
   [main] ('b : sequent { <H> >- 'T }) -->
   sequent { <H> >- univ[i:l] } =
   'a = 'b in 'T

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_equal.equalityEquality {| intro [] |} :
   [wf] sequent { <H> >- 'T1 = 'T2 in univ[i:l] } -->
   [wf] sequent { <H> >- 'a1 = 'a2 in 'T1 } -->
   [wf] sequent { <H> >- 'b1 = 'b2 in 'T1 } -->
   sequent { <H> >- ('a1 = 'b1 in 'T1) = ('a2 = 'b2 in 'T2) in univ[i:l] } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_equal.equalityType {| intro [] |} :
   [wf] sequent { <H> >- 'a in 'T } -->
   [wf] sequent { <H> >- 'b in 'T } -->
   sequent { <H> >- ('a = 'b in 'T) Type } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_equal.axiomMember {| intro [] |} :
   [wf] sequent { <H> >- 'a = 'b in 'T } -->
   sequent { <H> >- it in ('a = 'b in 'T) } =
   it

doc <:doc< In << 'a = 'b in 'T >>, <<it>> is the only member, so the rule is trivially true >>
   
(*OK*) prim itt_equal.equalityElimination {| elim [] |} 'H :
   ('t['x] : sequent { <H>; x: 'a = 'b in 'T; <J[it]> >- 'C[it] }) -->
   sequent { <H>; x: 'a = 'b in 'T; <J['x]> >- 'C['x] } =
   't[it]

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_equal.type_axiomMember {| intro [] |} :
   sequent { <H> >- 'T Type } -->
   sequent { <H> >- it in ('T Type) } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_equal.typeEquality :
   [main] sequent { <H> >- 'T } -->
   sequent { <H> >- 'T Type } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_equal.universeMember :
   sequent { <H> >- cumulativity[j:l, i:l] } -->
   sequent { <H> >- univ[j:l] in univ[i:l] } =
  it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_equal.universeCumulativity univ[j:l] :
   sequent { <H> >- cumulativity[j:l, i:l] } -->
   sequent { <H> >- 'x = 'y in univ[j:l] } -->
   sequent { <H> >- 'x = 'y in univ[i:l] } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_equal.universeMemberType univ[i:l] :
   [wf] sequent { <H> >- 'x in univ[i:l] } -->
   sequent { <H> >- 'x Type } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_equal.universeFormation univ[j:l] :
   sequent { <H> >- cumulativity[j:l, i:l] } -->
   sequent { <H> >- univ[i:l] } =
   univ[j:l]

doc <:doc< In pairwise, the truth semantics of a sequent is monotone  >>

(*OK*) prim itt_struct.thin_many 'H 'J :
   ('t : sequent { <H>; <K> >- 'C }) -->
   sequent { <H>; <J>; < K<|H|> > >- 'C<|H;K|> } =
   't

doc <:doc< ... and commutative (for independent hyps). >>

(*OK*) prim itt_struct.exchange 'H 'K 'L:
   ('t : sequent { <H>; <L>; <K>; <J> >- 'C }) -->
   sequent { <H>; <K>; < L<|H|> >; <J> >- 'C } =
   't

doc <:doc< A and A : we proved it >>
   
(*OK*) prim itt_struct.cut 'H 'S :
   [assertion] ('a : sequent { <H>; <J> >- 'S }) -->
   [main] ('f['x] : sequent { <H>; x: 'S; <J> >- 'T }) -->
   sequent { <H>; <J> >- 'T } =
   'f['a]

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_struct.introduction 't :
   [wf] sequent { <H> >- 't in 'T } -->
   sequent { <H> >- 'T } =
   't

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_struct.substitution ('t1 = 't2 in 'T2) bind{x. 'T1['x]} :
   [equality] sequent { <H> >- 't1 = 't2 in 'T2 } -->
   [main] ('t : sequent { <H> >- 'T1['t2] }) -->
   [wf] sequent { <H>; x: 'T2 >- "type"{'T1['x]} } -->
   sequent { <H> >- 'T1['t1] } =
   't

doc <:doc< In pairwise semantic, much stronger hypReplacement is valid; this one may be derived >>

(*OK*) prim itt_struct.hypReplacement 'H 'B univ[i:l] :
   [main] ('t['x] : sequent { <H>; x: 'B; <J['x]> >- 'T['x] }) -->
   [equality] sequent { <H>; x: 'A; <J['x]> >- 'A = 'B<|H|> in univ[i:l] } -->
   sequent { <H>; x: 'A; <J['x]> >- 'T['x] } =
   't['x]

doc <:doc< And the same is true here as well >>
   
(*OK*) prim itt_struct.hypSubstitution 'H ('t1 = 't2 in 'T2) bind{y. 'A['y]} :
   [equality] sequent { <H>; x: 'A['t1]; <J['x]> >- 't1 = 't2<|H|> in 'T2 } -->
   [main] ('t['x] : sequent { <H>; x: 'A['t2]; <J['x]> >- 'T1['x] }) -->
   [wf] sequent { <H>; x: 'A['t1]; <J['x]>; z: 'T2 >- "type"{'A['z]} } -->
   sequent { <H>; x: 'A['t1]; <J['x]> >- 'T1['x] } =
   't['x]

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_squash.squashEquality {| intro [] |} :
   [wf] sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   sequent { <H> >- squash{'A1} = squash{'A2} in univ[i:l] } = it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_squash.squashType {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- "type"{squash{'A}} } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_squash.squashMemberFormation {| intro [AutoMustComplete] |} :
   sequent { <H> >- 'A } -->
   sequent { <H> >- squash{'A} } =
   it

doc <:doc< Since <<'J>> does not depend on a variable here, the pairwise and pointwise semantics still agree >>
   
(*OK*) prim itt_squash.unsquashEqualWeak 'H :
   sequent { <H>; 'P; <J> >- 'x = 'y in 'A } -->
   sequent { <H>; squash{'P}; <J> >- 'x = 'y in 'A } =
   it

doc <:doc< Since << squash{'P} >> has << it >> as its only member, the rule is trivially true >>
   
(*OK*) prim itt_squash.squashElim 'H :
   ('t['u] : sequent { <H>; u: squash{'P}; <J[it]> >- 'C[it] }) -->
   sequent { <H>; u: squash{'P}; <J['u]> >- 'C['u] } =
   't[it]

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_squiggle.squiggleEquality {| intro [] |} :
  [wf] sequent{ <H> >- 't1 ~ 's1 } -->
  [wf] sequent{ <H> >- 't2 ~ 's2 } -->
  sequent{ <H> >- ('t1 ~ 's1) = ('t2 ~ 's2) in univ[i:l]} =
  it

doc <:doc< Since << 't ~ 's >> has << it >> as its only member, the rule is trivially true >>

(*OK*) prim itt_squiggle.squiggleElimination {| elim [ThinOption thinT] |} 'H :
   ('f['x] : sequent{ <H>; x: ('t ~ 's); <J[it]> >- 'C[it] }) -->
   sequent { <H>; x: ('t ~ 's); <J['x]> >- 'C['x] } =
   'f['x]

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_squiggle.squiggleRef {| intro [] |} :
   sequent { <H> >- 't ~ 't } =
   it

doc <:doc< The rule does not deal with equality in any fashion >>

(*OK*) prim itt_squiggle.squiggleHypSubstitution 'H ('t ~ 's) bind{x. 'A['x]}:
   [equality] sequent { <H>; x: 'A['t]; <J['x]> >- 't ~ 's } -->
   [main] ('f['x]: sequent { <H>; x: 'A['s]; <J['x]> >- 'C['x] }) -->
   sequent { <H>; x: 'A['t]; <J['x]> >- 'C['x] } =
   'f['x]

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_subtype.subtypeEquality {| intro [] |} :
   [wf] sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent { <H> >- 'B1 = 'B2 in univ[i:l] } -->
   sequent { <H> >- 'A1 subtype 'B1 = 'A2 subtype 'B2 in univ[i:l] } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_subtype.subtypeType {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- "type"{'B} } -->
   sequent { <H> >- "type"{'A subtype 'B} } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_subtype.subtypeTypeRight 'B :
   [main] sequent { <H> >- 'A subtype 'B } -->
   sequent { <H> >- "type"{'A} } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_subtype.subtypeTypeLeft 'A :
   [main] sequent { <H> >- 'A subtype 'B }  -->
   sequent { <H> >- "type"{'B} } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_subtype.subtype_axiomFormation {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [main] sequent { <H>; x: 'A >- 'x in 'B } -->
   sequent { <H> >- 'A subtype 'B } =
   it

doc <:doc< Since << 'A subtype 'B >> has << it >> as its only member, the rule is trivially true >>

(*OK*) prim itt_subtype.subtypeElimination {| elim [ThinOption thinT] |} 'H :
   ('t['x] : sequent { <H>; x: 'A subtype 'B; <J[it]> >- 'C[it] }) -->
   sequent { <H>; x: 'A subtype 'B; <J['x]> >- 'C['x] } =
   't[it]

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_subtype.useSubtype 'A :
   sequent { <H> >- 'A subtype 'B } -->
   sequent { <H> >- 'a = 'b in 'A } -->
   sequent { <H> >- 'a = 'b in 'B } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_void.voidEquality {| intro [] |} :
   sequent { <H> >- void in univ[i:l] } =
   it

doc <:doc< Obvious >>

(*OK*) prim itt_void.voidElimination {| elim []; squash; nth_hyp |} 'H :
   sequent { <H>; x: void; <J['x]> >- 'C['x] } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_unit.unitEquality {| intro [] |} :
   sequent { <H> >- unit in univ[i:l] } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_unit.unit_memberEquality {| intro []; squash |} :
   sequent { <H> >- it in unit } =
   it

doc <:doc< Since << unit >> has << it >> as its only member, the rule is trivially true >>

(*OK*) prim itt_unit.unitElimination {| elim [ThinOption thinT] |} 'H :
   ('t['x] : sequent{ <H>; x: unit; <J[it]> >- 'C[it] }) -->
   sequent { <H>; x: unit; <J['x]> >- 'C['x] } =
   't[it]

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_unit.unitSqequal {| nth_hyp |} :
   sequent { <H> >- 'x = 'y in unit } -->
   sequent { <H> >- 'x ~ 'y } = it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_atom.atomEquality {| intro [] |} :
   sequent { <H> >- atom in univ[i:l] } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_atom.tokenEquality {| intro [] |} :
   sequent { <H> >- token[t:t] in atom } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_atom.atomSqequal {| nth_hyp |} :
   sequent { <H> >- 'x = 'y in atom } -->
   sequent { <H> >- 'x ~ 'y } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_set.setEquality {| intro [] |} :
   [wf] sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent { <H>; a1: 'A1 >- 'B1['a1] = 'B2['a1] in univ[i:l] } -->
   sequent { <H> >- { a1:'A1 | 'B1['a1] } = { a2:'A2 | 'B2['a2] } in univ[i:l] } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_set.setType {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H>; a: 'A >- "type"{'B['a]} } -->
   sequent { <H> >- "type"{ { a:'A | 'B['a] } } } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_set.setMemberEquality {| intro [] |} :
   [wf] sequent { <H> >- 'a1 = 'a2 in 'A } -->
   [assertion] sequent { <H> >- squash{'B['a1]} } -->
   [wf] sequent { <H>; a: 'A >- "type"{'B['a]} } -->
   sequent { <H> >- 'a1 = 'a2 in { a:'A | 'B['a] } } =
   it

doc <:doc< A and A: this is fairly straightforward >>

(*OK*) prim itt_set.setElimination {| elim [] |} 'H :
   ('t['u;'i] : sequent { <H>; u: 'A; i: squash{'B['u]}; <J['u]> >- 'T['u] }) -->
   sequent { <H>; u: { x:'A | 'B['x] }; <J['u]> >- 'T['u] } =
   't['u;it]

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_set.setFormation 'A :
   [wf] sequent { <H> >- 'A = 'A in univ[i:l] } -->
   ('B['a] : sequent { <H>; a: 'A >- univ[i:l] }) -->
   sequent { <H> >- univ[i:l] } =
   { a: 'A | 'B['a] }

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_union.unionFormation :
   ('A : sequent { <H> >- univ[i:l] }) -->
   ('B : sequent { <H> >- univ[i:l] }) -->
   sequent { <H> >- univ[i:l] } =
   'A + 'B

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_union.unionEquality {| intro [] |} :
   [wf] sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent { <H> >- 'B1 = 'B2 in univ[i:l] } -->
   sequent { <H> >- 'A1 + 'B1 = 'A2 + 'B2 in univ[i:l] } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_union.unionType {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- "type"{'B} } -->
   sequent { <H> >- "type"{'A + 'B} } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_union.inlFormation {| intro [SelectOption 1] |} :
   [main] ('a : sequent { <H> >- 'A }) -->
   [wf] sequent { <H> >- "type"{'B} } -->
   sequent { <H> >- 'A + 'B } =
   inl{'a}

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_union.inrFormation {| intro [SelectOption 2] |} :
   [main] ('b : sequent { <H> >- 'B }) -->
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- 'A + 'B } =
   inr{'b}

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_union.inlEquality {| intro [] |} :
   [wf] sequent { <H> >- 'a1 = 'a2 in 'A } -->
   [wf] sequent { <H> >- "type"{'B} } -->
   sequent { <H> >- inl{'a1} = inl{'a2} in 'A + 'B } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_union.inrEquality {| intro [] |} :
   [wf] sequent { <H> >- 'b1 = 'b2 in 'B } -->
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- inr{'b1} = inr{'b2} in 'A + 'B } =
   it

doc <:doc< A and A: fairly straightforward >>

(*OK*) prim itt_union.unionElimination {| elim [ThinOption thinT] |} 'H :
   [left] ('left['u;'p] : sequent { <H>; p: 'A + 'B; u: 'A; <J[inl{'u}]> >- 'T[inl{'u}] }) -->
   [right] ('right['v;'p] : sequent { <H>; p: 'A + 'B; v: 'B; <J[inr{'v}]> >- 'T[inr{'v}] }) -->
   sequent { <H>; x: 'A + 'B; <J['x]> >- 'T['x] } =
   decide{'x; u. 'left['u;'x]; v. 'right['v;'x]}

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_union.decideEquality {| intro [] |} bind{z. 'T['z]} ('A + 'B) :
   [wf] sequent { <H> >- 'e1 = 'e2 in 'A + 'B } -->
   [wf] sequent { <H>; u: 'A; 'e1 = inl{'u} in 'A + 'B >- 'l1['u] = 'l2['u] in 'T[inl{'u}] } -->
   [wf] sequent { <H>; v: 'B; 'e1 = inr{'v} in 'A + 'B >- 'r1['v] = 'r2['v] in 'T[inr{'v}] } -->
   sequent { <H> >- decide{'e1; u1. 'l1['u1]; v1. 'r1['v1]} =
                    decide{'e2; u2. 'l2['u2]; v2. 'r2['v2]} in
                    'T['e1] } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_union.unionSubtype {| intro [] |} :
   ["subtype"] sequent { <H> >- 'A1 subtype 'A2 } -->
   ["subtype"] sequent { <H> >- 'B1 subtype 'B2 } -->
   sequent { <H> >- 'A1 + 'B1 subtype 'A2 + 'B2  } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_dprod.productFormation 'A :
   [wf] sequent { <H> >- 'A in univ[i:l] } -->
   [main] ('B['x] : sequent { <H>; x: 'A >- univ[i:l] }) -->
   sequent { <H> >- univ[i:l] } =
   x:'A * 'B['x]

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_dprod.productEquality {| intro [] |} :
   [wf] sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent { <H>; x1: 'A1 >- 'B1['x1] = 'B2['x1] in univ[i:l] } -->
   sequent { <H> >- x1:'A1 * 'B1['x1] = x2:'A2 * 'B2['x2] in univ[i:l] } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_dprod.productType {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A1} } -->
   [wf] sequent { <H>; x: 'A1 >- "type"{'A2['x]} } -->
   sequent { <H> >- "type"{x:'A1 * 'A2['x]} } =
   it

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_dprod.pairEquality {| intro [] |} :
   [wf] sequent { <H> >- 'a1 = 'a2 in 'A } -->
   [wf] sequent { <H> >- 'b1 = 'b2 in 'B['a1] } -->
   [wf] sequent { <H>; x: 'A >- "type"{'B['x]} } -->
   sequent { <H> >- ('a1, 'b1) = ('a2, 'b2) in x:'A * 'B['x] } =
   it

doc <:doc< A and A: this is fairly straightforward >>

(*OK*) prim itt_dprod.productElimination {| elim [ThinOption thinT] |} 'H :
   ('t['z; 'x; 'y] : sequent { <H>; z: x:'A * 'B['x]; x: 'A; y: 'B['x]; <J['x, 'y]> >- 'T['x, 'y] }) -->
   sequent { <H>; z: x:'A * 'B['x]; <J['z]> >- 'T['z] } =
   spread{'z; x, y. 't['z; 'x; 'y]}

doc <:doc< Introduction rules have identical semantics in pairwise and pointwise, no need to re-verify >>

(*OK*) prim itt_dprod.spreadEquality bind{z. 'T['z]} (w:'A * 'B['w]) :
   [wf] sequent { <H> >- 'e1 = 'e2 in w:'A * 'B['w] } -->
   [wf] sequent { <H>; u: 'A; v: 'B['u]; a: 'e1 = ('u, 'v) in w:'A * 'B['w] >-
             'b1['u; 'v] = 'b2['u; 'v] in 'T['u, 'v] } -->
   sequent { <H> >- spread{'e1; u1, v1. 'b1['u1; 'v1]} = spread{'e2; u2, v2. 'b2['u2; 'v2]} in 'T['e1] } =
   it

prim itt_dfun.functionEquality {| intro [] |} :
   [wf] sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent { <H>; a1: 'A1 >- 'B1['a1] = 'B2['a1] in univ[i:l] } -->
   sequent { <H> >- (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[i:l] }
   = it

prim itt_dfun.functionType {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H>; a: 'A >- "type"{'B['a]} } -->
   sequent { <H> >- "type"{ a:'A -> 'B['a] } }
   = it

prim itt_dfun.lambdaFormation {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [main] ('b['a] : sequent { <H>; a: 'A >- 'B['a] }) -->
   sequent { <H> >- a:'A -> 'B['a] }
   = lambda{a.'b['a]}

prim itt_dfun.lambdaEquality {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H>; a1: 'A >- 'b1['a1] = 'b2['a1] in 'B['a1] } -->
   sequent { <H> >- lambda{a1. 'b1['a1]} = lambda{a2. 'b2['a2]} in a:'A -> 'B['a] }
   = it

prim itt_dfun.functionExtensionality (y:'C -> 'D['y]) (z:'E -> 'F['z]) :
   [main] sequent { <H>; x: 'A >- ('f 'x) = ('g 'x) in 'B['x] } -->
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- 'f in y:'C -> 'D['y] } -->
   [wf] sequent { <H> >- 'g in z:'E -> 'F['z] } -->
   sequent { <H> >- 'f = 'g in x:'A -> 'B['x] }
   = it

prim itt_dfun.functionElimination {| elim [] |} 'H 'a :
   [wf] sequent { <H>; f: x:'A -> 'B['x]; <J['f]> >- 'a in 'A } -->
   ('t['f; 'y; 'it] : sequent { <H>; f: x:'A -> 'B['x]; <J['f]>; y: 'B['a]; it: 'y = ('f 'a) in 'B['a] >- 'T['f] }) -->
   sequent { <H>; f: x:'A -> 'B['x]; <J['f]> >- 'T['f] }
   = 't['f; 'f 'a; it]

prim itt_dfun.applyEquality {| intro[intro_typeinf <<'f1>>; complete_unless_member] |} (x:'A -> 'B['x]) :
   sequent { <H> >- 'f1 = 'f2 in x:'A -> 'B['x] } -->
   sequent { <H> >- 'a1 = 'a2 in 'A } -->
   sequent { <H> >- ('f1 'a1) = ('f2 'a2) in 'B['a1] }
   = it

prim itt_esquash.esquash_type {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- "type"{'P} } -->
   sequent { <H> >- "type"{esquash{'P}} } =
   it

prim itt_esquash.esquash_equal {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- esquash{'P1} in univ[i:l] } -->
   [wf] sequent { <H> >- esquash{'P2} in univ[i:l] } -->
   sequent { <H>; esquash{'P1} >- esquash{'P2} } -->
   sequent { <H>; esquash{'P2} >- esquash{'P1} } -->
   sequent { <H> >- esquash{'P1} = esquash{'P2} in univ[i:l] } =
   it

prim itt_esquash.esquash_univ :
   [wf] sequent { <H> >- 'P in univ[i:l] } -->
   sequent { <H> >- esquash{'P} in univ[i:l] } =
   it

prim itt_esquash.esquash_intro {| intro [AutoMustComplete] |} :
   [main] sequent { <H> >- squash{'P} } -->
   sequent { <H> >- esquash{'P} } =
   it

prim itt_esquash.esquash_elim {| elim [] |} 'H :
   ( 't['x] : sequent { <H>; x: esquash{'A}; <J[it]> >- 'C[it] }) -->
   sequent { <H>; x: esquash{'A}; <J['x]> >- 'C['x] } =
   't[it]

prim itt_esquash.esquash :
   [wf] sequent { <H> >- "type"{'P} } -->
   sequent { <H> >- esquash{'P} } -->
   sequent { <H> >- squash{'P} } =
   it

prim itt_list.listType {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- "type"{list{'A}} } =
   it

prim itt_list.listEquality {| intro [] |} :
   [wf] sequent { <H> >- 'A = 'B in univ[i:l] } -->
   sequent { <H> >- list{'A} = list{'B} in univ[i:l] } =
   it

prim itt_list.nilEquality {| intro [] |} :
   [wf] sequent { <H> >- "type"{list{'A}} } -->
   sequent { <H> >- nil in list{'A} } =
   it

prim itt_list.consEquality {| intro [] |} :
   [wf] sequent { <H> >- 'u1 = 'u2 in 'A } -->
   [wf] sequent { <H> >- 'v1 = 'v2 in list{'A} } -->
   sequent { <H> >- cons{'u1; 'v1} = cons{'u2; 'v2} in list{'A} } =
   it

prim itt_list.list_indEquality {| intro [] |} bind{l. 'T['l]} list{'A} :
   [wf] sequent { <H> >- 'e1 = 'e2 in list{'A} } -->
   [wf] sequent { <H> >- 'base1 = 'base2 in 'T[nil] } -->
   [wf] sequent { <H>; u: 'A; v: list{'A}; w: 'T['v] >-
             'step1['u; 'v; 'w] = 'step2['u; 'v; 'w] in 'T['u::'v]
           } -->
   sequent { <H> >- list_ind{'e1; 'base1; u1, v1, z1. 'step1['u1; 'v1; 'z1]}
                   = list_ind{'e2; 'base2; u2, v2, z2. 'step2['u2; 'v2; 'z2]}
                   in 'T['e1]
           } =
   it

prim itt_list.listElimination {| elim [ThinOption thinT] |} 'H :
   [main] ('base['l] : sequent { <H>; l: list{'A}; <J['l]> >- 'C[nil] }) -->
   [main] ('step['l; 'u; 'v; 'w] : sequent { <H>; l: list{'A}; <J['l]>; u: 'A; v: list{'A}; w: 'C['v] >- 'C['u::'v] }) -->
   sequent { <H>; l: list{'A}; <J['l]> >- 'C['l] } =
   list_ind{'l; 'base['l]; u, v, w. 'step['l; 'u; 'v; 'w]}

prim itt_list.nilSqequal {| nth_hyp |} 'T :
   sequent { <H> >- 'u = nil in list{'T} } -->
   sequent { <H> >- 'u ~ nil } =
   it

prim ../extensions/itt_pairwise.let_rule 'H ('z='s in 'S):
  [assertion] sequent { <H>; <J> >- 's in 'S } -->
   [main]    ('t['x; 'u]:  sequent { <H>; x: 'S;  <J>; u:'s ~ 'x  >- 'T } )-->
   sequent { <H>; <J>  >- 'T}
      = 't['s; it]

prim itt_int_base.int_sqequal {| nth_hyp |} :
   sequent { <H> >- 'a = 'b in int } -->
   sequent { <H> >- 'a ~ 'b } = it

prim itt_int_base.intEquality {| intro [] |} :
   sequent { <H> >- int in univ[i:l] } = it

prim itt_int_base.numberFormation {| intro [] |} number[n:n] :
   sequent { <H> >- int } = number[n:n]

prim itt_int_base.add_wf {| intro [complete_unless_member] |} :
   [wf] sequent { <H> >- 'a = 'a1 in int } -->
   [wf] sequent { <H> >- 'b = 'b1 in int } -->
   sequent { <H> >- 'a +@ 'b = 'a1 +@ 'b1 in int } = it

prim itt_int_base.minus_wf {| intro [] |} :
   [wf] sequent { <H> >- 'a = 'a1 in int } -->
   sequent { <H> >- (-'a) = (-'a1) in int } = it

prim itt_int_base.lt_bool_wf {| intro [complete_unless_member] |} :
   sequent { <H> >- 'a='a1 in int } -->
   sequent { <H> >- 'b='b1 in int } -->
   sequent { <H> >- lt_bool{'a; 'b} = lt_bool{'a1; 'b1} in bool } = it

prim itt_int_base.beq_wf {| intro [complete_unless_member] |} :
   [wf] sequent { <H> >- 'a = 'a1 in int } -->
   [wf] sequent { <H> >- 'b = 'b1 in int } -->
   sequent { <H> >- beq_int{'a; 'b} = beq_int{'a1; 'b1} in bool } = it

prim itt_int_base.beq_int2prop :
   [main] sequent { <H> >- "assert"{beq_int{'a; 'b}} } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- 'a = 'b in int } = it

prim itt_int_base.beq_int_is_true {| nth_hyp |} :
   sequent { <H> >- 'a = 'b in int } -->
   sequent { <H> >- beq_int{'a; 'b} ~ btrue } = it

prim itt_int_base.numberEquality {| intro [] |} :
   sequent { <H> >- number[n:n] in int } = it

prim itt_int_base.lt_Reflex :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- band{lt_bool{'a; 'b}; lt_bool{'b; 'a}} ~ bfalse } =
 it

prim itt_int_base.lt_Trichot :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent {
     <H> >- bor{bor{lt_bool{'a; 'b};lt_bool{'b; 'a}}; beq_int{'a; 'b}} ~ btrue
 } = it

prim itt_int_base.lt_Transit 'b :
   [main] sequent {
      <H> >- band{lt_bool{'a; 'b};lt_bool{'b; 'c}} = btrue in bool } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- lt_bool{'a; 'c} ~ btrue } = it

prim itt_int_base.lt_Discret :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- lt_bool{'a; 'b} ~
                          bor{beq_int{('a +@ 1); 'b}; lt_bool{('a +@ 1); 'b}} }
 = it

prim itt_int_base.intElimination {| elim [ThinOption thinT] |} 'H :
   ( 'down['n; 'm; 'v; 'z] :
      sequent { <H>; n: int; <J['n]>; m: int; v: 'm < 0; z: 'C['m +@ 1]
 >- 'C['m] } ) -->
   ( 'base['n] : sequent { <H>; n: int; <J['n]> >- 'C[0] } ) -->
   ( 'up['n; 'm; 'v; 'z] :
      sequent { <H>; n: int; <J['n]>; m: int; v: 0 < 'm; z: 'C['m -@ 1]
 >- 'C['m] } ) -->
   sequent { <H>; n: int; <J['n]> >- 'C['n] } =
      ind{'n; m, z. 'down['n; 'm; it; 'z]; 'base['n]; m, z. 'up['n; 'm; it; 'z]}

prim itt_int_base.add_Commut :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a +@ 'b) ~ ('b +@ 'a) } = it

prim itt_int_base.add_Assoc :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- ('a +@ ('b +@ 'c)) ~ (('a +@ 'b) +@ 'c) } = it

prim itt_int_base.add_Id {| nth_hyp |} :
   [wf] sequent { <H> >- 'a in int } -->
   sequent { <H> >- ('a +@ 0) ~ 'a } = it

prim itt_int_base.lt_addMono :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- lt_bool{('a +@ 'c); ('b +@ 'c)} ~ lt_bool{'a; 'b} } =
 it

prim itt_int_base.minus_add_inverse {| nth_hyp |} :
   [wf] sequent { <H> >- 'a in int } -->
   sequent { <H> >- ( 'a +@ (- 'a ) ) ~ 0 } = it

prim itt_int_ext.mul_wf {| intro [complete_unless_member] |} :
   [wf] sequent { <H> >- 'a = 'a1 in int } -->
   [wf] sequent { <H> >- 'b = 'b1 in int } -->
   sequent { <H> >- 'a *@ 'b = 'a1 *@ 'b1 in int } = it

prim itt_int_ext.mul_Commut :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a *@ 'b) ~ ('b *@ 'a) } = it

prim itt_int_ext.mul_Assoc :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- ('a *@ ('b *@ 'c)) ~ (('a *@ 'b) *@ 'c) } = it

prim itt_int_ext.mul_add_Distrib :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- ('a *@ ('b +@ 'c)) ~ (('a *@ 'b) +@ ('a *@ 'c)) } = it

prim itt_int_ext.mul_Id {| nth_hyp |} :
   [wf] sequent { <H> >- 'a in int } -->
   sequent { <H> >- (1 *@ 'a) ~ 'a } = it

prim itt_int_ext.mul_Zero {| nth_hyp |} :
   [wf] sequent { <H> >- 'a in int } -->
   sequent { <H> >- (0 *@ 'a) ~ 0 } = it

prim itt_int_ext.rem_baseReduce :
   sequent { <H> >- 0 <= 'a } -->
   sequent { <H> >- 'a < 'b } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a %@ 'b) ~ 'a } = it

prim itt_int_ext.rem_neg :
   sequent { <H> >- 'b <> 0 } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a %@ 'b) ~ ('a %@ (-'b)) } = it

prim itt_int_ext.rem_indReduce :
   sequent { <H> >- 'b <> 0 } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- ((('a *@ 'b) +@ 'c) %@ 'b) ~ ('c %@ 'b) } = it

prim itt_int_ext.div_baseReduce :
   sequent { <H> >- 0 <= 'a } -->
   sequent { <H> >- 'a < 'b } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a /@ 'b) ~ 0 } = it

prim itt_int_ext.div_neg :
   sequent { <H> >- 'b <> 0 } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a /@ 'b) ~ ((-'a) /@ (-'b)) } = it

prim itt_int_ext.div_indReduce :
   sequent { <H> >- 'b <> 0 } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- ((('a *@ 'b) +@ 'c) /@ 'b) ~ ('a +@ ('c /@ 'b)) } = it

prim itt_atom_bool.eq_atom_wf {| intro [] |} :
   [wf] sequent { <H> >- 'x in atom } -->
   [wf] sequent { <H> >- 'y in atom } -->
   sequent { <H> >- eq_atom{'x; 'y} in bool } =
   it

prim itt_atom_bool.eq_atom_assert_intro {| intro [] |} :
   [wf] sequent { <H> >- 'x = 'y in atom } -->
   sequent { <H> >- "assert"{eq_atom{'x; 'y}} } =
   it

prim itt_atom_bool.eq_atom_assert_elim {| elim [] |} 'H :
   [main] sequent { <H>; x: 'a = 'b in atom; <J[it]> >- 'C[it] } -->
   sequent { <H>; x: "assert"{eq_atom{'a; 'b}}; <J['x]> >- 'C['x] } =
   it

prim itt_isect.intersectionFormation 'A :
   [wf] sequent { <H> >- 'A in univ[i:l] } -->
   ('B['x] : sequent { <H>; x: 'A >- univ[i:l] }) -->
   sequent { <H> >- univ[i:l] } =
   Isect x: 'A. 'B['x]

prim itt_isect.intersectionEquality {| intro [] |} :
   [wf] sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent { <H>; y: 'A1 >- 'B1['y] = 'B2['y] in univ[i:l] } -->
   sequent { <H> >- Isect x1: 'A1. 'B1['x1] = Isect x2: 'A2. 'B2['x2] in univ[i:l] } =
   it

prim itt_isect.intersectionType {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H>; y: 'A >- "type"{'B['y]} } -->
   sequent { <H> >- "type"{"isect"{'A; x. 'B['x]}} } =
   it

prim itt_isect.intersectionMemberEquality {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H>; z: 'A >- 'b1 = 'b2 in 'B['z] } -->
   sequent { <H> >- 'b1 = 'b2 in Isect x: 'A. 'B['x] } =
   it

prim itt_isect.intersectionElimination {| elim [] |} 'H 'a :
   [wf] sequent { <H>; x: Isect y: 'A. 'B['y]; <J['x]> >- 'a in 'A } -->
   [main] ('t['x; 'z] : sequent { <H>; x: Isect y: 'A. 'B['y]; <J['x]>; z: 'B['a] >- 'T['z] }) -->
   sequent { <H>; x: Isect y: 'A. 'B['y]; <J['x]> >- 'T['x] } =
   't['x; 'x]

prim itt_disect.dintersectionFormation 'A :
   [wf] sequent { <H> >- 'A = 'A in univ[i:l] } -->
   ('B['x] : sequent { <H>; x: 'A >- univ[i:l] }) -->
   sequent { <H> >- univ[i:l] } =
   bisect{'A; x.'B['x]}

prim itt_disect.dintersectionEquality {| intro [] |} :
   [wf] sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent { <H>; y: 'A1 >- 'B1['y] = 'B2['y] in univ[i:l] } -->
   sequent { <H> >- bisect{'A1; x1.'B1['x1]} = bisect{'A2; x2.'B2['x2]} in univ[i:l] } =
   it

prim itt_disect.dintersectionType {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H>; y: 'A >- "type"{'B['y]} } -->
   sequent { <H> >- "type"{bisect{'A; x. 'B['x]}} } =
   it

prim itt_disect.dintersectionTypeElimination {| elim [ThinOption thinT] |} 'H 'a :
   [wf] sequent { <H>; u:"type"{bisect{'A; x. 'B['x]}}; <J['u]>  >- 'a in 'A } -->
   ('t['u;'v] :
   sequent { <H>; u:"type"{bisect{'A; x. 'B['x]}}; v:"type"{'B['a]}; <J['u]> >- 'C['u] }) -->
   sequent { <H>; u:"type"{bisect{'A; x. 'B['x]}}; <J['u]> >- 'C['u] } =
   't['u;it]

prim itt_disect.dintersectionMemberEquality {| intro [] |} :
   [wf] sequent { <H>; x:'A >- "type"{'B['x]} } -->
   sequent { <H> >- 't1 = 't2 in 'A } -->
   sequent { <H> >- 't1 = 't2 in 'B['t1] } -->
   sequent { <H> >- 't1 = 't2 in bisect{'A; x.'B['x]} } =
   it

prim itt_disect.disectElimination {| elim [] |} 'H bind{a,b.'T['a;'b]}:
   [main] ('t['x; 'a; 'b] :
   sequent { <H>; x: bisect{'A; y.'B['y]}; <J['x]>;  a:'A; b: 'B['a]  >- 'T['a;'b] }) -->
   sequent { <H>; x: bisect{'A; y.'B['y]}; <J['x]> >- 'T['x;'x] } =
   't['x; 'x; 'x]

prim itt_disect.dintersectionSubtype :
   ["subtype"] sequent { <H> >- \subtype{'A1; 'A2} } -->
   ["subtype"] sequent { <H>; a: 'A1 >- \subtype{'B1['a]; 'B2['a]} } -->
   sequent { <H> >- \subtype{ bisect{'A1; a1.'B1['a1]}; bisect{'A2; a2.'B2['a2]} } } =
   it

prim itt_image.img_type {| intro [] |}:
   sequent { <H> >- 'A Type } -->
   sequent { <H> >- Img{'A; x.'f<||>['x]} Type } = it

prim itt_image.img_univ {| intro [] |}:
   sequent { <H> >- 'A in univ[i:l] } -->
   sequent { <H> >- Img{'A; x.'f<||>['x]} in univ[i:l] } = it

prim itt_image.img_mem 'a :
   sequent { <H> >- 'a in 'A } -->
   sequent { <H> >- 'f['a] in Img{'A; x.'f<||>['x]} } = it

prim itt_image.img_elim {| elim [ThinOption thinT] |} 'H :
   sequent { <H>; y: Img{'A; x.'f<||>['x]}; <J['y]>; a: 'A >- squash{'C['f['a]]} } -->
   sequent { <H>; y: Img{'A; x.'f<||>['x]}; <J['y]> >- squash{'C['y]} } = it

prim itt_inv_typing.dintersectionTypeElimination {| elim [ThinOption thinT] |} 'H 'a :
   [wf] sequent { <H>; u:"type"{bisect{'A; x. 'B['x]}}; <J['u]>  >- 'a in 'A } -->
   ('t['u;'v] :
   sequent { <H>; u:"type"{bisect{'A; x. 'B['x]}}; v:"type"{'B['a]}; <J['u]> >- 'C['u] }) -->
   sequent { <H>; u:"type"{bisect{'A; x. 'B['x]}}; <J['u]> >- 'C['u] } =
   't['u;it]

prim itt_inv_typing.independentProductTypeElimination {| elim [ThinOption thinT] |} 'H :
   ('t['u;'v;'w] :
   sequent { <H>; u:"type"{'A * 'B}; v:"type"{'A}; w:"type"{'B}; <J['u]> >- 'C['u] }) -->
   sequent { <H>; u:"type"{'A * 'B}; <J['u]> >- 'C['u] } =
   't['u;it;it]

prim itt_inv_typing.functionTypeElimination {| elim [ThinOption thinT] |} 'H :
   ('t['u;'v; 'w] :
   sequent { <H>; u:"type"{'A -> 'B }; v:"type"{'A}; w:('A -> "type"{'B}); <J['u]> >- 'C['u] }) -->
   sequent { <H>; u:"type"{'A -> 'B }; <J['u]> >- 'C['u] } =
   't['u;it;it]

prim itt_w.wFormation 'A :
   sequent { <H> >- 'A = 'A in univ[i:l] } -->
   ('B['x] : sequent { <H>; x: 'A >- univ[i:l] }) -->
   sequent { <H> >- univ[i:l] } =
   w{'A; x. 'B['x]}

prim itt_w.wEquality {| intro [] |} :
   [wf] sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent { <H>; y: 'A1 >- 'B1['y] = 'B2['y] in univ[i:l] } -->
   sequent { <H> >- w{'A1; x1. 'B1['x1]} = w{'A2; x2. 'B2['x2]} in univ[i:l] } =
   it

prim itt_w.wType {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A1} } -->
   [wf] sequent { <H>; x: 'A1 >- "type"{'A2['x]} } -->
   sequent { <H> >- "type"{w{'A1; y.'A2['y]}} } =
   it

prim itt_w.treeFormation {| intro [] |} 'a :
   [wf] sequent { <H> >- 'a = 'a in 'A } -->
   [main] ('f : sequent { <H> >- 'B['a] -> w{'A; x. 'B['x]} }) -->
   [wf] sequent { <H>; y: 'A >- "type"{'B['y]} } -->
   sequent { <H> >- w{'A; x. 'B['x]} } =
   tree{'a; 'f}

prim itt_w.treeEquality {| intro [] |} :
   [wf] sequent { <H> >- 'a1 = 'a2 in 'A } -->
   [wf] sequent { <H> >- 'b1 = 'b2 in 'B['a1] -> w{'A; x. 'B['x]} } -->
   [wf] sequent { <H>; y: 'A >- "type"{'B['y]} } -->
   sequent { <H> >- tree{'a1; 'b1} = tree{'a2; 'b2} in w{'A; x. 'B['x]} } =
   it

prim itt_w.wElimination {| elim [ThinOption thinT] |} 'H :
   [main] ('t['z; 'a; 'f; 'g] :
   sequent { <H>;
                    z: w{'A; x. 'B['x]};
                    <J['z]>;
                    a: 'A;
                    f: 'B['a] -> w{'A; x. 'B['x]};
                    g: b: 'B['a] -> 'T['f 'b]
                  >- 'T[tree{'a; 'f}]
                  }) -->
   sequent { <H>; z: w{'A; x. 'B['x]}; <J['z]> >- 'T['z] } =
      tree_ind{'z; a, f, g. 't['z; 'a; 'f; 'g]}

prim itt_prec.precEquality {| intro [] |} 'A :
   [wf] sequent { <H> >- 'a1 = 'a2 in 'A } -->
   [wf] sequent { <H>; x: 'A; T: 'A -> univ[i:l] >- 'B1['T; 'x] = 'B2['T; 'x] in univ[i:l] } -->
   [wf] sequent { <H>;
             P1: 'A -> univ[i:l];
             P2: 'A -> univ[i:l];
             z: x:'A -> \subtype{('P1 'x); ('P2 'x)};
             x: 'A;
             y: 'B1['P1; 'x]
           >- 'y = 'y in 'B1['P2; 'x]
           } -->
   sequent { <H> >- "prec"{A1, x1. 'B1['A1; 'x1]; 'a1}
                   = "prec"{A2, x2. 'B2['A2; 'x2]; 'a2}
                   in univ[i:l]
           } =
   it

prim itt_prec.precMemberFormation {| intro [] |} :
   [main] ('t : sequent { <H> >- 'B[lambda{z. "prec"{T, x. 'B['T; 'x]; 'z}}; 'a] }) -->
   [wf] sequent { <H> >- "type"{("prec"{T, x. 'B['T; 'x]; 'a})} } -->
   sequent { <H> >- "prec"{T, x. 'B['T; 'x]; 'a} } =
   't

prim itt_prec.precMemberEquality {| intro [] |} :
   [wf] sequent { <H> >- "type"{("prec"{T, x. 'B['T; 'x]; 'a})} } -->
   [wf] sequent { <H> >- 'a1 = 'a2 in 'B[lambda{z. "prec"{T, x. 'B['T; 'x]; 'z}}; 'a] } -->
   sequent { <H> >- 'a1 = 'a2 in "prec"{T, x. 'B['T; 'x]; 'a} } =
   it

prim itt_prec.precElimination {| elim [ThinOption thinT] |} 'H lambda{z. 'G['z]} 'A univ[i:l] :
   [wf] sequent { <H>; r: "prec"{T, x. 'B['T; 'x]; 'a}; <J['r]> >- 'a in 'A } -->
   [main] ('g['r; 'Z; 'u; 'p; 'h] : sequent { <H>; r: "prec"{T, x. 'B['T; 'x]; 'a}; <J['r]>;
      Z: 'A -> univ[i:l];
      u: \subtype{(a: 'A * 'Z 'a); (a: 'A * "prec"{T, x. 'B['T; 'x]; 'a})};
      h: p: (a: 'A * 'Z 'a) -> 'G['p];
      p: a: 'A * 'B['Z; 'a]
   >- 'G['p]
   }) -->
   sequent { <H>; r: "prec"{T, x. 'B['T; 'x]; 'a}; <J['r]> >- 'G['a] } =
   precind{'a; p, h. 'g['r; lambda{x.void}; lambda{x. it}; 'p; 'h]}

prim itt_prec.precUnrollElimination {| elim [ThinOption thinT] |} 'H :
   ('g['r; 'y; 'u] : sequent { <H>; r: "prec"{T, x. 'B['T; 'x]; 'a}; <J['r]>;
             y: 'B[lambda{z. "prec"{T, x. 'B['T; 'x]; 'z}}; 'a];
             u: 'r = 'y in 'B[lambda{z. "prec"{T, x. 'B['T; 'x]; 'z}}; 'a]
             >- 'G['y]
           }) -->
   sequent { <H>; r: "prec"{T, x. 'B['T; 'x]; 'a}; <J['r]> >- 'G['r] } =
   'g['r; 'r; it]

prim itt_prec.precindEquality {| intro [] |} lambda{x. 'S['x]} (a:'A * "prec"{T, y. 'B['T; 'y]; 'a}) univ[i:l] :
   [wf] sequent { <H> >- 'r1 = 'r2 in a: 'A * "prec"{T, y. 'B['T; 'y]; 'a} } -->
   [wf] sequent { <H>; Z: 'A -> univ[i:l];
             u: \subtype{(a: 'A * 'Z 'a); (a: 'A * "prec"{T, x. 'B['T; 'x]; 'a})};
             h: z: (a: 'A * 'Z 'a) -> 'S['z];
             z: a: 'A * 'B['Z; 'a]
             >- 't1['h; 'z] = 't2['h; 'z] in 'S['z]
           } -->
   sequent { <H> >- precind{'r1; h1, z1. 't1['h1; 'z1]}
                   = precind{'r2; h2, z2. 't2['h2; 'z2]}
                   in 'S['r1]
           } =
   it

prim itt_srec.srecFormation :
   ('B['T] : sequent { <H>; T: univ[i:l] >- univ[i:l] }) -->
   sequent { <H> >- univ[i:l] } =
   srec{T. 'B['T]}

prim itt_srec.srecEquality {| intro [] |} :
   [wf] sequent { <H>; T: univ[i:l] >- 'B1['T] = 'B2['T] in univ[i:l] } -->
   [wf] sequent { <H>; S1: univ[i:l]; S2: univ[i:l]; z: \subtype{'S1; 'S2} >- \subtype{'B1['S1]; 'B1['S2]} } -->
   sequent { <H> >- srec{T1. 'B1['T1]} = srec{T2. 'B2['T2]} in univ[i:l] } =
   it

prim itt_srec.srec_memberFormation {| intro [] |} :
   [wf] ('g : sequent { <H> >- 'B[srec{T. 'B['T]}] }) -->
   [wf] sequent { <H> >- "type"{(srec{T. 'B['T]})} } -->
   sequent { <H> >- srec{T. 'B['T]} } =
   'g

prim itt_srec.srec_memberEquality {| intro [] |} :
   sequent { <H> >- 'x1 = 'x2 in 'B[srec{T. 'B['T]}] } -->
   [wf] sequent { <H> >- "type"{(srec{T. 'B['T]})} } -->
   sequent { <H> >- 'x1 = 'x2 in srec{T. 'B['T]} } =
   it

prim itt_srec.srecElimination {| elim [ThinOption thinT] |} 'H univ[i:l] :
   [main] ('g['x; 'T; 'u; 'w; 'z] : sequent {
             <H>;
             x: srec{X. 'B['X]};
             <J['x]>;
             T: univ[i:l];
             u: \subtype{'T; srec{X. 'B['X]}};
             w: all v:'T. 'C['v];
             z: 'B['T]
           >- 'C['z]
           }) -->
   sequent { <H>; x: srec{X. 'B['X]}; <J['x]> >- 'C['x] } =
   srecind{'x; p, h. 'g['x; srec{X. 'B['X]}; it; 'p; 'h]}

prim itt_srec.srecUnrollElimination (* {| elim [ThinOption thinT] |} *) 'H :
   [main] ('g['x; 'y; 'u] : sequent { <H>; x: srec{T. 'B['T]}; <J['x]>; y: 'B[srec{T. 'B['T]}]; u: 'x = 'y in 'B[srec{T. 'B['T]}] >- 'C['y] }) -->
   sequent { <H>; x: srec{T. 'B['T]}; <J['x]> >- 'C['x] } =
   'g['x; 'x; it]

prim itt_srec.srecindEquality {| intro [] |} bind{x. 'S['x]} srec{T. 'B['T]} univ[i:l] :
   [wf] sequent { <H> >- 'r1 = 'r2 in srec{T. 'B['T]} } -->
   [wf] sequent { <H>; r: srec{T. 'B['T]} >- "type"{'S['r]} } -->
   [wf] sequent { <H>; T1: univ[i:l]; z: \subtype{'T1; srec{T. 'B['T]}};
               v: w: 'T1 -> 'S['w]; w: 'B['T1]
           >- 't1['v; 'w] = 't2['v; 'w] in 'S['w]
           } -->
   sequent { <H> >- srecind{'r1; h1, z1. 't1['h1; 'z1]}
                   = srecind{'r2; h2, z2. 't2['h2; 'z2]}
                   in 'S['r1]
           } =
   it

prim itt_quotient.quotientType {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H>; u: 'A; v: 'A >- "type"{'E['u; 'v]} } -->
   [wf] sequent { <H>; u: 'A >- 'E['u; 'u] } -->
   [wf] sequent { <H>; u: 'A; v: 'A; 'E['u; 'v] >- 'E['v; 'u] } -->
   [wf] sequent { <H>; u: 'A; v: 'A; w: 'A; 'E['u; 'v]; 'E['v; 'w] >- 'E['u; 'w] } -->
   sequent { <H> >- "type"{quot x, y: 'A // 'E['x; 'y]} } =
   it

prim itt_quotient.quotientEquality {| intro [] |} :
   [wf] sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent { <H>; x: 'A1; y: 'A1 >- 'E1['x; 'y] = 'E2['x; 'y] in univ[i:l] } -->
   [wf] sequent { <H> >- "type"{quot x1, y1: 'A1 // 'E1['x1; 'y1]} } -->
   sequent { <H> >- quot x1, y1: 'A1 // 'E1['x1; 'y1]
                   = quot x2, y2: 'A2 // 'E2['x2; 'y2]
                   in univ[i:l]
           } =
   it

prim itt_quotient.quotient_memberWeakEquality {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- "type"{(quot x, y: 'A // 'E['x; 'y])} } -->
   [wf] sequent { <H> >- 'a1 = 'a2 in 'A } -->
   sequent { <H> >- 'a1 = 'a2 in quot x, y: 'A // 'E['x; 'y] } =
   it

prim itt_quotient.quotient_memberEquality :
   [wf] sequent { <H> >- 'a1 in quot x, y: 'A // 'E['x; 'y] } -->
   [wf] sequent { <H> >- 'a2 in quot x, y: 'A // 'E['x; 'y] } -->
   sequent { <H> >- esquash{'E['a1; 'a2]} } -->
   sequent { <H> >- 'a1 = 'a2 in quot x, y: 'A // 'E['x; 'y] } =
   it

prim itt_quotient.quotientElimination1 {| elim [ThinOption thinT] |} 'H :
   [wf] sequent { <H>; a: quot x, y: 'A // 'E['x; 'y]; <J['a]> >- "type"{'T['a]} } -->
   [main] sequent { <H>; a: quot x, y: 'A // 'E['x; 'y]; <J['a]>;
             v: 'A; w: 'A; z: 'E['v; 'w] >- 's['v] = 't['w] in 'T['v]
           } -->
   sequent { <H>; a: quot x, y: 'A // 'E['x; 'y]; <J['a]> >- 's['a] = 't['a] in 'T['a] } =
   it

prim itt_quotient.quotient_equalityElimination {| elim [ThinOption thinT] |} 'H :
   [main] ('g['e; 'v] : sequent { <H>; e: 'a1 = 'a2 in quot x, y: 'A // 'E['x; 'y]; <J['e]>; v: esquash{'E['a1; 'a2]} >- 'T['e] }) -->
   sequent { <H>; e: 'a1 = 'a2 in quot x, y: 'A // 'E['x; 'y]; <J['e]> >- 'T['e] } =
   'g['e; it]

prim itt_record_label.labelMember {| intro [] |} :
   sequent { <H> >- label[t:t] in label } =
   it

prim itt_record_label.reduce_eq_label_true {| intro [] |} :
   sequent{ <H> >- label[x:t] = label[y:t]  in label} -->
   sequent{ <H> >- eq_label[x:t,y:t]{'A;'B} ~ 'A}
      = it

prim itt_record_label.reduce_eq_label_false {| intro [] |} :
   sequent{ <H> >- label[x:t] <> label[y:t]  in label} -->
   sequent{ <H> >- eq_label[x:t,y:t]{'A;'B} ~ 'B}
      = it

