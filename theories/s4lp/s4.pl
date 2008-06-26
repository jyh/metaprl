takeout(X,[X|R],R).
takeout(X,[F|R],[F|S]) :- takeout(X,R,S).

takeoutAll([], From, From).
takeoutAll([X|R], From, To) :-
	takeout(X, From, To0),
	takeoutAll(R, To0, To).

newMember(E, [E|T]).
newMember(E, [H|T]) :- nonvar(H), newMember(E, T).

proof(axiom(S), Gamma, Delta, leaf) :-
	member(S, Gamma),
	member(S, Delta).

proof(axiomFalse, Gamma, Delta, leaf) :-
	member(false, Gamma).

proof(negLeft(A), Gamma, Delta, chain(Derivation)) :-
	takeout(neg(A), Gamma, Gamma1),
	Derivation = proof(Rule, Gamma1, [A|Delta], Branches),
	Derivation.

proof(implLeft(A, B), Gamma, Delta, branches(DerivationA, DerivationB)) :-
	takeout(impl(A,B), Gamma, Gamma1),
	DerivationA = proof(RuleA, Gamma1, [A|Delta], BranchesA),
	DerivationB = proof(RuleB, [B|Gamma1], Delta, BranchesB),
	DerivationA,
	DerivationB.
	
proof(implRight(A, B), Gamma, Delta, chain(Derivation)) :-
	takeout(impl(A,B), Delta, Delta1),
	Derivation = proof(Rule, [A|Gamma], [B|Delta1], Branches),
	Derivation.

collectBoxes([box(A)|L], Boxes) :-
	Boxes = [box(A)| R],
	collectBoxes(L, R).
collectBoxes([Nonbox|L], Boxes) :- collectBoxes(L, Boxes).
collectBoxes([], []).

proof(boxRight(B), Gamma, Delta, chain(Derivation)) :-
	member(box(B), Delta),
	collectBoxes(Gamma, Boxes),
	Derivation = proof(Rule, Boxes, [B], Branches),
	Derivation.

proof(boxLeft(A), Gamma, Delta, chain(Derivation)) :-
	member(box(A), Gamma),
	not(member(A, Gamma)),
	!,
	Derivation = proof(Rule, [A|Gamma], Delta, Branches),
	Derivation.

/* proof(Rule, [], [impl(a, impl(b,a))], Branches).
solve(proof(Rule, [], [impl(box(a), box(box(a)))], Branches)).
*/

prove(F, Proof) :-
	Proof = proof(Rule, [], [F], Branches),
	Proof.

/*
from
node(box(a), branches(node(box(a), leaf), node(box(a), leaf)))

to
node(pr(plus([X,Y]),a), branches(node(pr(plus([X,Y]), a), leaf), node(pr(plus([X,Y]), a), leaf)))
*/

assignTerm(box(F0), pr(T, F1), Map0, Map, Start, End) :-
	assignTerm(F0, F1, Map0, Map1, Start, End0),
	T = plus(W),
	member(c(End0), W),
	Map = [ [box(F0), pr(T, F1)] | Map1],
	End is End0 + 1.

assignTerm(impl(A0, B0), impl(A1, B1), Map0, Map, Start, End) :-
	assignTerm(A0, A1, Map0, Map1, Start, Tmp),
	assignTerm(B0, B1, Map1, Map2, Tmp, End),
	Map = [ [impl(A0, B0), impl(A1, B1)] | Map2].

assignTerm(neg(A0), neg(A1), Map0, Map, Start, End) :-
	assignTerm(A0, A1, Map0, Map1, Start, End),
	Map = [ [neg(A0), neg(A1)] | Map1].

assignTerm(V, V, Map0, Map, Start, Start) :-
	print('Var '),print(V),nl,
	Map = [ [V, V] | Map0].

assignTerms([F0|From], [F1|To], Map0, Map, Start, End) :-
	assignTerm(F0, F1, Map0, Map1, Start, End0),
	assignTerms(From, To, Map1, Map, End0, End).

assignTerms([], [], Map, Map, Start, Start).

assignFamily(proof(boxLeft(A), Gamma, Delta, chain(Derivation)), 
	     fProof(boxLeft(A1), Gamma1, Delta1, chain(Derivation1)),
	     Map0, Map,
	     Counter0, Counter) :-
	assignFamily(Derivation, Derivation1, Map0, Map, Counter0, Counter),
	member([A, A1], Map),
	member([box(A), pr(T, A2)], Map),
	print('1 A='),print(A),print(' A1='),print(A1),print(' T='),print(T),print(' A2='),print(A2),nl,
	A1=A2,
	Derivation1 = fProof(Rule1, Gamma2, Delta1, Derivation2),
	takeout(A1, Gamma2, Gamma1),
	print(Map),nl,
	print('2 A='),print(A),print(' A1='),print(A1),print(' T='),print(T),print(' A2='),print(A2),nl.

assignFamily(proof(boxRight(B), Gamma, Delta, chain(Derivation)),
	     fProof(boxRight(B1), Gamma1, Delta1, chain(Derivation1)),
             Map0, Map,
	     Counter0, Counter) :-
	/*print('Counter0='),print(Counter0),nl,*/
	assignFamily(Derivation, Derivation1, Map0, Map1, Counter0, Counter1),
	/*print('Counter1='),print(Counter1),nl,*/
	Derivation = proof(Rule, Boxes, [B], Branches),
	Derivation1 = fProof(Rule1, Boxes1, [B1], Derivation2),
	member([B, B1], Map1),
	takeout(box(B), Delta, Delta0),
	takeoutAll(Boxes, Gamma, Gamma0),
	assignTerms(Gamma0, Gamma2, Map1, Map2, Counter1, Counter2),
	/*print('Counter2='),print(Counter2),nl,*/
	assignTerms(Delta0, Delta2, Map2, Map3, Counter2, Counter3),
	/*print('Counter3='),print(Counter3),nl,*/
	append(Gamma2, Boxes1, Gamma1),
	T = pr(plus(W), B1),
	Delta1 = [T | Delta2],
	Map = [ [box(B), T] | Map3],
	Counter is Counter3 + 1,
	/*print('Counter='),print(Counter),nl,*/
	member(c(Counter3), W).

assignFamily(proof(axiom(S), Gamma, Delta, leaf),
	     fProof(axiom(S1), Gamma1, Delta1, leaf),
	     Map0, Map,
	     Counter0, Counter) :-
        takeout(S, Gamma, Gamma0),
        takeout(S, Delta, Delta0),
	assignTerm(S, S1, Map0, Map1, Counter0, Counter1),
	assignTerms(Gamma0, Gamma2, Map1, Map2, Counter1, Counter2),
	assignTerms(Delta0, Delta2, Map2, Map, Counter2, Counter),
	Gamma1 = [S1 | Gamma2],
	Delta1 = [S1 | Delta2].

assignFamily(proof(axiomFalse, Gamma, Delta, leaf),
	     fProof(axiomFalse, Gamma1, Delta1, leaf),
	     Map0, Map,
	     Counter0, Counter) :-
        assignTerms(Gamma, Gamma1, Map0, Map1, Counter0, Counter1),
        assignTerms(Delta, Delta1, Map1, Map, Counter1, Counter).

assignFamily(proof(implLeft(A, B), Gamma, Delta, branches(DerivationA, DerivationB)),
	     fProof(implLeft(A2, B2), Gamma2, Delta2, branches(DerivationA2, DerivationB2)),
	     Map0, Map,
	     Counter0, Counter) :-
	assignFamily(DerivationA, DerivationA2, Map0, Map1, Counter0, Counter1),
	assignFamily(DerivationB, DerivationB2, Map1, Map2, Counter1, Counter),
        DerivationA2 = fProof(RuleA, Gamma1, Delta2A2, BranchesA),
        DerivationB2 = fProof(RuleB, Gamma1B2, Delta2, BranchesB),
	member([A,A2], Map2),
	member([B,B2], Map2),
	Map = [[impl(A, B), impl(A2, B2)] | Map2],
	Gamma2 = [impl(A2, B2) | Gamma1].
	
assignFamily(proof(implRight(A, B), Gamma, Delta, chain(Derivation)),
	     fProof(implRight(A2, B2), Gamma2, Delta2, chain(Derivation2)),
	     Map0, Map,
	     Counter0, Counter) :-
	assignFamily(Derivation, Derivation2, Map0, Map1, Counter0, Counter),
	Derivation2 = fProof(Rule, Gamma2A2, Delta1B2, Branches),
	member([A, A2], Map1),
	member([B, B2], Map1),
	Map = [[impl(A, B), impl(A2, B2)] |  Map1],
	takeout(A2, Gamma2A2, Gamma2),
	takeout(B2, Delta1B2, Delta1),
	Delta2 = [impl(A2, B2) | Delta1].

assignFamily(proof(negLeft(A), Gamma, Delta, chain(Derivation)),
	     fProof(negLeft(A2), Gamma2, Delta2, chain(Derivation2)),
	     Map0, Map,
	     Counter0, Counter) :-
	assignFamily(Derivation, Derivation2, Map0, Map1, Counter0, Counter),
	Derivation2 = fProof(Rule, Gamma1, Delta2A2, Branches),
	member([A, A2], Map1),
	Gamma2 = [neg(A2) | Gamma1],
	takeout(A2, Delta2A2, Delta2), 
	Map = [[neg(A), neg(A2)] | Map1].

axiom(impl(A,impl(B,A))).
axiom(impl(impl(A,impl(B,C)),impl(impl(A,B),impl(A,C)))).
axiom(impl(pr(S,impl(A,B)),impl(pr(T,A),pr(prod(S,T),B)))).
axiom(impl(pr(T,A),A)).
axiom(impl(pr(T,A),pr(bang(T),pr(T,A)))).
axiom(impl(pr(T,A),pr(plus(L),A))) :- member(T,L).

lift([],[]).

lift([[axiom,H]|T], Lifted) :-
	lift(T,LiftedT),
	Lifted = [[axiom,pr(axiom(H),H)]|LiftedT].
	
lift([[mp,H]|T], Lifted) :-
	lift(T, LiftedT),
	member([_,pr(f, impl(A,H))], LiftedT),
	member([_,pr(a, A)], LiftedT),
	Lifted = [[mp,pr(prod(f,a), H)],[mp,impl(pr(a,A),pr(prod(f,a),H))],[axiom,impl(pr(f,impl(A,H),impl(pr(a,H),pr(prod(f,a),H)))]|LiftedT].

realize(proof(axiom(S), Gamma, Delta, leaf), fProof(axiom(SF), GammaF, DeltaF, leaf), Map,
	Tail, [[axiom,pr(axiomC(Start), impl(andL(GammaF), orL(DeltaF)))] | Tail], Start, End) :-
	End is Start+1.

realize(proof(axiomFalse, Gamma, Delta, leaf), fProof(axiomFalse, GammaF, DeltaF, leaf), Map,
	Tail, [[axiom,pr(axiomC(Start), impl(andL(GammaL), orL(DeltaF)))] | Tail], Start, End) :-
	End is Start+1.

realize(proof(boxLeft(A), Gamma, Delta, chain(Pr)), fProof(boxLeft(AF), GammaF, DeltaF, chain(PrF), Map,
		Tail, NewProof, Start, End) :- 
	realize(Pr, PrF, Map, Tail, NewProof0, Start, Tmp) :-
	NewProof0 = [[_,pr(T, F)]|_],
	NewF = impl(andL(GammaF), orL(DeltaF)),
	Lemma = pr(boxLeft(Tmp), impl(F, NewF)),
	NewProof = [[mp,pr(prod(boxLeft(Tmp), T), NewF)],[axiom,impl(Lemma,impl(pr(T,F),pr(prod(boxLeft(Tmp), T), NewF)))]|NewProof0],
	End is Tmp+1.

realize(proof(boxRight(A), Gamma, Delta, chain(Pr)), fProof(boxRight(AF), GammaF, DeltaF, chain(PrF), Map,
		Tail, NewProof, Start, end) :-
	realize(Pr, PrF, Map, Tail, NewProof0, Start, Tmp),
	NewProof0 = [[_,pr(T, F)]|_],
	F = impl(As,B),
	s = l3(As),
	L3 = impl(As, pr(s, As)),
	Lemma0 = impl(pr(s,As), pr(prod(T,s), B),
	Lemma1 = impl(As, pr(prod(T,s), B),
	Lemma2 = impl(As, AF),
	Lemma3 = pr(XXX, impl(Lemma2, NewF)),
	NewF = impl(andL(GammaF), orL(DeltaF)),
	Lemma = pr(boxRight(Tmp), impl(F, NewF)),
	NewProof = [pr(prod(boxRight(Tmp), T), NewF)|NewProof0]
	End is Tmp+1.

realize(proof(implLeft(A,B), Gamma, Delta, branches(BrA, BrB)), fProof(implLeft(AF,BF), GammaF, DeltaF, branches(BrAF, BrBF)), Map,
		Tail, NewProof, Start, End) :-
	realize(BrA, BrAF, Map, Tail, NewProof0, Start, Tmp0),
	realize(BrB, BrBF, Map, NewProof0, NewProof1, Tmp0, Tmp1),
	NewProof0 = [[_,pr(T0, F0)]|_],
	NewProof1 = [[_,pr(T1, F1)]|_],
	NewF = impl(andL(GammaF), orL(DeltaF)),
	Lemma = pr(implLeft(Tmp1), impl(F0, impl(F1, NewF))),
	NewProof = [[mp,pr(prod(prod(implLeft(Tmp1), T0), T1), newF)]|NewProof1),
	End is Tmp1+1.

realize(proof(implRight(A,B), Gamma, Delta, chain(Pr)), fProof(implRight(AF, BF), GammaF, DeltaF, chain(PrF)), Map,
		Tail, NewProof, Start, End) :-
	realize(Pr, PrF, Map, Tail, NewProof0, Start, Tmp),
	NewProof0 = [[_,pr(T, F)]|_],
	NewF = impl(andL(GammaF), orL(DeltaF)),
	Lemma = pr(implRight(Tmp), impl(F, NewF)),
	NewProf = [[mp,pr(prod(implRight(Tmp), T), NewF)]|NewProof0],
	End is Tmp+1.

realize(proof(negLeft(A), Gamma, Delta, chain(Pr), fProof(negLeft(AF), GammaF, DeltaF, chain(PrF)), Map,
		Tail, NewProof, Start, End) :-
	realize(Pr, PrF, Map, Tail, NewProof0, Start, Tmp),
	NewProof0 = [[_,pr(T, F)]|_],
	NewF = impl(andL(GammaF), orL(DeltaF)),
	Lemma = pr(negLeft(Tmp), impl(F, NewF)),
	NewProof = [[mp,pr(prod(negLeft(Tmp), T), NewF)]|NewProof0],
	End is Tmp+1.

/*
proof(
	boxLeft(neg(impl(s,box(s)))),
	[box(neg(impl(s,box(s))))],[],
	chain(proof(
		negLeft(impl(s,box(s))),
		[neg(impl(s,box(s))),box(neg(impl(s,box(s))))],[],
		chain(proof(
			implRight(s,box(s)),
			[box(neg(impl(s,box(s))))],[impl(s,box(s))],
			chain(proof(
				boxRight(s),
				[s,box(neg(impl(s,box(s))))],[box(s)],
				chain(proof(
					boxLeft(neg(impl(s,box(s)))),
					[box(neg(impl(s,box(s))))],[s],
					chain(proof(
						negLeft(impl(s,box(s))),
						[neg(impl(s,box(s))),box(neg(impl(s,box(s))))],[s],
						chain(proof(
							implRight(s,box(s)),
							[box(neg(impl(s,box(s))))],[impl(s,box(s)),s],
							chain(proof(
								axiom(s),
								[s,box(neg(impl(s,box(s))))],[box(s),s],
								leaf
							))
						))
					))
				))
			))
		))
	))
)
*/
