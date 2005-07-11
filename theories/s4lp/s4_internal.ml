open Hilbert_internal
open LP

module OrderedFormula =
struct

type family = int

type t =
	Falsum
 | Atom of symbol
 | And of formula * formula
 | Or of formula * formula
 | Neg of formula
 | Implies of formula * formula
 | Box of family * formula

let compare f1 f2 =
	match f1, f2 with
	 | Falsum, Falsum -> 0
	 | Falsum, (Atom _, And _ | Or _ | Neg _ | Implies _ | Box _) -> -1
	 | Atom _, Falsum -> 1
	 | Atom s1, Atom s2 -> Lm_symbol.compare s1 s2
	 | Atom _, (And _ | Or _ | Neg _ | Implies _ | Box _) -> -1
	 | And(f11,f12), (Falsum | Atom _) -> 1
	 | And p1, And p2 -> compare_pairs p1 p2
	 | And _, (Or _ | Neg _ | Implies _ | Box _) -> -1
	 | Or _, (Falsum | Atom _ | And _) -> 1
    | Or p1, Or p2 -> compare_pairs p1 p2
	 | Or _, (Neg _ | Implies _ | Box _) -> -1
	 | Neg _, (Falsum | Atom _ | And _ | Or _) -> 1
	 | Neg f1, Neg f2 -> compare f1 f2
	 | Neg _, (Implies _ | Box _) -> -1
	 | Implies _, (Falsum | Atom _ | And _ | Or _ | Neg _) -> 1
	 | Implies p1, Implies p2 -> compare_pairs p1 p2
	 | Implies _, Box _ -> 1
	 | Box _, (Falsum | Atom _ | And _ | Or _ | Neg _ | Implies _) -> 1
	 | Box(fam1,fml1), Box(fam2,fml2) ->
	 		let c = Pervasives.compare fam1 fam2 in
			if c = 0 then
				compare fml1 fml2
			else
				c

and compare_pairs (f11,f12) (f21,f22) =
   let c = compare f11 f21 in
   if c = 0 then
      compare f12 f22
   else
      c

end

let FSet = Lm_set.LmMake(OrderedFormula)

type derivation =
   NegLeft of formula * derivation
 | NegRight of formula * derivation
 | AndLeft of formula * derivation
 | AndRight of formula * derivation * derivation
 | OrLeft of formula * derivation * derivation
 | OrRight of formula * derivation
 | ImplLeft of formula * derivation * derivation
 | ImplRight of formula * derivation
 | BoxLeft of formula * derivation
 | BoxRight of formula * derivation
 | Axiom of formula
 | FalsumLeft

let rec realize d hyps concls =
	match d with
		(*NegLeft((Neg f0 as f), d0) ->
			let hyps0 = FSet.add (FSet.remove hyps f) f0 in
			let pterm0, concl0, hilb0 = realize d0 hyps0 concls in
			let hilb1, f1 = hilbert_neg_left hyps concls hyps0 hilb0 f0 in
			let hilb2, pterm2 = lift [] hilb1 f1 in
			App(pterm2, pterm0),
			one_implication hyps concls,
			LP.MP(
				concl0,
				hilb0,
				MP(
					Pr(pterm2, f1),
					hilb2,
					Axiom(12)
				)
			)*)
	 | ImplRight((Implies(f01,f02) as f) d0) ->
	 		let concls0 = FSet.add (FSet.remove concls f) f02 in
			let hyps0 = FSet.add hyps f01 in
			let pterm0, concl0, hilb0 = realize d0 hyps0 concls0 in
			let hilb1, f1 = hilbert_impl_right hyps concls hyps0 concls0 hilb0 f01 f02 in
			let hilb2, pterm2 = lift [] hilb1 f1 in
         App(pterm2, pterm0),
         one_implication hyps concls,
         MP(
            Pr(pterm0,concl0),
            hilb0,
            MP(
               Pr(pterm2, f1),
               hilb2,
               Axiom(12)
            )
         )
	 | ImplLeft((Implies(f01,f02) as f),d01,d02) ->
	 		let concls01 = FSet.add concls f01 in
			let hyps01 = FSet.remove hyps f in
			let concls02 = concls in
			let hyps02 = FSet.add hyps01 f02 in
			let pterm01, concl01, hilb01 = realize d01 hyps01 concls01 in
			let pterm02, concl02, hilb02 = realize d02 hyps02 concls02 in
			let hilb1, f1 =
				hilbert_impl_left
					hyps concls
					hyps01 concls01
					hyps02 concls02
					hilb01 hilb02
			in
			let hilb2, pterm2 = lift [] hilb1 f1 in
			App(App(pterm2, pterm02), pterm01),
			one_implication hyps concls,
			let subproof =
				MP(
					Pr(pterm01, concl01),
					hilb01,
					MP(
						Pr(pterm2,f1),
						hilb2,
						Axiom(12)
					)
				)
			in
			MP(
				Pr(pterm02,concl02),
				hilb02,
				MP(
					Pr(App(pterm2, pterm01), Implies(concl02, f1)),
					subproof,
					Axiom(12)
				)
			)
	 | Axiom f ->
	 		let hilb1, f1 = hilbert_axiom hyps concls f in
			let hilb2, pterm2 = lift [] hilb1 f1 in
			pterm2,
			one_implication hyps concls,
			hilb2
	 | FalsumLeft ->
	 		let hilb1, f1 = hilbert_falsum_left hyps concls f in
			let hilb2, pterm2 = lift [] hilb1 f1 in
			pterm2,
			one_implication hyps concls,
			hilb2
	 | BoxLeft((Box(fam,f0)) as f, d0) ->
	 		let hyps0 = FSet.add hyps f0 in
			let pterm0, concl0, hilb0 = realize d0 hyps0 concls in
			let hilb1, f1 = hilbert_box_left hyps concls hyps0 hilb0 in
			let hilb2, pterm2 = lift [] hilb1 f1 in
         App(pterm2, pterm0),
         one_implication hyps concls,
         MP(
            Pr(pterm0,concl0),
            hilb0,
            MP(
               Pr(pterm2, f1),
               hilb2,
               Axiom(12)
            )
         )
	 | BoxRight((Box(fam,f0)) as f, d0) ->
	 		let hyps0 = boxed_only_hyps hyps in
			let concls0 = FSet.singleton f0 in
			let pterm0, concl0, hilb0 = realize d0 hyps0 concls0 in

