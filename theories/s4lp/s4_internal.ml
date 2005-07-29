open Hilbert_internal
open Lm_int_set
open Lm_symbol
open LP
open OrderedFormula

type derivation =
   NegLeft of formula * derivation
 | NegRight of formula * derivation
 | AndLeft of formula * derivation
 | AndRight of formula * derivation * derivation
 | OrLeft of formula * derivation * derivation
 | OrRight of formula * derivation
 | ImplLeft of formula * formula * derivation * derivation
 | ImplRight of formula * formula * derivation
 | BoxLeft of formula * derivation
 | BoxRight of formula * FSet.t * FSet.t * derivation
 | Axiom of formula * FSet.t * FSet.t
 | FalsumLeft of FSet.t * FSet.t

let extract set item =
	let item_set, rest = FSet.partition (fun x -> compare item x = 0) set in
	FSet.choose item_set, rest

let map (info: IntSet.t IntTable.t) n f (set : FSet.t) =
	FSet.fold
		(fun (info, n, acc) fml ->
			let info', n', fml' = f info n fml in
			info', n', FSet.add acc fml'
		)
		(info, n, FSet.empty)
		set

let map2_aux f set2 info item =
	let item2, _ = extract set2 item in
	let info' = f info item item2 in
	info'

let map2 f info set1 set2 =
	FSet.fold (map2_aux f set2) info set1

let rec join_families info f1 f2 =
   match f1, f2 with
      Falsum, Falsum ->
			info
    | Implies(f11, f12), Implies(f21, f22) ->
	 		let info1 = join_families info f11 f21 in
			join_families info1 f12 f22
    | Box((Modal fam1) as m1, f10), Box((Modal fam2) as m2, f20) when fam_cmp m1 m2 = 0 ->
	 		join_families info f10 f20
    | Box(Evidence e1, f10), Box(Evidence e2, f20) ->
	 		let set1 = IntTable.find info e1 in
			let set2 = IntTable.find info e2 in
			let info1 = IntTable.remove (IntTable.remove info e1) e2 in
			let info2 = IntTable.add info1 e1 (IntSet.union set1 set2) in
			join_families info2 f10 f20
    | _ ->
         raise (Invalid_argument "assign_fresh_families: unsupported connective")

let rec assign_fresh_families info n f =
	match f with
		Falsum -> info, n, f
	 | Implies(f1, f2) ->
	 		let info1, n1, f1' = assign_fresh_families info n f1 in
			let info2, n2, f2' =  assign_fresh_families info1 n1 f2 in
			info2, n2, Implies(f1', f2')
	 | Box((Modal fam) as m, f0) ->
	 		let info', n', f0' = assign_fresh_families info n f0 in
			info', n', Box(m, f0')
	 | Box(Evidence _, f0) ->
	 		let info', n', f0' = assign_fresh_families info n f0 in
			let info'' = IntTable.add info' n' IntSet.empty in
			info'', succ n', Box(Evidence n', f0')
	 | _ ->
	 		raise (Invalid_argument "assign_fresh_families: unsupported connective")

let rec box2pr = function
   Falsum -> Falsum
 | Implies(f1, f2) ->
 		Implies(box2pr f1, box2pr f2)
 | Box((Modal fam) as m, f0) ->
      Box(m, box2pr f0)
 | Box(Evidence e, f0) ->
 		Pr(Provisional e, box2pr f0)
 | _ ->
      raise (Invalid_argument "box2pr: unsupported connective")

let box2pr_set set =
	FSet.fold (fun acc f -> FSet.add acc (box2pr f)) FSet.empty set

(*
let rec count_boxes_fml n = function
	Falsum ->
		n
 | Implies a, b ->
 		count_boxes_fml (count_boxes_fml n a) b
 | Box(Modal _, a) ->
 		count_boxes_fml n a
 | Box(Evidence _, a) ->
 		succ (count_boxes_fml n a)
 | _ ->
 		raise (Invalid_argument "count_boxes_fml: unsupported connective")

let rec count_boxes_set n set =
	FSet.fold (fun acc f -> count_boxes_fml acc f) n set

let rec count_boxes n = function
	ImplLeft _, _, d1, d2 ->
		let n1 = count_boxes n d1 in
		count_boxes n1 d2
 | ImplRight _, _, d ->
 		count_boxes n d
 | BoxLeft (_, d ->
 		count_boxes n d in
 | BoxRight _, d, hyps, concls ->
 		let n' = succ (count_boxes n d) in
		let n'' = count_boxes_set n' hyps in
		count_boxes_set n'' concls
 | Axiom f, hyps, concls ->
 		let n' = count_boxes_fml n f in
      let n'' = count_boxes_set n' hyps in
      count_boxes_set n'' concls
 | FalsumLeft hyps, concls ->
      let n' = count_boxes_set n hyps in
      count_boxes_set n' concls
 | _ ->
 		raise (Invalid_argument "count_boxes: a rule for an unsupported connective")
*)

let rec assign_families (info: IntSet.t IntTable.t) n = function
   ImplLeft(a, b, d1, d2) ->
      let info1, n1, d1', hyps1, concls1 = assign_families info n d1 in
      let info2, n2, d2', hyps2, concls2 = assign_families info1 n1 d2 in
      let a', concls1' = extract concls1 a in
      let b', hyps2' = extract hyps2 b in
      let info3 = map2 join_families info2 hyps1 hyps2' in
      let info4 = map2 join_families info3 concls1' concls2 in
      info4, n2, ImplLeft(a', b', d1', d2'), FSet.add hyps1 (Implies(a', b')), concls1'
 | ImplRight(a, b, d) ->
      let info', n', d', hyps, concls = assign_families info n d in
      let a', hyps' = extract hyps a in
      let b', concls' = extract concls b in
      info', n', ImplRight(a', b', d'), hyps', FSet.add concls' (Implies(a', b'))
 | BoxLeft(Box(Evidence _, a) as f, d) ->
      let info', n', d', hyps, concls = assign_families info n d in
      let a', hyps' = extract hyps a in
      let f', hyps'' = extract hyps' f in
      begin match f' with
         Box(Evidence i as e, a'') ->
            let info'' = join_families info' a' a'' in
            info'', n', BoxLeft(f', d'), FSet.add hyps'' f', concls
       | _ ->
            raise (Invalid_argument "assign_families bug: evidence box expected")
		end
 | BoxRight(Box(Evidence _, b) as f, hyps, concls, d) ->
      let info1, n1, hyps' = map info n assign_fresh_families hyps in
      let info2, n2, concls' = map info1 n1 assign_fresh_families concls in
      let info3, n3, d', hyps'', concls'' = assign_families info2 n2 d in
      begin match FSet.to_list concls'' with
         [b'] when compare b b' = 0 ->
            let f' = Box(Evidence n3, b') in
				let info4 = IntTable.add info3 n3 (IntSet.singleton n3) in
            info4, succ n3, BoxRight(f', hyps', concls', d'),
            FSet.union hyps' hyps'', FSet.add concls' f'
       | _ ->
            raise (Invalid_argument "assign_families bug: incompatible conclusions")
		end
 | Axiom(f, hyps, concls) ->
      let info1, n1, f' = assign_fresh_families info n f in
      let info2, n2, hyps' = map info1 n1 assign_fresh_families hyps in
      let info3, n3, concls' = map info2 n2 assign_fresh_families concls in
      info3, n3, Axiom(f', hyps', concls'), (FSet.add hyps' f'), (FSet.add concls' f')
 | FalsumLeft(hyps, concls) ->
      let info1, n1, hyps' = map info n assign_fresh_families hyps in
      let info2, n2, concls' = map info1 n1 assign_fresh_families concls in
      info2, n2, FalsumLeft(hyps', concls'), (FSet.add hyps' Falsum), concls'
 | _ ->
      raise (Invalid_argument "assign_families: a rule for an unsupported connective")

let allocate d =
	let info, n, d', hyps, concls = assign_families IntTable.empty 0 d in
	let ar = Array.make n IntSet.empty in
	IntTable.iter (fun _ set -> IntSet.iter (fun i -> ar.(i) <- set) set) info;
	ar, d', hyps, concls

let set2conj set =
	let last = FSet.max_elt set in
	let rest = FSet.remove set last in
	if FSet.is_empty rest then
		last
	else
		FSet.fold (fun acc f -> And(f, acc)) last rest

let set2disj set =
   let last = FSet.max_elt set in
   let rest = FSet.remove set last in
   if FSet.is_empty rest then
      last
   else
      FSet.fold (fun acc f -> Or(f, acc)) last rest

let one_implication hyps concls =
   let b =
		if FSet.is_empty concls then
			Falsum
		else
			set2disj concls
	in
	if FSet.is_empty hyps then
		b
	else
		let a = set2conj hyps in
		Implies(a, b)

(*
let hilbert_impl_right hyps concls hyps0 concls0 hilb0 concl0 f01 f02 =
	let concl = one_implication hyps concls in
	MP(
		concl0,
		hilb0,
		Hyp(new_number ())
	),
	Implies(concl0, concl)

let hilbert_impl_left
	hyps concls hyps01 concls01 concl01 hyps02 concls02 concl02 hilb01 hilb02
	=
	let concl = one_implication hyps concls in
	MP(
		concl02,
		hilb02,
		MP(
			concl01.
			hilb01,
			Hyp(new_number ())
		)
	),
	Implies(concl01, Implies(concl02, concl))
*)

let rec deduction_all hyps hilb f =
	match hyps with
		[] ->
			hilb, f
	 | h::rest ->
			let hilb' = deduction h rest hilb f in
			deduction_all rest hilb' (Implies(h, f))

let lemma3 set =
	let concl0 = set2conj set in
	let hilb0 = Hyp(new_number ()) in
	let list = FSet.to_list set in
	let hilb, pterm = lift list hilb0 concl0 in
	let concl = Pr(pterm, concl0) in
	let hilb1, concl1 = deduction_all list hilb concl in
	let concl2 = Implies(concl0, concl) in
	let concl3 = Implies(concl1, concl2) in
	let hilb3 = MP(Pr(PropTaut concl3, concl3), ConstSpec, LP.Axiom(13)) in
	pterm, concl2,
	MP(
		concl1,
		hilb1,
		hilb3
	)

let syllogism concl1 hilb1 concl2 hilb2 =
	match concl1, concl2 with
		Implies(a,b), Implies(b', c) when compare b b' = 0 ->
			let subproof =
				MP(
					concl2,
					hilb2,
					LP.Axiom(1)
				)
			in
			Implies(a, c),
			MP(
				concl1,
				hilb1,
				MP(
					Implies(a,concl2),
					subproof,
					LP.Axiom(2)
				)
			)
	 | _ ->
	 		raise (Invalid_argument "syllogism: unexpected shape of conclusions")

let boxed_only_hyps set =
	FSet.filter (fun f -> match f with Box(Evidence _, _) -> true | _ -> false) set

let rec sum_provisionals = function
	[] -> raise (Invalid_argument "sum_provisionals bug: empty list")
 | [i] -> Provisional i
 | i::tl -> Plus(Provisional i, sum_provisionals tl)

let rec add_lesser_terms concl hilb = function
	[] -> concl, hilb
 | i::tl ->
 		match concl with
			Implies(a, (Pr(t, f) as f1)) ->
		 		let concl1, hilb1 =
					syllogism concl hilb (Implies(f1, Pr(Plus(Provisional i, t), f))) (LP.Axiom(15))
				in
 				add_lesser_terms concl1 hilb1 tl
		 | _ ->
         	raise (Invalid_argument "add_lesser_terms: unexpected shape of term")

let add_families families index concl hilb =
	match concl with
		Implies(a, (Pr(t, f) as f1)) ->
			let family = families.(index) in
			let family' = IntSet.remove family index in
			let fam_list = IntSet.to_list family' in
			let less, greater = List.partition (fun i -> i < index) fam_list in
			let less' = List.rev less in
			let concl1, hilb1 =
				match greater with
					[] -> concl, hilb
				 | _::_ ->
						let greater_term = sum_provisionals greater in
						let t1 = Plus(t, greater_term) in
						let f2 = Pr(t1, f) in
						let concl' = Implies(f1, f2) in
						syllogism concl hilb concl' (LP.Axiom(16))
			in
			add_lesser_terms concl1 hilb1 less'
	 | _ ->
	 		raise (Invalid_argument "add_families: unexpected shape of term")

let rec realize families terms d =
	match d with
		ImplRight(a, b, d0) ->
			let pterm0, concl0, hilb0, hyps0, concls0 = realize families terms d0 in
			(*let hilb1, f1 = hilbert_impl_right hyps concls hyps0 concls0 hilb0 concl0 f01 f02 in
			let hilb2, pterm2 = lift [] hilb1 f1 in*)
			let a = box2pr a in
			let b = box2pr b in
			let hyps = FSet.remove hyps0 a in
			let concls = FSet.add (FSet.remove concls0 b) (Implies(a, b)) in
			let concl = one_implication hyps concls in
			let f1 = Implies(concl0, concl) in
			let hilb2 = ConstSpec in
			let pterm2 = PropTaut f1 in
         App(pterm2, pterm0),
         concl,
         MP(
            Pr(pterm0,concl0),
            hilb0,
            MP(
               Pr(pterm2, f1),
               hilb2,
               LP.Axiom(12)
            )
         ),
			hyps, concls
	 | ImplLeft(a, b, d01, d02) ->
			let pterm01, concl01, hilb01, hyps01, concls01 = realize families terms d01 in
			let pterm02, concl02, hilb02, hyps02, concls02 = realize families terms d02 in
			let a = box2pr a in
			let b = box2pr b in
			let hyps = FSet.add hyps01 (Implies(a,b)) in
			let concls = concls02 in
			(*let hilb1, f1 =
				hilbert_impl_left
					hyps concls
					hyps01 concls01 concl02
					hyps02 concls02 concl02
					hilb01 hilb02
			in
			let hilb2, pterm2 = lift [] hilb1 f1 in*)
			let concl = one_implication hyps concls in
			let f1 = Implies(concl01, Implies(concl02, concl)) in
         let hilb2 = ConstSpec in
         let pterm2 = PropTaut(f1) in
			let subproof =
				MP(
					Pr(pterm01, concl01),
					hilb01,
					MP(
						Pr(pterm2,f1),
						hilb2,
						LP.Axiom(12)
					)
				)
			in
         App(App(pterm2, pterm02), pterm01),
         concl,
			MP(
				Pr(pterm02,concl02),
				hilb02,
				MP(
					Pr(App(pterm2, pterm01), Implies(concl02, f1)),
					subproof,
					LP.Axiom(12)
				)
			),
			hyps, concls
	 | Axiom(f, hyps0, concls0) ->
	 		let f = box2pr f in
			let hyps = FSet.add (box2pr_set hyps0) f in
			let concls = FSet.add (box2pr_set concls0) f in
	 		(*let hilb1, f1 = hilbert_axiom hyps concls f in
			let hilb2, pterm2 = lift [] hilb1 f1 in*)
			let f1 = one_implication hyps concls in
         let hilb2 = ConstSpec in
         let pterm2 = PropTaut(f1) in
			pterm2,
			f1,
			hilb2,
			hyps, concls
	 | FalsumLeft(hyps0, concls0) ->
	 		let hyps = FSet.add (box2pr_set hyps0) Falsum in
			let concls = box2pr_set concls0 in
	 		(*let hilb1, f1 = hilbert_falsum_left hyps concls f in
			let hilb2, pterm2 = lift [] hilb1 f1 in*)
			let f1 = one_implication hyps concls in
         let hilb2 = ConstSpec in
         let pterm2 = PropTaut(f1) in
			pterm2,
			f1,
			hilb2,
			hyps, concls
	 | BoxLeft((Box(Evidence e,f0)) as f, d0) ->
			let pterm0, concl0, hilb0, hyps0, concls0 = realize families terms d0 in
			let f0 = box2pr f0 in
			let f = Pr(Provisional e, f0) in
			let hyps = FSet.remove hyps0 f0 in
			let concls = concls0 in
			(*let hilb1, f1 = hilbert_box_left hyps concls hyps0 hilb0 in
			let hilb2, pterm2 = lift [] hilb1 f1 in*)
			let concl = one_implication hyps concls in
			let f1 = Implies(concl0, concl) in
         let hilb2 = ConstSpec in
         let pterm2 = PropTaut(f1) in
         App(pterm2, pterm0),
         concl,
         MP(
            Pr(pterm0,concl0),
            hilb0,
            MP(
               Pr(pterm2, f1),
               hilb2,
               LP.Axiom(12)
            )
         ),
			hyps, concls
	 | BoxRight((Box(Evidence e,f0)) as f, new_hyps, new_concls, d0) ->
			let pterm0, concl0, hilb0, hyps0, concls0 = realize families terms d0 in
			let f0 = FSet.choose concls0 in
			let new_hyps = box2pr_set new_hyps in
			let new_concls = box2pr_set new_concls in
			let hyps = FSet.union hyps0 new_hyps in
			let s, concl1, hilb1 = lemma3 hyps0 in
			let hilb2 =
				MP(
					Pr(pterm0,concl0),
					hilb0,
					LP.Axiom(12)
				)
			in
			let e_term = App(pterm0, s) in
			let concl2 =
				match concl1 with
					Implies(_, (Pr(s, conj) as a)) ->
						Implies(a, Pr(e_term, f0))
				 | _ ->
				 		raise (Invalid_argument "realize bug: unexpected conclusion of lemma3")
			in
			let concl3, hilb3 = syllogism concl1 hilb1 concl2 hilb2 in
			terms.(e) <- e_term;
			let concl4, hilb4 = add_families families e concl3 hilb3 in
			(*let concl5, hilb5 = hilbert_box_right hyps concls concl4 hilb4 in
			let hilb6, pterm6 = lift [] hilb5 concl5 in*)
			begin match concl4 with
				Implies(a, box_b) ->
					let concls = FSet.add new_concls box_b in
					let concl5 = one_implication hyps concls in
					let concl6 = Implies(concl4, concl5) in
					let pterm6 = PropTaut(concl6) in
					let hilb6 = ConstSpec in
					let hilb7, pterm7 = lift [] (MP(concl4, hilb4, hilb6)) concl5 in
					pterm7, concl5, hilb7, hyps, concls
			 | _ ->
					raise (Invalid_argument "realize bug: unexpected conclusion of add_families")
			end
	 | _ ->
	 		raise (Invalid_argument "realize: a rule for an unsupported connective")
