open Lm_symbol

module Derivation =
struct
	type proof_term =
		Var of symbol
	 | Const of int
	 | App of proof_term * proof_term
	 | Plus of proof_term * proof_term
	 | Check of proof_term

	type formula =
		Atom of symbol
	 | And of formula * formula
	 | Or of formula * formula
	 | Neg of formula
	 | Implies of formula * formula
	 | Pr of proof_term * formula

	type derivation =
		Axiom of formula * int
	 | MP of formula * formula * derivation * derivation
	 | Concat of derivation * derivation
	 | Hyp of int
end

open Derivation

(*
let rec pt2term = function
	Var s -> mk_var_term s
 | Const i -> mk_const_term i
 | App(s,t) -> mk_app_term (pt2term s) (pt2term t)
 | Plus(s,t) -> mk_union_term (pt2term s) (pt2term t)
 | Check t -> mk_check_term (pt2term t)

let rec fml2term = function
	Atom s -> mk_var_term s
 | And(s,t) -> mk_and_term(fml2term s) (fml2term t)
 | Or(s,t) -> mk_or_term(fml2term s) (fml2term t)
 | Implies(s,t) -> mk_implies_term(fml2term s) (fml2term t)
 | Neg t -> mk_neg_term t
 | Pr(s,t) -> mk_pr_term (pr2term s) (fml2term t)
*)

exception Not_axiom

let prop_axiom_index = function
	Implies(a1,Implies(b,a2)) when a1=a2 -> 1
 | Implies(Implies(a1,Implies(b1,c1)),Implies(Implies(a2,b2),Implies(a3,c2)))
 	when a1=a2 & a1=a3 & b1=b2 & c1=c2 -> 2
 | Implies(And(a1,b),a2) when a1=a2 -> 3
 | Implies(And(a,b1),b2) when b1=b2 -> 4
 | Implies(a1,Implies(b1,And(a2,b2))) when a1=a2 & b1=b2 -> 5
 | Implies(a1,Or(a2,b)) when a1=a2 -> 6
 | Implies(b1,Or(a,b2)) when b1=b2 -> 7
 | Implies(Implies(a1,c1),Implies(Implies(b1,c2),Implies(Or(a2,b2),c3)))
 	when a1=a2 & b1=b2 & c1=c2 & c1=c3 -> 8
 | Implies(Implies(a1,b1),Implies(Implies(a2,Neg(b2)),Neg(a3)))
 	when a1=a2 & a1=a3 & b1=b2 -> 9
 | Implies(a1,Implies(Neg(a2),b)) when a1=a2 -> 10
 | Or(a1,Neg(a2)) when a1=a2 -> 11
 | Implies(Pr(s1,Implies(a1,b1)),Implies(Pr(t1,a2),Pr(App(s2,t2),b2)))
 	when a1=a2 & b1=b2 & s1=s2 & t1=t2 -> 12
 | Implies(Pr(t,a1),a2) when a1=a2 -> 13
 | Implies(Pr(t1,a1),Pr(Check(t2),Pr(t3,a2))) when a1=a2 & t1=t2 & t1=t3 -> 14
 | Implies(Pr(t1,a1),Pr(Plus(s,t2),a2)) when t1=t2 & a1=a2 -> 15
 | Implies(Pr(s1,a1),Pr(Plus(s2,t),a2)) when s2=s2 & a1=a2 -> 16
 | _ -> 0

let prop_axiom_count = 16

let axiom_index = function
 | Pr(Const(i),a) ->
 		if i > 0 then
	 		let ai = prop_axiom_index a in
			if i = ai then
				prop_axiom_count + i
			else
				0
		else
			0
 | f -> prop_axiom_index f

let rec check_proof hyps d f =
	match d with
		Axiom(a,i) ->
			(a = f) && (i > 0) && (axiom_index f = i)
	 | MP(a,b,d1,d2) ->
	 		(f = b) && (check_proof hyps d1 a) && (check_proof hyps d2 (Implies(a,f)))
	 | Concat(d1,d2) ->
	 		(check_proof hyps d1 f) || (check_proof hyps d2 f)
	 | Hyp i ->
	 		List.nth hyps i = f

exception Unliftable
exception Not_proof

let rec lift hyps d f =
	match d with
		Concat(d1,d2) ->
			begin try
				lift hyps d1 f
			with Not_proof | Unliftable ->
				lift hyps d2 f
			end
	 | Axiom((Pr(t,a) as f1),i) when f1=f ->
	 		if i > 0 && axiom_index f = i then
		 		MP(f,Pr(Check(t),f),d,Axiom(Implies(f,Pr(Check(t),f)),14)),
				Check(t)
			else
				raise Not_proof
	 | Axiom(f1,i) when f1=f -> (* propositional axiom *)
	 		if i > 0 && prop_axiom_index f = i then
				Axiom(Pr(Const(i), f), i+prop_axiom_count),
				Const(i)
			else
				raise Not_proof
	 | Axiom _ ->
	 		raise Not_proof
	 | Hyp i ->
			if f = List.nth hyps i then
				match f with
					Pr(t,a) ->
						MP(f,Pr(Check(t),f),d,Axiom(Implies(f,Pr(Check(t),f)),14)),
						Check(t)
				 | _ ->
				 		raise Unliftable
			else
				raise Not_proof
	 | MP(a,b,d1,d2) ->
	 		if b=f then
		 		let ld1, a_pt = lift hyps d1 a in
				let ld2, ab_pt = lift hyps d2 (Implies(a,b)) in
				MP(
					Pr(a_pt,a),
					Pr(App(ab_pt,a_pt),b),
					ld1,
					MP(
						Pr(ab_pt,Implies(a,b)),
						Implies(Pr(a_pt,a),Pr(App(ab_pt,a_pt),b)),
						ld2,
						Axiom(
							Implies(
								Pr(ab_pt,Implies(a,b)),
								Implies(Pr(a_pt,a),Pr(App(ab_pt,a_pt),b))),
							12
						)
					)
				),
				App(ab_pt,a_pt)
			else
				raise Not_proof

let rec deduction_theorem h hyps d f =
	match d with
		Concat(d1,d2) ->
			begin try
				deduction_theorem h hyps d1 f
			with Not_proof ->
				deduction_theorem h hyps d2 f
			end
	 | Axiom(a,i) when f=a ->
	 		if i > 0 && axiom_index f = i then
		 		MP(a,Implies(h,a),Axiom(a,i),Axiom(Implies(a,Implies(h,a)),1))
			else
				raise Not_proof
	 | Axiom _ ->
	 		raise Not_proof
	 | Hyp 0 ->
	 		if h=f then
		 		MP(
					Implies(f,Implies(f,f)),
					Implies(f,f),
					Axiom(Implies(f,Implies(f,f)),1),
					MP(
						Implies(f,Implies(Implies(f,f),f)),
						Implies(Implies(f,Implies(f,f)),Implies(f,f)),
						Axiom(Implies(f,Implies(Implies(f,f),f)),1),
						Axiom(
							Implies(
								Implies(f,Implies(Implies(f,f),f)),
								Implies(Implies(f,Implies(f,f)),Implies(f,f))
							),
							2
						)
					)
				)
			else
				raise Not_proof
	 | Hyp i ->
	 		let i' = pred i in
	 		if List.nth hyps i' = f then
		 		MP(f,Implies(h,f),Hyp(i'),Axiom(Implies(f,Implies(h,f)),1))
			else
				raise Not_proof
	 | MP(a,b,d1,d2) ->
	 		if b=f then
				let dd1 = deduction_theorem h hyps d1 a in
				let dd2 = deduction_theorem h hyps d2 (Implies(a,b)) in
				MP(
					Implies(h,a),
					Implies(h,b),
					dd1,
					MP(
						Implies(h,Implies(a,b)),
						Implies(Implies(h,a),Implies(h,b)),
						dd2,
						Axiom(Implies(Implies(h,Implies(a,b)),Implies(Implies(h,a),Implies(h,b))),2)
					)
				)
			else
				raise Not_proof
