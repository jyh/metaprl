open Lm_symbol

module LP =
struct
	type proof_term =
		Var of symbol
	 | Const of int
	 | App of proof_term * proof_term
	 | Plus of proof_term * proof_term
	 | Check of proof_term
	 | Provisional of int
	 | PropTaut of formula

	and family = Modal of int | Evidence of int

	and formula =
		Falsum
	 |	Atom of symbol
	 | And of formula * formula
	 | Or of formula * formula
	 | Neg of formula
	 | Implies of formula * formula
	 | Box of family * formula
	 | Pr of proof_term * formula

	type derivation =
		Axiom of int
	 | MP of formula * derivation * derivation
	 | Concat of derivation * derivation
	 | Hyp of int
	 | ConstSpec

end

open LP

module OrderedFormula =
struct

type t = formula

let fam_cmp f1 f2 =
   match f1, f2 with
      Evidence _, Evidence _ ->
         0
    | Evidence _, Modal _ ->
         -1
    | Modal _, Evidence _ ->
         1
    | Modal i1, Modal i2 ->
         Pervasives.compare i1 i2

let rec compare_pterm t1 t2 =
   match t1, t2 with
      Var v1, Var v2 -> Lm_symbol.compare v1 v2
    | Var _, (Const _ | App _ | Plus _ | Check _ | Provisional _ | PropTaut _) -> -1
    | Const _, Var _ -> 1
    | Const c1, Const c2 -> Pervasives.compare c1 c2
    | Const _, (App _ | Plus _ | Check _ | Provisional _ | PropTaut _) -> -1
    | App _, (Var _ | Const _) -> 1
    | App(t11, t12), App(t21, t22) ->
         let c = compare_pterm t11 t21 in
         if c = 0 then
            compare_pterm t12 t22
         else
            c
    | App _, (Plus _ | Check _ | Provisional _ | PropTaut _) -> -1
    | Plus _, (Var _ | Const _ | App _) -> 1
    | Plus(t11, t12), Plus(t21, t22) ->
         let c = compare_pterm t11 t21 in
         if c = 0 then
            compare_pterm t12 t22
         else
            c
    | Plus _, (Check _ | Provisional _ | PropTaut _) -> -1
    | Check _, (Var _ | Const _ | App _ | Plus _) -> 1
    | Check t1, Check t2 -> compare_pterm t1 t2
	 | Check _, (Provisional _ | PropTaut _) -> -1
	 | Provisional _, (Var _ | Const _ | App _ | Plus _ | Check _) ->
	 		raise (Invalid_argument
			"Equal formulas were prefixed with provisional term and something else")
	 | Provisional i, Provisional j ->
	 		let c = Pervasives.compare i j in
			if c = 0 then
				0
			else
		 		raise (Invalid_argument
				"compare_pterm: Equal formulas were prefixed with different provisional terms")
	 | Provisional _, PropTaut _ ->
         raise (Invalid_argument
         "Equal formulas were prefixed with provisional term and something else")
	 | PropTaut _, (Var _ | Const _ | App _ | Plus _ | Check _ | Provisional _) -> 1
	 | PropTaut _, PropTaut _ -> 0

let rec compare f1 f2 =
   match f1, f2 with
    | Falsum, Falsum -> 0
    | Falsum, (Atom _| And _ | Or _ | Neg _ | Implies _ | Box _ | Pr _) -> -1
    | Atom _, Falsum -> 1
    | Atom s1, Atom s2 -> Lm_symbol.compare s1 s2
    | Atom _, (And _ | Or _ | Neg _ | Implies _ | Box _ | Pr _) -> -1
    | And(f11,f12), (Falsum | Atom _) -> 1
    | And(p11,p12), And(p21,p22) -> compare_pairs (p11,p12) (p21,p22)
    | And _, (Or _ | Neg _ | Implies _ | Box _ | Pr _) -> -1
    | Or _, (Falsum | Atom _ | And _) -> 1
    | Or(p11,p12), Or(p21,p22) -> compare_pairs (p11,p12) (p21,p22)
    | Or _, (Neg _ | Implies _ | Box _ | Pr _) -> -1
    | Neg _, (Falsum | Atom _ | And _ | Or _) -> 1
    | Neg f1, Neg f2 -> compare f1 f2
    | Neg _, (Implies _ | Box _ | Pr _) -> -1
    | Implies _, (Falsum | Atom _ | And _ | Or _ | Neg _) -> 1
    | Implies(p11,p12), Implies(p21,p22) -> compare_pairs (p11,p12) (p21,p22)
    | Implies _, (Box _ | Pr _) -> -1
    | Box _, (Falsum | Atom _ | And _ | Or _ | Neg _ | Implies _) -> 1
    | Box(fam1,fml1), Box(fam2,fml2) ->
         let c = fam_cmp fam1 fam2 in
         if c = 0 then
            compare fml1 fml2
         else
            c
    | Box _, Pr _ -> -1
    | Pr _, (Falsum | Atom _ | And _ | Or _ | Neg _ | Implies _ | Box _) -> 1
    | Pr(t1, f1), Pr(t2, f2) ->
         let c = compare f1 f2 in
         if c = 0 then
            compare_pterm t1 t2
         else
            c

and compare_pairs (f11,f12) (f21,f22) =
   let c = compare f11 f21 in
   if c = 0 then
      compare f12 f22
   else
      c

end

open OrderedFormula
module FSet = Lm_set.LmMake(OrderedFormula)

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
		Axiom(i) ->
			(i > 0) && (axiom_index f = i)
	 | MP(a,d1,d2) ->
	 		(check_proof hyps d1 a) && (check_proof hyps d2 (Implies(a,f)))
	 | Concat(d1,d2) ->
	 		(check_proof hyps d1 f) || (check_proof hyps d2 f)
	 | Hyp i ->
	 		List.nth hyps i = f
	 | ConstSpec ->
	 		match f with
				Pr(PropTaut(f1), f2) ->
			 		compare f1 f2 = 0
			 | _ ->
			 		false

exception Unliftable
exception Not_proof

let rec lift hyps d f =
	match d, f with
		Concat(d1,d2), _ ->
			begin try
				lift hyps d1 f
			with Not_proof | Unliftable ->
				lift hyps d2 f
			end
	 | Axiom i, Pr(t,a) ->
	 		if i > 0 && axiom_index f = i then
		 		MP(f,d,Axiom(14)),
				Check(t)
			else
				raise Not_proof
	 | Axiom i, _ -> (* propositional axiom *)
	 		if i > 0 && prop_axiom_index f = i then
				Axiom(i+prop_axiom_count),
				Const(i)
			else
				raise Not_proof
	 | Hyp i, Pr(t,a) when f = List.nth hyps i ->
				MP(f,d,Axiom(14)),
				Check(t)
	 | Hyp i, _ ->
				raise Unliftable
	 | MP(a,d1,d2), _ ->
	 		let ld1, a_pt = lift hyps d1 a in
			let ld2, af_pt = lift hyps d2 (Implies(a,f)) in
			MP(
				Pr(a_pt,a),
				ld1,
				MP(
					Pr(af_pt,Implies(a,f)),
					ld2,
					Axiom(12)
				)
			),
			App(af_pt,a_pt)
	 | ConstSpec, Pr(PropTaut(f1) as t, f2) when compare f1 f2 = 0 ->
			MP(f,d,Axiom(14)),
			Check(t)
	 | ConstSpec, _ ->
	 		raise (Invalid_argument "lift: PropTaut used to prove a wrong formula")

let rec deduction h hyps d f =
	match d with
		Concat(d1,d2) ->
			begin try
				deduction h hyps d1 f
			with Not_proof ->
				deduction h hyps d2 f
			end
	 | Axiom i when i > 0 && axiom_index f = i ->
	 		MP(f,Axiom(i),Axiom(1))
	 | Axiom _ ->
	 		raise Not_proof
	 | Hyp 0 when compare h f = 0 ->
	 		MP(
				Implies(f,Implies(f,f)),
				Axiom(1),
				MP(
					Implies(f,Implies(Implies(f,f),f)),
					Axiom(1),
					Axiom(2)
				)
			)
	 | Hyp 0 ->
				raise Not_proof
	 | Hyp i ->
	 		let i' = pred i in
	 		if List.nth hyps i' = f then
		 		MP(f,Hyp(i'),Axiom(1))
			else
				raise Not_proof
	 | MP(a,d1,d2) ->
			let dd1 = deduction h hyps d1 a in
			let dd2 = deduction h hyps d2 (Implies(a,f)) in
			MP(
				Implies(h,a),
				dd1,
				MP(
					Implies(h,Implies(a,f)),
					dd2,
					Axiom(2)
				)
			)
	 | ConstSpec ->
	 		match f with
				Pr(PropTaut(f1), f2) when compare f1 f2 = 0 ->
					MP(f,ConstSpec,Axiom(1))
			 | _ ->
			 		raise Not_proof
