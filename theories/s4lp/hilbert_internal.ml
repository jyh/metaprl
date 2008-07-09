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

	and agent = Modal of int | Evidence of int

	and formula =
		Falsum
	 |	Atom of symbol
	 | And of formula * formula
	 | Or of formula * formula
	 | Neg of formula
	 | Implies of formula * formula
	 | Box of agent * formula
	 | Pr of proof_term * formula

	type 'formula hilbert =
		Axiom of int
	 | MP of 'formula * 'formula hilbert * 'formula hilbert
	 | Choice of 'formula hilbert * 'formula hilbert
	 | Hyp of int
	 | ConstSpec

   open Lm_printf

   let rec print_formula out = function
      Falsum -> fprintf out "Falsum"
    | Atom s -> fprintf out "Atom %a" output_symbol s
    | And(a,b) -> fprintf out "And(%a, %a)" print_formula a print_formula b
    | Or(a,b) -> fprintf out "Or(%a, %a)" print_formula a print_formula b
    | Neg a -> fprintf out "Neg %a" print_formula a
    | Implies(a,b) -> fprintf out "Implies(%a, %a)" print_formula a print_formula b
    | Box(agent,a) -> fprintf out "Box(%a, %a)" print_agent agent print_formula a
    | Pr(t,a) -> fprintf out "Pr(%a, %a)" print_term t print_formula a

   and print_agent out = function
      Modal i -> fprintf out "Modal %i" i
    | Evidence i -> fprintf out "Evidence %i" i

   and print_term out = function
      Var s -> fprintf out "%a" output_symbol s
    | Const i -> fprintf out "C%i" i
    | App(a,b) -> fprintf out "(%a %a)" print_term a print_term b
    | Plus(a,b) -> fprintf out "(%a+%a)" print_term a print_term b
    | Check(t) -> fprintf out "!%a" print_term t
    | Provisional i -> fprintf out "V%i" i
    | PropTaut a -> fprintf out "PropTaut" (*print_formula a*)

   let rec print_hproof out = function
      Axiom i -> fprintf out "A%i" i
    | MP(f,pf,p) -> fprintf out "MP(%a,%a)" print_hproof pf print_hproof p
    | Choice(p1,p2) -> fprintf out "(%a|%a)" print_hproof p1 print_hproof p2
    | Hyp i -> fprintf out "H%i" i
    | ConstSpec -> fprintf out "CS"
end

exception Not_implemented

open LP

module OrderedFormula =
struct

type t = formula

let fam_cmp f1 f2 =
   match f1, f2 with
      Evidence _, Evidence _ ->
         0 (* why 0, not Pervasives.compare ? 
            * because these are two provisionals for the same formula
            *)
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

module SymbolicSet = functor (O : Lm_set_sig.OrderedType) ->
struct
   include Lm_set.LmMake(O)

   let symbolic_left_sum base op set =
      let first = min_elt set in
      let rest = remove set first in
      fold op (base first) rest

end

module FSet =
struct
   include SymbolicSet(OrderedFormula)

   let print out set =
      iter (fun f -> Lm_printf.fprintf out "%a " print_formula f) set
end

module FMap =
struct

   include Lm_map.LmMakeList(OrderedFormula)

   let remove map k =
      filter map k (function
         h :: t -> t
       | [] ->
            begin
               Lm_printf.printf "FMap.remove: Not found %a" print_formula k;
               raise Not_found
            end
      )

   let print printer out map = 
      iter
         (fun k d ->
            Lm_printf.fprintf out "%a : %a\n" print_formula k printer d
         )
         map
end

module Integer =
struct
   type t = int
   let compare = Pervasives.compare
end

module IntMap = Lm_map.LmMake(Integer)
module IntSet = SymbolicSet(Integer)

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
	 | Choice(d1,d2) ->
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
exception Not_proof of formula hilbert * formula 

let rec lift hyps d f =
	match d, f with
	 | Axiom i, Pr(t,a) ->
	 		if i > 0 && axiom_index f = i then
		 		MP(f,d,Axiom(14)),
				Check(t)
			else
				raise (Not_proof(d, f))
	 | Axiom i, _ -> (* propositional axiom *)
	 		if i > 0 && prop_axiom_index f = i then
				Axiom(i+prop_axiom_count),
				Const(i)
			else
				raise (Not_proof(d,f))
	 | Hyp i, Pr(t,a) when f = List.nth hyps i ->
				MP(f,d,Axiom(14)),
				Check(t)
	 | Hyp i, _ ->
				raise Unliftable
	 | ConstSpec, Pr(PropTaut(f1) as t, f2) when compare f1 f2 = 0 ->
			MP(f,d,Axiom(14)),
			Check(t)
	 | ConstSpec, _ ->
	 		raise (Invalid_argument "lift: PropTaut used to prove a wrong formula")
    | _, Pr(t, a) ->
         let proof0 = Axiom(14) in (* t:a->!t:t:a *)
         MP(f,d,proof0),
         Check(t)
    | Choice(d1,d2), _ ->
         begin try
            lift hyps d1 f
         with Not_proof _ | Unliftable ->
            lift hyps d2 f
         end
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


let rec deduction h hyps d f =
   (*Lm_printf.printf "deduction: h=%a hyps=%a f=%a\n" print_formula h (fun out l -> List.iter (Lm_printf.fprintf out "%a " print_formula) l) hyps print_formula f;*)
   assert (check_proof (h::hyps) d f);
	match d with
		Choice(d1,d2) ->
			begin try
				deduction h hyps d1 f
			with Not_proof _ ->
				deduction h hyps d2 f
			end
	 | Axiom i when i > 0 && axiom_index f = i ->
	 		MP(f,Axiom(i),Axiom(1))
	 | Axiom _ ->
	 		raise (Not_proof(d,f))
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
				raise (Not_proof(d,f))
	 | Hyp i ->
	 		let i' = pred i in
	 		if List.nth hyps i' = f then
		 		MP(f,Hyp(i'),Axiom(1))
			else
				raise (Not_proof(d,f))
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
			 		raise (Not_proof(d,f))

let syllogism a b c proofAB proofBC =
   let ab = Implies(a,b) in
   let bc = Implies(b,c) in
   let ac = Implies(a,c) in
   let bcac = Implies(bc, ac) in
   let syll = Implies(ab, bcac) in
   let proof0 = MP(a, Hyp 0, Hyp 2) in (* a,b->c,a->b >- b *)
   let proof1 = MP(b, proof0, Hyp 1) in (* a,b->c,a->b >- c *)
   let proof2 = deduction a [bc;ab] proof1 c in
   assert(check_proof [bc;ab] proof2 (Implies(a,c)));
   let proof3 = deduction bc [ab] proof2 ac in
   assert(check_proof [ab] proof3 (Implies(bc,ac)));
   let proof4 = deduction ab [] proof3 bcac in
   assert(check_proof [] proof4 syll);
   let proof5 = MP(ab, proofAB, proof4) in (* bcac *)
   let proof6 = MP(bc, proofBC, proof5) in (* ac *)
   assert(check_proof [] proof6 ac);
   proof6

module S4G =
struct
   type fset = FSet.t
   
   type rule_node =
      Axiom of LP.formula
    | AxiomFalsum
    | NegLeft of LP.formula * gentzen
    | ImplLeft of LP.formula * LP.formula * gentzen * gentzen
    | ImplRight of LP.formula * LP.formula * gentzen
    | BoxRight of int * LP.formula * gentzen
    | BoxLeft of LP.formula * gentzen

   and gentzen = rule_node * fset * fset (* rule, hyps, concls *)
end

open S4G

let sequent_formula hyps concls =
   let fh = 
      if FSet.is_empty hyps then
         Neg Falsum
      else
         FSet.symbolic_left_sum (fun x->x) (fun acc e -> And(acc, e)) hyps
   in
   let fc =
      if FSet.is_empty concls then
         Falsum
      else
         FSet.symbolic_left_sum (fun x->x) (fun acc e -> Or(acc, e)) concls
   in
   Implies(fh, fc)

let rec substitute_box_for_provisional i = function
   Implies(a,b) ->
      Implies(
         substitute_box_for_provisional i a,
         substitute_box_for_provisional i b
      )
 | Neg a ->
      substitute_box_for_provisional i a
 | And(a,b) ->
      And(
         substitute_box_for_provisional i a,
         substitute_box_for_provisional i b
      )
 | Or(a,b) ->
      Or(
         substitute_box_for_provisional i a,
         substitute_box_for_provisional i b
      )
 | Falsum -> Falsum
 | Atom _ as a -> a
 | Box(Modal 0, a) -> Pr(Provisional i, a)
 | Box(m, a) ->
      Box(
         m,
         substitute_box_for_provisional i a
      )
 | Pr(t, a) ->
      Pr(
         t,
         substitute_box_for_provisional i a
      )

type family = Essential of IntSet.t | NonEssential of int

let merge_families f1 f2 =
   match f1, f2 with
      Essential s1, Essential s2 ->
         Essential(IntSet.union s1 s2)
    | Essential s, NonEssential _ -> f1
    | NonEssential _, Essential s -> f2
    | NonEssential i1, NonEssential i2 -> NonEssential(min i1 i2)

let rec assign_fresh counter = function
   Implies(a,b) ->
      let counter0, a' = assign_fresh counter a in
      let counter1, b' =  assign_fresh counter0 b in
      counter1, Implies(a', b')
 | Neg a ->
      let counter', a' = assign_fresh counter a in
      counter', Neg a'
 | And(a,b) ->
      let counter0, a' = assign_fresh counter a in
      let counter1, b' = assign_fresh counter0 b in
      counter1, And(a', b')
 | Or(a,b) ->
      let counter0, a' = assign_fresh counter a in
      let counter1, b' = assign_fresh counter0 b in
      counter1, Or(a', b')
 | Falsum -> counter, Falsum
 | Atom _ as a -> counter, a
 | Box(Modal 0, a) ->
      let counter', a' = assign_fresh counter a in
      succ counter', Pr(Provisional counter', a')
 | Box(m, a) ->
      let counter', a' = assign_fresh counter a in
      counter', Box(m, a')
 | Pr(t, a) ->
      let counter', a' = assign_fresh counter a in
      counter', Pr(t, a')

let assign_fresh_multiple map counter set =
   FSet.fold 
      (fun (map, counter, set) a ->
         let counter', a' = assign_fresh counter a in
         FMap.add map a a',
         counter',
         FSet.add set a'
      )
      (map, counter, FSet.empty)
      set

let rec merge_pair acc f1 f2 =
match f1, f2 with
   Falsum, Falsum -> acc
 | Atom _, Atom _ -> acc
 | And(a0,b0), And(a1,b1) ->
      let acc' = merge_pair acc a0 a1 in
      merge_pair acc' b0 b1
 | Or(a0,b0), Or(a1,b1) ->
      let acc' = merge_pair acc a0 a1 in
      merge_pair acc' b0 b1
 | Neg a0, Neg a1 ->
      merge_pair acc a0 a1
 | Implies(a0,b0), Implies(a1,b1) ->
      let acc' = merge_pair acc a0 a1 in
      merge_pair acc' b0 b1
 | Pr(Provisional i0, a0), Pr(Provisional i1, a1) ->
      let fam0 =
         try IntMap.find acc i0
         with Not_found ->
            NonEssential i0
      in
      let fam1 =
         try IntMap.find acc i1
         with Not_found ->
            NonEssential i1
      in
      let fam = merge_families fam0 fam1 in
      let acc0 = IntMap.remove acc i0 in
      let acc1 = IntMap.remove acc0 i1 in
      let acc2 = IntMap.add_list acc1 [(i0,fam);(i1,fam)] in
      merge_pair acc2 a0 a1
 | Box(_,a0), Box(_,a1) ->
      merge_pair acc a0 a1
 | Pr(_,a0), Pr(_,a1) ->
      merge_pair acc a0 a1
 | _, _ ->
      raise (Invalid_argument "merge_pair: non-matching formulas")

let merge_formula map0 map1 acc f =
   merge_pair acc (FMap.find map0 f) (FMap.find map1 f)

let merge start_set map0 map1 families0 families1 =
   let families = IntMap.union (fun k l r -> merge_families l r) families0 families1 in
   FSet.fold (merge_formula map0 map1) families start_set

(*
 * assign recursively goes over a Gentzen style S4 proof and assigns
 * unique indices to each fresh instance of box0 (agent0's box).
 * It does so in such a way that the same formula instance
 * above and below a rule (line) get the same indices in its boxes
 * Since a rule might have two branches and indices in them
 * might clash, a mapping 'families' is maintained to map
 * each index to the complete list of indices from its family
 * for the formula below such rule one of the indices is chosen.
 * Another problem is that when 'assign' converts a subderivation,
 * its bottom sequent has many formulas converted and not identical
 * to the originals but the sequent below the current rules
 * has only original formulas. They have to be related somehow.
 * One option would be to consider hyps and conclusions not
 * as multisets but as lists/arrays and refer toformulas by
 * their positions but this approach will render certain operation
 * less efficient.
 * So, I've chosen a different approach - the first element of
 * the 'assign's result tuple is a map from original formulas
 * to their new forms 
 * (not global but limited to just processed sequent)
 *)
let rec assign families counter deriv =
let result = match deriv with
   AxiomFalsum, hyps, concls ->
      let map0, counter0, hyps' = assign_fresh_multiple FMap.empty counter hyps in
      let map1, counter1, concls' = assign_fresh_multiple map0 counter0 concls in
      families, map1, counter1, (AxiomFalsum, hyps', concls')
 | Axiom(a), hyps, concls ->
      let map0, counter0, hyps' = assign_fresh_multiple FMap.empty counter (FSet.remove hyps a) in
      let map1, counter1, concls' = assign_fresh_multiple map0 counter0 (FSet.remove concls a) in
      let counter2, a' = assign_fresh counter1 a in
      families, FMap.add (FMap.add map1 a a') a a', counter2, (Axiom a', FSet.add hyps' a', FSet.add concls' a')
 | NegLeft(a, subder), hyps, concls ->
      let families0, map0, counter0, subder0 = assign families counter subder in
      let _, hyps0, concls0 = subder0 in
      let a' = FMap.find map0 a in
      let nega' = Neg a' in
      families0,
      FMap.add (FMap.remove map0 a) (Neg a) nega',
      counter0,
      (
         NegLeft(a', subder0),
         FSet.add hyps0 nega',
         FSet.remove concls0 a'
      )
 | ImplLeft(a,b,left,right), hyps, concls ->
      let families0, map0, counter0, left' = assign families counter left in
      let families1, map1, counter1, right' = assign families counter0 right in
      let _, hyps0, concls0 = left' in
      let a' = FMap.find map0 a in
      let b' = FMap.find map1 b in
      let ab' = Implies(a', b') in
      let start_set = FSet.union hyps concls in
      merge start_set map0 map1 families0 families1,
      FMap.add (FMap.remove map0 a) (Implies(a, b)) ab',
      counter1,
      (
         ImplLeft(a', b', left', right'),
         FSet.add hyps0 ab',
         FSet.remove concls0 a'
      )      
 | ImplRight(a,b,subder), hyps, concls ->
      let families0, map0, counter0, subder0 = assign families counter subder in
      let _, hyps0, concls0 = subder0 in
      let a' = FMap.find map0 a in
      let b' = FMap.find map0 b in
      let ab' = Implies(a', b') in
      families0,
      FMap.add (FMap.remove (FMap.remove map0 a) b) (Implies(a, b)) ab',
      counter0,
      (
         ImplRight(a', b', subder0),
         FSet.remove hyps0 a',
         FSet.add (FSet.remove concls0 b') ab'
      )
 | BoxRight(agent,b,subder), hyps, concls ->
      let families0, map0, counter0, subder0 = assign families counter subder in
      let _, hyps0, concls0 = subder0 in
      let b' = FMap.find map0 b in
      let map0' = FMap.remove map0 b in
      let _, assum_h, _ = subder in
      let gamma = FSet.subtract_list hyps (FSet.to_list assum_h) in
      let boxb = Box(Modal agent, b) in
      let delta = FSet.remove concls boxb in 
      let map1, counter1, gamma' = assign_fresh_multiple map0' counter0 gamma in
      let map2, counter2, delta' = assign_fresh_multiple map1 counter1 delta in
      let boxb' = Pr(Provisional counter2, b') in 
      IntMap.add families0 counter2 (Essential(IntSet.singleton counter2)),
      FMap.add map2 boxb boxb',
      succ counter2,
      (
         BoxRight(agent, b', subder0),
         FSet.union hyps0 gamma',
         FSet.add delta' boxb'
      )
 | BoxLeft(a,subder), hyps, concls ->
      let families0, map0, counter0, subder0 = assign families counter subder in
      let _, hyps0, concls0 = subder0 in
      let a' = FMap.find map0 a in
      families0,
      FMap.remove map0 a,
      counter0,
      (
         BoxLeft(a', subder0), 
         FSet.remove hyps0 a',
         concls0
      )
in
   let families', map', counter', deriv' = result in
   let _, hyps', concls' = deriv' in
   Lm_printf.printf "\nmap:\n%a" (FMap.print print_formula) map';
   Lm_printf.printf "\n%a\n>-\n%a\n" FSet.print hyps' FSet.print concls';
   result

(*
 * c - propositional translation of the assuption sequent of the rule
 * tC - a proof term for it
 * proofTC - the proof of tC:c
 * hyps, concls - hyps and conclusion formulae of the conclusion sequent
 *)
let realize_chain_rule tC c proofTC hyps concls =
   let c' = sequent_formula hyps concls in
   let tR = PropTaut(Implies(c, c')) in
   let tail2 = ConstSpec in (* a proof of Pr(tR, c -> c') *)
   let tail3 = LP.Axiom(12) in (* a proof of tR:(c->c')->(tC:c->tR*tC:c') *)
   let tail4 = MP(Pr(tR, Implies(c, c')), tail2, tail3) in (* a proof of tC:c->tR*tC:c' *)
   let tail5 = MP(Pr(tC,c), proofTC, tail4) in (* a proof of tR*tC:c' *)
   App(tR,tC), c', tail5

let realize_branch_rule tC1 c1 proofTC1 tC2 c2 proofTC2 hyps concls =
   let c' = sequent_formula hyps concls in
   let d = Implies(c2, c') in
   let taut = Implies(c1, d) in
   let tR = PropTaut(taut) in
   let proof1 = ConstSpec in (*for tR:taut *)
   let proof2 = LP.Axiom(12) in (*for tR:taut->(tC1:c1->tR*tC1:d *)
   let proof3 = MP(Pr(tR, taut), proof1, proof2) in (*for tC1:c1->tR*tC1:d *)
   let proof4 = MP(Pr(tC1,c1), proofTC1, proof3) in (*for tR*tC1:d *)
   let proof5 = LP.Axiom(12) in (*for tR*tC1:d->(tC2:c2->tR*tC1*tC2:c') *)
   let proof6 = MP(Pr(App(tR, tC1), d), proof4, proof5) in (*for tC2:c2->tR*tC1*tC2:c' *)
   let proof7 = MP(Pr(tC2, c2), proofTC2, proof6) in (*for tR*tC1*tC2:c' *)
   App(App(tR, tC1), tC2), c', proof7

let realize_axiom hyps concls =
   let f' = sequent_formula hyps concls in
   PropTaut f', f', ConstSpec

let weaker_or_equal a b =
   match a with
      Box(Modal af, _) ->
         begin match b with
            Box(Modal bf, _) ->
               (af = bf) || (bf = 0)
          | Pr(_, _) ->
               true
          | _ ->
               false
         end
    | Pr(_, _) ->
         begin match b with
            Box(Modal bf, _) ->
               (bf = 0)
          | Pr(_, _) ->
               true
          | _ ->
               false
         end
    | _ ->
         false

let add_family families fam t f =
   let family_set =
      match IntMap.find families fam with
         Essential s -> s
       | NonEssential i -> raise (Invalid_argument "BoxRight rule associated with a non-essential family")
   in
   let family_term =
      IntSet.symbolic_left_sum
         (fun e -> Provisional e)
         (fun acc e -> LP.Plus(acc,Provisional e))
         family_set
   in
   let taut = Implies(Pr(t,f), Pr(family_term,f)) in
   let taut' = Pr(PropTaut(taut), taut) in
   let proof0 = ConstSpec in (* taut' *)
   assert(check_proof [] proof0 taut');
   let proof1 = LP.Axiom(13) in (* taut'->taut *)
   let proof2 = MP(taut', proof0, proof1) in
   let prF = Pr(family_term, f) in
   Lm_printf.printf "add_family: %a\n" print_formula prF;
   assert(check_proof [] proof2 taut);
   proof2, prF

exception Found of int

(* Gentzen to Hilbert transformation (phase 3) *)
let rec g2h families = function
      Axiom(f), hyps, concls ->
         assert (FSet.mem hyps f);
         assert (FSet.mem concls f);
         realize_axiom hyps concls
    | AxiomFalsum, hyps, concls ->
         assert (FSet.mem hyps Falsum);
         realize_axiom hyps concls
    | NegLeft(f, subderivation), hyps, concls ->
         assert (FSet.mem hyps (Neg f));
         let tC, c, proofTC = g2h families subderivation in
         realize_chain_rule tC c proofTC hyps concls
    | ImplLeft(a, b, left, right), hyps, concls ->
         assert (FSet.mem hyps (Implies(a, b)));
         let tC1, c1, proofTC1 = g2h families left in
         let tC2, c2, proofTC2 = g2h families right in
         realize_branch_rule tC1 c1 proofTC1 tC2 c2 proofTC2 hyps concls
    | ImplRight(a, b, subderivation), hyps, concls ->
         assert (FSet.mem concls (Implies(a, b)));
         let tC, c, proofTC = g2h families subderivation in
         realize_chain_rule tC c proofTC hyps concls
    | BoxLeft(f, subderivation), hyps, concls ->
         assert (if FSet.mem hyps f then false else true);
         let tC, c, proofTC = g2h families subderivation in
         realize_chain_rule tC c proofTC hyps concls
    | BoxRight(agent, f, subderivation), hyps, concls ->
         let _, assum_hyps, assum_concls = subderivation in
         assert (FSet.cardinal assum_concls = 1);
         let boxf = Box(Modal agent, f) in
         assert (FSet.choose assum_concls = f);
         let test = weaker_or_equal boxf in
         assert (FSet.for_all test assum_hyps);
         let tC, c, proofTC = g2h families subderivation in
         let fam =
            try
               begin
                  FSet.fold (fun _ e ->
                     match e with
                        Pr(Provisional i, f') when compare f f' = 0 ->
                           raise (Found i)
                      | _ -> ()
                  ) () concls;
                  Lm_printf.printf "g2h.BoxRight: box(%a) not found in the conclusion" print_formula f;
                  raise Not_found
               end
            with Found i -> i
         in
         begin match c with
            Implies(ais, b) ->
               let proof0, s = lift [ais] (Hyp 0) ais in (* ais >- s:ais *)
               assert (check_proof [ais] proof0 (Pr(s,ais)));
               let proof1 = deduction ais [] proof0 (Pr(s,ais)) in (* ais->s:ais *)
               let proof2 = LP.Axiom(12) in (* tC:c->(s:ais->tC*s:b) *)
               let proof3 = MP(Pr(tC, c), proofTC, proof2) in (* s:ais->tC*s:b) *)
               let prB = Pr(App(tC, s), b) in
               assert (check_proof [] proof1 (Implies(ais, Pr(s,ais))));
               assert (check_proof [] proof3 (Implies(Pr(s,ais), prB)));
               let proof4 = syllogism ais (Pr(s, ais)) prB proof1 proof3 in (* ais->tC*s:b *)
               assert(check_proof [] proof4 (Implies(ais, prB)));
               let proof5, prB' = add_family families fam (App(tC, s)) b in (* tC*s:b->fam:b *)
               assert(check_proof [] proof5 (Implies(prB, prB')));
               let proof6 = syllogism ais prB prB' proof4 proof5 in (* ais->prB' *)
               assert(check_proof [] proof6 (Implies(ais,prB')));
               let c' = sequent_formula hyps concls in
               let taut = Implies(Implies(ais, prB'), c') in
               let taut' = Pr(PropTaut(taut), taut) in
               let proof7 = ConstSpec in (* taut' *)
               assert(check_proof [] proof7 taut');
               let proof8 = LP.Axiom 13 in (* taut'->taut *)
               assert(check_proof [] proof8 (Implies(taut', taut)));
               let proof9 = MP(taut', proof7, proof8) in (* taut *)
               assert(check_proof [] proof9 taut);
               let proof10 = MP(Implies(ais, prB'), proof6, proof9) in
               assert (check_proof [] proof10 c');
               let proof11, tC' = lift [] proof10 c' in
               tC', c', proof11
          | _ ->
               raise Not_implemented
         end

let realize derivation =
   let families, map, counter, derivation' = assign IntMap.empty 0 derivation in
   g2h families derivation'

let s = Atom(add "s")
let s_concl = FSet.singleton s
let hyps0 = FSet.singleton (Box(Modal 0, Neg(Implies(s, Box(Modal 0, s)))))

let _ =
   let b = Implies(s, s) in
   let m = FMap.add FMap.empty s s in
   let m' = FMap.add m s b in
   assert (FMap.find m' s = b);
   let m'' = FMap.remove m' s in
   assert (FMap.mem m'' s);
   assert (FMap.find m'' s = s)

let proof1 =
   BoxLeft(
      Neg(Implies(s, Box(Modal 0, s))),
      (
         NegLeft(
            Implies(s, Box(Modal 0, s)),
            (
               ImplRight(
                  s,
                  Box(Modal 0, s),
                  (
                     BoxRight(
                        0,
                        s,
                        (
                           BoxLeft(
                              Neg(Implies(s, Box(Modal 0, s))),
                              (
                                 NegLeft(
                                    Implies(s, Box(Modal 0, s)),
                                    (
                                       ImplRight(
                                          s,
                                          Box(Modal 0, s),
                                          (
                                             Axiom(s),
                                             FSet.add hyps0 s,
                                             FSet.add s_concl (Box(Modal 0, s))
                                          )
                                       ),
                                       hyps0,
                                       FSet.add s_concl (Implies(s, Box(Modal 0, s)))
                                    )
                                 ),
                                 FSet.add hyps0 (Neg(Implies(s, Box(Modal 0, s)))),
                                 s_concl
                              )
                           ),
                           hyps0,
                           s_concl
                        )
                     ),
                     FSet.add hyps0 s,
                     FSet.singleton (Box(Modal 0, s))
                  )
               ),
               hyps0,
               FSet.singleton (Implies(s, Box(Modal 0, s)))
            )
         ),
         FSet.add hyps0 (Neg(Implies(s, Box(Modal 0, s)))),
         FSet.empty
      )
   ),
   hyps0,
   FSet.empty

let tC, c, proof = realize proof1 in
   Lm_printf.printf "result: %a\nproof: %a" print_formula (Pr(tC, c)) print_hproof proof;
   assert(check_proof [] proof (Pr(tC, c)))
(*
Pr((PropTaut (PropTaut (PropTaut ((C13 !PropTaut) ((((C2 ((C2 (C1 C2)) ((C2 ((C2 (C1 C2)) ((C2 (C1 C1)) (C1 C2)))) ((C2 ((C2 (C1 C2)) ((C2 (C1 C1)) (C1 C1)))) ((C2 ((C2 (C1 C2)) (C1 C1))) (C1 C1)))))) ((C2 ((C2 (C1 C2)) ((C2 ((C2 (C1 C2)) ((C2 (C1 C1)) (C1 C2)))) ((C2 ((C2 (C1 C2)) ((C2 (C1 C1)) (C1 C1)))) ((C2 (C1 C1)) ((C2 C1) C1)))))) ((C2 ((C2 (C1 C2)) ((C2 ((C2 (C1 C2)) ((C2 (C1 C1)) (C1 C2)))) ((C2 (C1 C1)) (C1 C1))))) ((C2 (C1 C1)) (C1 C1))))) ((((C2 ((C2 (C1 C2)) ((C2 ((C2 (C1 C2)) ((C2 (C1 C1)) (C1 C2)))) ((C2 ((C2 (C1 C2)) ((C2 (C1 C1)) (C1 C1)))) ((C2 ((C2 (C1 C2)) (C1 C1))) (C1 C1)))))) ((C2 ((C2 (C1 C2)) ((C2 ((C2 (C1 C2)) ((C2 (C1 C1)) (C1 C2)))) ((C2 ((C2 (C1 C2)) ((C2 (C1 C1)) (C1 C1)))) ((C2 (C1 C1)) ((C2 C1) C1)))))) ((C2 ((C2 (C1 C2)) ((C2 ((C2 (C1 C2)) ((C2 (C1 C1)) (C1 C2)))) ((C2 (C1 C1)) (C1 C1))))) ((C2 (C1 C1)) (C1 C1))))) ((C2 (C1 C14)) ((C2 C1) C1))) (C12 !(PropTaut (PropTaut (PropTaut PropTaut)))))) (C13 !PropTaut)))))), Implies(Pr(V1, Neg Implies(Atom s, Pr(V0, Atom s))), Falsum))

MP(MP(MP(MP(MP(MP(MP(CS,A14),MP(A29,A12)),MP(MP(MP(MP(MP(MP(MP(MP(CS,MP(CS,A12)),MP(CS,A12)),MP(CS,A12)),A14),MP(A28,A12)),MP(MP(MP(MP(A17,MP(MP(A17,MP(A18,A12)),A12)),MP(MP(MP(A30,MP(A17,A12)),MP(A18,A12)),A12)),MP(MP(MP(MP(MP(MP(A17,MP(A17,A12)),MP(MP(MP(A17,MP(A17,A12)),MP(A18,A12)),A12)),MP(MP(MP(MP(MP(MP(A17,MP(A17,A12)),MP(MP(MP(A17,MP(A17,A12)),MP(A18,A12)),A12)),MP(MP(MP(MP(MP(A18,MP(A17,A12)),MP(MP(MP(A17,MP(A17,A12)),MP(A18,A12)),A12)),MP(MP(MP(A18,MP(A17,A12)),MP(A18,A12)),A12)),MP(A18,A12)),A12)),MP(MP(MP(A18,MP(A17,A12)),MP(A18,A12)),A12)),MP(A18,A12)),A12)),MP(MP(MP(MP(MP(MP(MP(A17,MP(MP(A17,MP(A18,A12)),A12)),MP(MP(MP(A17,MP(A17,A12)),MP(A18,A12)),A12)),MP(MP(MP(MP(MP(A17,MP(A17,A12)),MP(MP(MP(A17,MP(A17,A12)),MP(A18,A12)),A12)),MP(MP(MP(A18,MP(A17,A12)),MP(A18,A12)),A12)),MP(A18,A12)),A12)),MP(MP(MP(MP(MP(A18,MP(A17,A12)),MP(MP(MP(A17,MP(A17,A12)),MP(A18,A12)),A12)),MP(MP(MP(A18,MP(A17,A12)),MP(A18,A12)),A12)),MP(A18,A12)),A12)),MP(MP(MP(A18,MP(A17,A12)),MP(A18,A12)),A12)),MP(A18,A12)),A12)),MP(MP(MP(MP(MP(MP(MP(A17,MP(A17,A12)),MP(MP(MP(MP(A17,MP(A17,A12)),MP(MP(MP(A18,MP(A17,A12)),MP(A18,A12)),A12)),MP(A18,A12)),A12)),MP(MP(MP(MP(MP(A17,MP(A17,A12)),MP(MP(MP(A17,MP(A17,A12)),MP(A18,A12)),A12)),MP(MP(MP(A18,MP(A17,A12)),MP(A18,A12)),A12)),MP(A18,A12)),A12)),MP(MP(MP(MP(MP(A18,MP(A17,A12)),MP(MP(MP(A17,MP(A17,A12)),MP(A18,A12)),A12)),MP(MP(MP(A18,MP(A17,A12)),MP(A18,A12)),A12)),MP(A18,A12)),A12)),MP(MP(MP(A18,MP(A17,A12)),MP(A18,A12)),A12)),MP(A18,A12)),A12)),A12)),A12)),MP(MP(MP(MP(MP(MP(A17,MP(A17,A12)),MP(MP(MP(A17,MP(A17,A12)),MP(A18,A12)),A12)),MP(MP(MP(MP(MP(MP(A17,MP(A17,A12)),MP(MP(MP(A17,MP(A17,A12)),MP(A18,A12)),A12)),MP(MP(MP(MP(MP(A18,MP(A17,A12)),MP(MP(MP(A17,MP(A17,A12)),MP(A18,A12)),A12)),MP(MP(MP(A18,MP(A17,A12)),MP(A18,A12)),A12)),MP(A18,A12)),A12)),MP(MP(MP(A18,MP(A17,A12)),MP(A18,A12)),A12)),MP(A18,A12)),A12)),MP(MP(MP(MP(MP(MP(MP(A17,MP(MP(A17,MP(A18,A12)),A12)),MP(MP(MP(A17,MP(A17,A12)),MP(A18,A12)),A12)),MP(MP(MP(MP(MP(A17,MP(A17,A12)),MP(MP(MP(A17,MP(A17,A12)),MP(A18,A12)),A12)),MP(MP(MP(A18,MP(A17,A12)),MP(A18,A12)),A12)),MP(A18,A12)),A12)),MP(MP(MP(MP(MP(A18,MP(A17,A12)),MP(MP(MP(A17,MP(A17,A12)),MP(A18,A12)),A12)),MP(MP(MP(A18,MP(A17,A12)),MP(A18,A12)),A12)),MP(A18,A12)),A12)),MP(MP(MP(A18,MP(A17,A12)),MP(A18,A12)),A12)),MP(A18,A12)),A12)),MP(MP(MP(MP(MP(MP(MP(A17,MP(A17,A12)),MP(MP(MP(MP(A17,MP(A17,A12)),MP(MP(MP(A18,MP(A17,A12)),MP(A18,A12)),A12)),MP(A18,A12)),A12)),MP(MP(MP(MP(MP(A17,MP(A17,A12)),MP(MP(MP(A17,MP(A17,A12)),MP(A18,A12)),A12)),MP(MP(MP(A18,MP(A17,A12)),MP(A18,A12)),A12)),MP(A18,A12)),A12)),MP(MP(MP(MP(MP(A18,MP(A17,A12)),MP(MP(MP(A17,MP(A17,A12)),MP(A18,A12)),A12)),MP(MP(MP(A18,MP(A17,A12)),MP(A18,A12)),A12)),MP(A18,A12)),A12)),MP(MP(MP(A18,MP(A17,A12)),MP(A18,A12)),A12)),MP(A18,A12)),A12)),A12)),A12)),MP(MP(MP(CS,A14),MP(A29,A12)),A12)),MP(CS,A12)),MP(CS,A12)),MP(CS,A12))
*)
