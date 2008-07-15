open Lm_symbol
open Lm_printf

open Term_sig
open Refiner.Refiner
open Term
open RefineError

module SymbolicSet = functor (O : Lm_set_sig.OrderedTypeDebug) ->
struct
   include Lm_set.LmMake(O)

   let map f s = fold (fun acc i -> add acc (f i)) empty s

   let symbolic_left_sum base op set =
      let first = min_elt set in
      let rest = remove set first in
      fold op (base first) rest

   let print out set =
      Lm_printf.fprintf out "{";
      iter (fun i -> Lm_printf.fprintf out "%a " O.print i) set;
      Lm_printf.fprintf out "}"

	exception Found of O.t

	let find set i =
		try 
			iter
				(fun i0 -> if O.compare i i0 = 0 then raise (Found i0))
				set;
			raise Not_found
		with Found i1 -> i1

	exception Success

	let query f set =
		let result = ref None in
      try
         iter
            (fun i -> 
					match f i with
						Some x ->
							result := Some x;
							raise Success
					 | None ->
					 		()
				)
            set;
         raise Not_found
      with Success ->
			match !result with
				Some r -> r
			 | None -> raise Not_found

end

module Integer =
struct
   type t = int

   let compare (i : int) (j : int) =
      if i < j then
         -1
      else if i > j then
         1
      else
         0

   let print out i = Lm_printf.fprintf out "%i" i
end

module IntMap =
struct
   include Lm_map.LmMake(Integer)

   let print printer out map =
      iter
         (fun k d ->
            Lm_printf.fprintf out "%i : %a\n" k printer d
         )
         map

end

module IntSet = SymbolicSet(Integer)

module Partitioning = functor (O : Lm_set_sig.OrderedTypeDebug) ->
struct

   type elt = O.t
   module Set = SymbolicSet(O)
   type part = Set.t

   let empty = []

   let rec mem s i =
   match s with
      [] -> false
    | h::t ->
         if Set.mem h i then
            true
         else
            mem t i

   let rec find s i =
   match s with
      [] -> raise Not_found
    | h::t ->
         if Set.mem h i then
            h
         else
            find t i

   let merge s i1 i2 =
      let rec phase2 i1part = function
         [] -> raise Not_found
       | h::t ->
            if Set.mem h i2 then
               let new_part = Set.union i1part h in
               new_part::t
            else
               h::(phase2 i1part t)
      in
      let rec phase1 = function
         [] -> raise Not_found
       | h::t ->
            if Set.mem h i1 then
               phase2 h t
            else
               h::(phase1 t)
      in
      phase1 s

   let add_new s i = (Set.singleton i)::s

   let rec add s i =
   match s with
      [] -> [Set.singleton i]
    | h::t ->
         if Set.mem h i then
            s
         else
            h::(add t i)

   let join p1 p2 =
      let rec join_aux acc s =
         match acc with
            [] -> [s]
          | h::t ->
               if Set.is_empty (Set.inter h s) then
                  h::(join_aux t s)
               else
                  join_aux t (Set.union h s)
      in
      List.fold_left join_aux p1 p2

   let fold = List.fold_left

   let print out p =
      List.iter (fun s ->
         Lm_printf.fprintf out " {";
         Set.iter (fun i -> Lm_printf.fprintf out "%a " O.print i) s;
         Lm_printf.fprintf out "}"
      ) p

end

module Provisional =
struct
   type t = Principal of int | NonPrincipal of int

   exception Collision of int

   let exact_compare p1 p2 =
      match p1, p2 with
         Principal i1, Principal i2 -> Pervasives.compare i1 i2
       | NonPrincipal i1, NonPrincipal i2 -> Pervasives.compare i1 i2
       | Principal i1, NonPrincipal i2 when i1 = i2 -> raise (Collision i1)
       | NonPrincipal i1, Principal i2 when i1 = i2 -> raise (Collision i1)
       | Principal i1, NonPrincipal i2 -> 1
       | NonPrincipal i1, Principal i2 -> -1

   let compare p1 p2 =
      try exact_compare p1 p2
      with Collision _ -> 0

   let print out = function
      Principal i -> Lm_printf.fprintf out "+%i" i
    | NonPrincipal i -> Lm_printf.fprintf out "-%i" i

end

module FamilyPart =
struct
   include Partitioning(Provisional)
   open Provisional

   type family = Essential of IntSet.t | NonEssential of int

   let print_family out = function
      Essential s -> Lm_printf.fprintf out "Ess%a" IntSet.print s
    | NonEssential i -> Lm_printf.fprintf out "NonEss%i" i

   let strip_principality family =
      Set.fold
         (fun acc rep ->
            match rep with
               Principal i -> IntSet.add acc i
             | NonPrincipal i -> IntSet.add acc i
         )
         IntSet.empty
         family

   let essential family =
      let s = Set.range_fold
         (fun p -> match p with Principal _ -> 0 | NonPrincipal _ -> 1)
         (fun acc -> function
            Principal i -> IntSet.add acc i
          | NonPrincipal _ -> raise (Invalid_argument "Only Principal provisionals were expected")
         )
         IntSet.empty
         family
      in
      if IntSet.is_empty s then
         match Set.min_elt family with
            NonPrincipal i -> NonEssential i
          | Principal _ -> raise (Invalid_argument "Found Principal but there were none just an instant ago")
      else
         Essential s

end

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
	 | Nec of int * 'formula hilbert

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

   open Lm_printf

   let rec subst_provisionals subst t =
      match t with
         Var _ | Const _ -> t
       | App(t1,t2) ->
            App(
               subst_provisionals subst t1,
               subst_provisionals subst t2
            )
       | Plus(t1,t2) ->
            Plus(
               subst_provisionals subst t1,
               subst_provisionals subst t2
            )
       | Check(t1) -> Check(subst_provisionals subst t1)
       | PropTaut(f) -> PropTaut(subst_provisionals_in_formula subst f)
       | Provisional i ->
            try
               IntMap.find subst i
            with
               Not_found -> t

   and subst_provisionals_in_formula subst (f: formula) =
      match f with
         Falsum | Atom _ -> f
       | And(a,b) -> 
            And(
               subst_provisionals_in_formula subst a,
               subst_provisionals_in_formula subst b
            )
       | Or(a,b) ->
            Or(
               subst_provisionals_in_formula subst a,
               subst_provisionals_in_formula subst b
            )
       | Neg a ->
            Neg (subst_provisionals_in_formula subst a)
       | Implies(a,b) ->
            Implies(
               subst_provisionals_in_formula subst a,
               subst_provisionals_in_formula subst b
            )
       | Box(a,b) ->
            Box(a, subst_provisionals_in_formula subst b)
       | Pr(t,a) ->
            Pr(
               subst_provisionals subst t,
               subst_provisionals_in_formula subst a
            )

   let rec subst_provisionals_in_hilbert subst pr =
   match pr with
      Axiom _ -> pr
    | MP(f,pr1,pr2) ->
         MP(
            subst_provisionals_in_formula subst f,
            subst_provisionals_in_hilbert subst pr1,
            subst_provisionals_in_hilbert subst pr2
         )
    | Choice(pr1,pr2) ->
         Choice(
            subst_provisionals_in_hilbert subst pr1,
            subst_provisionals_in_hilbert subst pr2
         )
    | Hyp _ | ConstSpec -> pr
	 | Nec(i,pr) ->
	 		Nec(i, subst_provisionals_in_hilbert subst pr)

   let rec print_formula out = function
      Falsum -> fprintf out "Falsum"
    | Atom s -> fprintf out "%a" output_symbol s
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
	 | Nec(i,p) -> fprintf out "Nec(%i,%a)" i print_hproof p
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

let print = print_formula

end

open OrderedFormula

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
 | Implies(Box(Modal i1, Implies(a1,b1)),Implies(Box(Modal i2,a2),Box(Modal i3,b2))) when i1=i2 & i1=i3 & a1=a2 & b1=b2 -> 17
 | Implies(Box(Modal i, a1),a2) when a1=a2 -> 18
 | Implies(Box(Modal i1, a1),Box(Modal i2,Box(Modal i3,a2))) when i1=i2 & i1=i3 & a1=a2 -> 19
 | Implies(Pr(t,a1),Box(Modal i,a2)) when a1=a2 -> 20
 | _ -> 0

let prop_axiom_count = 20

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

let axiom f = Axiom(axiom_index f)

let rec check_proof_hidden hyps d f hidden =
	match d with
	 | Axiom(i) ->
			(i > 0) && (axiom_index f = i), hidden
	 | MP(a,d1,d2) ->
	 		let check1, hidden1 = check_proof_hidden hyps d1 a hidden in
         if check1 then
            check_proof_hidden hyps d2 (Implies(a,f)) hidden1
         else
            false, FSet.empty
	 | Choice(d1,d2) ->
	 		let check1, hidden1 = check_proof_hidden hyps d1 f hidden in
         if check1 then
            true, hidden1
         else check_proof_hidden hyps d2 f hidden
	 | Hyp i ->
	 		List.nth hyps i = f, hidden
	 | ConstSpec ->
	 		begin match f with
				Pr(PropTaut(f1), f2) when compare f1 f2 = 0 ->
               true, FSet.add hidden f2
			 | _ ->
			 		false, FSet.empty
			end
	 | Nec(i,d1) ->
	 		begin match f with
				Box(Modal i1, f1) when i=i1 & (hyps=[] || prop_axiom_index f1 > 0) ->
					check_proof_hidden hyps d1 f1 hidden
			 | _ ->
			 		false, FSet.empty
			end

let check_proof hyps d f =
   let check, _ = check_proof_hidden hyps d f FSet.empty in
   check

exception Unliftable
exception Not_proof of formula hilbert * formula 

let pt t = Var(add t)
let pT = pt "t"
let pS = pt "s"
let atom s = Atom(add s)
let atomS = atom "s"
let atomA = atom "a"
let atomB = atom "b"
let atomC = atom "c"

(* from proofs of s:a->b and t:a build a proof of s*t:b *)
let appProof s b s_ab_proof t a t_a_proof =
	let pr_s_ab = Pr(s,Implies(a,b)) in
	let st = App(s,t) in
	MP(
		Pr(t,a),
		t_a_proof,
		MP(
			pr_s_ab,
			s_ab_proof,
			axiom (Implies(Pr(pS,Implies(atomA,atomB)),Implies(Pr(pT,atomA),Pr(App(pS,pT),atomB))))
		)
	),
	st

let rec lift hyps d f =
	let checkAxiom = axiom (Implies(Pr(pT,atomS),Pr(Check(pT),Pr(pT,atomS)))) in
	match d, f with
	 | Axiom i, Pr(t,a) ->
	 		if i > 0 && axiom_index f = i then
		 		MP(f,d,checkAxiom),
				Check(t)
			else
				raise (Not_proof(d, f))
	 | Axiom i, _ -> (* propositional axiom *)
	 		if i > 0 && prop_axiom_index f = i then
				axiom (Pr(Const(i),f)),
				Const(i)
			else
				raise (Not_proof(d,f))
	 | Hyp i, Pr(t,a) when f = List.nth hyps i ->
				MP(f,d,checkAxiom),
				Check(t)
	 | Hyp i, _ ->
				raise Unliftable
	 | ConstSpec, Pr(PropTaut(f1) as t, f2) when compare f1 f2 = 0 ->
			MP(f,d,checkAxiom),
			Check(t)
	 | ConstSpec, _ ->
	 		raise (Invalid_argument "lift: PropTaut used to prove a wrong formula")
    | _, Pr(t, a) ->
         let proof0 = checkAxiom in (* t:a->!t:t:a *)
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
			appProof af_pt f ld2 a_pt a ld1
	 | Nec(i,d1), Box(Modal i1, f1) when i=i1 ->
	 		let ld1, f1_pt = lift hyps d1 f1 in
			let pr_f1 = Pr(f1_pt, f1) in
			let lld1, check_f1_pt = lift hyps ld1 pr_f1 in
			let connection = Implies(Pr(f1_pt,f1),Box(Modal i, f1)) in
			let ai = axiom_index connection in
			appProof (Const ai) connection (Axiom ai) check_f1_pt pr_f1 lld1
	 | Nec(_,_), _ ->
	 		raise (Invalid_argument "lift: Nec used to prove a wrong formula")


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
	 		MP(f,Axiom(i),axiom (Implies(atomA,Implies(atomB,atomA))))
	 | Axiom _ ->
	 		raise (Not_proof(d,f))
	 | Hyp 0 when compare h f = 0 ->
	 		MP(
				Implies(f,Implies(f,f)),
				axiom (Implies(atomA,Implies(atomB,atomA))),
				MP(
					Implies(f,Implies(Implies(f,f),f)),
					axiom (Implies(atomA,Implies(atomB,atomA))),
					axiom (Implies(Implies(atomA,Implies(atomB,atomC)),Implies(Implies(atomA,atomB),Implies(atomA,atomC))))
				)
			)
	 | Hyp 0 ->
				raise (Not_proof(d,f))
	 | Hyp i ->
	 		let i' = pred i in
	 		if List.nth hyps i' = f then
		 		MP(f,Hyp(i'),axiom (Implies(atomA,Implies(atomB,atomA))))
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
					axiom (Implies(Implies(atomA,Implies(atomB,atomC)),Implies(Implies(atomA,atomB),Implies(atomA,atomC))))
				)
			)
	 | ConstSpec ->
	 		begin match f with
				Pr(PropTaut(f1), f2) when compare f1 f2 = 0 ->
					MP(f,ConstSpec,axiom (Implies(atomA,Implies(atomB,atomA))))
			 | _ ->
			 		raise (Not_proof(d,f))
			end
	 | Nec(i,d1) ->
	 		begin match f with
				Box(Modal i, f1) when prop_axiom_index f1 > 0 ->
					MP(
						f,
						axiom f,
						axiom (Implies(f,Implies(h,f)))
					)
			 | _ ->
			 		raise (Not_proof(d,f))
			end

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

   let rec subst_provisionals_in_gentzen subst (r, hyps, concls) =
      let hyps' = FSet.map (subst_provisionals_in_formula subst) hyps in
      let concls' = FSet.map (subst_provisionals_in_formula subst) concls in
      let r' = match r with
         Axiom f -> Axiom (subst_provisionals_in_formula subst f)
       | AxiomFalsum -> r
       | NegLeft(a,subderivation) ->
            NegLeft(
               subst_provisionals_in_formula subst a,
               subst_provisionals_in_gentzen subst subderivation
            )
       | ImplLeft(a,b,left,right) ->
            ImplLeft(
               subst_provisionals_in_formula subst a,
               subst_provisionals_in_formula subst b,
               subst_provisionals_in_gentzen subst left,
               subst_provisionals_in_gentzen subst right
            )
       | ImplRight(a,b,subderivation) ->
            ImplRight(
               subst_provisionals_in_formula subst a,
               subst_provisionals_in_formula subst b,
               subst_provisionals_in_gentzen subst subderivation
            )
       | BoxRight(agent,a,subderivation) ->
            BoxRight(
               agent,
               subst_provisionals_in_formula subst a,
               subst_provisionals_in_gentzen subst subderivation
            )
       | BoxLeft(a,subderivation) ->
            BoxLeft(
               subst_provisionals_in_formula subst a,
               subst_provisionals_in_gentzen subst subderivation
            )
      in
      r', hyps', concls'
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

let rec merge_pair families f1 f2 =
match f1, f2 with
   Falsum, Falsum -> families
 | Atom _, Atom _ -> families
 | And(a0,b0), And(a1,b1) ->
      let acc' = merge_pair families a0 a1 in
      merge_pair acc' b0 b1
 | Or(a0,b0), Or(a1,b1) ->
      let acc' = merge_pair families a0 a1 in
      merge_pair acc' b0 b1
 | Neg a0, Neg a1 ->
      merge_pair families a0 a1
 | Implies(a0,b0), Implies(a1,b1) ->
      let families' = merge_pair families a0 a1 in
      merge_pair families' b0 b1
 | Pr(Provisional i0, a0), Pr(Provisional i1, a1) ->
      let fam0 = Provisional.NonPrincipal i0 in
      let fam1 = Provisional.NonPrincipal i1 in
      let families0 = FamilyPart.add families fam0 in
      let families1 = FamilyPart.add families0 fam1 in
      let families2 = FamilyPart.merge families1 fam0 fam1 in
      merge_pair families2 a0 a1
 | Box(_,a0), Box(_,a1) ->
      merge_pair families a0 a1
 | Pr(_,a0), Pr(_,a1) ->
      merge_pair families a0 a1
 | _, _ ->
      raise (Invalid_argument "merge_pair: non-matching formulas")

let merge_formula map0 map1 acc f =
   merge_pair acc (FMap.find map0 f) (FMap.find map1 f)

let merge start_set map0 map1 families0 families1 =
   let families = FamilyPart.join families0 families1 in
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
		let boxb', families1, counter3 =
			if agent = 0 then
	      	Pr(Provisional counter2, b'),
   	   	FamilyPart.add_new families0 (Provisional.Principal counter2),
	      	succ counter2
			else
				Box(Modal agent, b'),
				families0,
         	counter2
		in
			families1,
			FMap.add map2 boxb boxb',
			counter3,
         (
            BoxRight(agent, b', subder0),
            FSet.union hyps0 gamma',
            FSet.add delta' boxb'
         )
 | BoxLeft(a,subder), hyps, concls ->
      let families0, map0, counter0, subder0 = assign families counter subder in
      let _, hyps0, concls0 = subder0 in
      let a' = FMap.find map0 a in
      let _, assum_hyps, _ = subder in
		let fm =
			FSet.query
				(function Box(Modal _, a1) as f when compare a a1 = 0 -> Some f | _ -> None)
				assum_hyps
		in
      let a'from_box =
        	match fm, FMap.find map0 fm with
   	      Box(Modal 0, _), Pr(_, fm') -> fm'
      	 | Box(Modal 0, _), _ -> raise (Invalid_argument "A Pr-formula expected")
			 | _, Box(Modal _, fm') -> fm'
			 | _, _ -> raise (Invalid_argument "A Box-formula expected")
      in
      let families1 = merge_pair families0 a' a'from_box in
      families1,
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

let make_provisionals_sum set =
   IntSet.symbolic_left_sum
      (fun e -> Provisional e)
      (fun acc e -> LP.Plus(acc,Provisional e))
      set

let rec make_provisionals_subst families =
   FamilyPart.fold 
      (fun subst set ->
         let family_set = FamilyPart.strip_principality set in
         let essential =
            match FamilyPart.essential set with
               FamilyPart.Essential s -> s
             | FamilyPart.NonEssential i -> IntSet.singleton i
         in
         let sum = make_provisionals_sum essential in
         IntSet.fold (fun acc i -> IntMap.add acc i sum) subst family_set
      )
      IntMap.empty
      families

(*
 * c - propositional translation of the assuption sequent of the rule
 * tC - a proof term for it
 * proofTC - the proof of tC:c
 * hyps, concls - hyps and conclusion formulae of the conclusion sequent
 *)
let realize_chain_rule subst tC c proofTC hyps concls =
   let c' = sequent_formula hyps concls in
   let cc' = Implies(c, c') in
   let tR = PropTaut(cc') in
   let tail2 = ConstSpec in (* a proof of Pr(tR, c -> c') *)
   let tail3 = axiom (Implies(Pr(pS,Implies(atomA,atomB)),Implies(Pr(pT,atomA),Pr(App(pS,pT),atomB)))) in (* a proof of tR:(c->c')->(tC:c->tR*tC:c') *)
   let tail4 = MP(Pr(tR, cc'), tail2, tail3) in (* a proof of tC:c->tR*tC:c' *)
   let tail5 = MP(Pr(tC,c), proofTC, tail4) in (* a proof of tR*tC:c' *)
   subst, App(tR,tC), c', tail5

let realize_branch_rule subst tC1 c1 proofTC1 tC2 c2 proofTC2 hyps concls =
   let c' = sequent_formula hyps concls in
   let d = Implies(c2, c') in
   let taut = Implies(c1, d) in
   let tR = PropTaut(taut) in
	let appAxiom = axiom (Implies(Pr(pS,Implies(atomA,atomB)),Implies(Pr(pT,atomA),Pr(App(pS,pT),atomB)))) in
   let proof1 = ConstSpec in (*for tR:taut *)
   let proof2 =  appAxiom in (*for tR:taut->(tC1:c1->tR*tC1:d *)
   let proof3 = MP(Pr(tR, taut), proof1, proof2) in (*for tC1:c1->tR*tC1:d *)
   let proof4 = MP(Pr(tC1,c1), proofTC1, proof3) in (*for tR*tC1:d *)
   let proof5 = appAxiom in (*for tR*tC1:d->(tC2:c2->tR*tC1*tC2:c') *)
   let proof6 = MP(Pr(App(tR, tC1), d), proof4, proof5) in (*for tC2:c2->tR*tC1*tC2:c' *)
   let proof7 = MP(Pr(tC2, c2), proofTC2, proof6) in (*for tR*tC1*tC2:c' *)
   subst, App(App(tR, tC1), tC2), c', proof7

let realize_axiom subst hyps concls =
   let f' = sequent_formula hyps concls in
   subst, PropTaut f', f', ConstSpec

let add_family families fam t f =
   Lm_printf.printf "family: %i\n" fam;
   Lm_printf.printf "fm: %a\n" print_formula (Pr(t,f));
   let family_set =
      match FamilyPart.essential (FamilyPart.find families (Provisional.Principal fam)) with
         FamilyPart.Essential s -> s
       | FamilyPart.NonEssential i -> raise (Invalid_argument "BoxRight rule associated with a non-essential family")
   in
   let family_term = make_provisionals_sum family_set in
   let taut = Implies(Pr(t,f), Pr(family_term,f)) in
   let taut' = Pr(PropTaut(taut), taut) in
   let proof0 = ConstSpec in (* taut' *)
   assert(check_proof [] proof0 taut');
   let proof1 = axiom (Implies(Pr(pT,atomA),atomA)) in (* taut'->taut *)
   let proof2 = MP(taut', proof0, proof1) in
   let prF = Pr(family_term, f) in
   Lm_printf.printf "add_family: %a\n" print_formula prF;
   assert(check_proof [] proof2 taut);
   proof2, prF

exception Found of int

(* Gentzen to Hilbert transformation (phase 3) *)
let rec g2h families subst = function
      Axiom(f), hyps, concls ->
         assert (FSet.mem hyps f);
         assert (FSet.mem concls f);
         realize_axiom subst hyps concls
    | AxiomFalsum, hyps, concls ->
         assert (FSet.mem hyps Falsum);
         realize_axiom subst hyps concls
    | NegLeft(f, subderivation), hyps, concls ->
         assert (FSet.mem hyps (Neg f));
         let subst', tC, c, proofTC = g2h families subst subderivation in
         realize_chain_rule subst' tC c proofTC hyps concls
    | ImplLeft(a, b, left, right), hyps, concls ->
         assert (FSet.mem hyps (Implies(a, b)));
         let subst1, tC1, c1, proofTC1 = g2h families subst left in
         let subst2, tC2, c2, proofTC2 = g2h families subst1 right in
         realize_branch_rule subst2 tC1 c1 proofTC1 tC2 c2 proofTC2 hyps concls
    | ImplRight(a, b, subderivation), hyps, concls ->
         assert (FSet.mem concls (Implies(a, b)));
         let subst', tC, c, proofTC = g2h families subst subderivation in
         realize_chain_rule subst' tC c proofTC hyps concls
    | BoxLeft(f, subderivation), hyps, concls ->
         assert (if FSet.mem hyps f then false else true);
         let subst', tC, c, proofTC = g2h families subst subderivation in
         realize_chain_rule subst' tC c proofTC hyps concls
    | BoxRight(0, f, subderivation), hyps, concls ->
         let _, assum_hyps, assum_concls = subderivation in
         assert (FSet.cardinal assum_concls = 1);
         let boxf = Box(Modal 0, f) in
         assert (FSet.choose assum_concls = f);
         let test = weaker_or_equal boxf in
         assert (FSet.for_all test assum_hyps);
         let subst1, tC, c, proofTC = g2h families subst subderivation in
         let fam = FSet.query
				(function
					Pr(Provisional i, f') when compare f f' = 0 -> Some i
				 | _ -> None
				)
				concls
			in
         begin match c with
            Implies(ais, b) ->
               let proof0, s = lift [ais] (Hyp 0) ais in (* ais >- s:ais *)
               assert (check_proof [ais] proof0 (Pr(s,ais)));
               Lm_printf.printf "s:ais %a\n" print_formula (Pr(s,ais));
               let proof1 = deduction ais [] proof0 (Pr(s,ais)) in (* ais->s:ais *)
               let proof2 = axiom (Implies(Pr(pS,Implies(atomA,atomB)),Implies(Pr(pT,atomA),Pr(App(pS,pT),atomB)))) in (* tC:c->(s:ais->tC*s:b) *)
               let proof3 = MP(Pr(tC, c), proofTC, proof2) in (* s:ais->tC*s:b) *)
               let tCs = App(tC, s) in
               let prB = Pr(tCs, b) in
               assert (check_proof [] proof1 (Implies(ais, Pr(s,ais))));
               assert (check_proof [] proof3 (Implies(Pr(s,ais), prB)));
               let proof4 = syllogism ais (Pr(s, ais)) prB proof1 proof3 in (* ais->tC*s:b *)
               assert(check_proof [] proof4 (Implies(ais, prB)));
               let subst2 = IntMap.add subst1 fam tCs in
               let proof5, prB' = add_family families fam tCs b in (* tC*s:b->fam:b *)
               assert(check_proof [] proof5 (Implies(prB, prB')));
               Lm_printf.printf "prB': %a\n" print_formula prB';
               let proof6 = syllogism ais prB prB' proof4 proof5 in (* ais->prB' *)
               assert(check_proof [] proof6 (Implies(ais,prB')));
               let c' = sequent_formula hyps concls in
               let taut = Implies(Implies(ais, prB'), c') in
               let taut' = Pr(PropTaut(taut), taut) in
               let proof7 = ConstSpec in (* taut' *)
               assert(check_proof [] proof7 taut');
               let proof8 = axiom (Implies(Pr(pT,atomA),atomA)) in (* taut'->taut *)
               assert(check_proof [] proof8 (Implies(taut', taut)));
               let proof9 = MP(taut', proof7, proof8) in (* taut *)
               assert(check_proof [] proof9 taut);
               let proof10 = MP(Implies(ais, prB'), proof6, proof9) in
               assert (check_proof [] proof10 c');
               let proof11, tC' = lift [] proof10 c' in
               subst2, tC', c', proof11
          | _ ->
               raise Not_implemented
         end
    | BoxRight(agent, f, subderivation), hyps, concls ->
	 		raise Not_implemented

let realize derivation =
   let families, map, counter, derivation1 = assign FamilyPart.empty 0 derivation in
   Lm_printf.printf "families:\n%a\n" FamilyPart.print families;
   let provisional_subst = make_provisionals_subst families in
   Lm_printf.printf "provisional subst: %a\n" (IntMap.print print_term) provisional_subst;
   let derivation2 = subst_provisionals_in_gentzen provisional_subst derivation1 in
   let subst,tC,c,proof = g2h families IntMap.empty derivation2 in
   Lm_printf.printf "subst: %a\n" (IntMap.print print_term) subst;
   subst_provisionals subst tC,
   subst_provisionals_in_formula subst c,
   subst_provisionals_in_hilbert subst proof

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

let rec lp_free subst f =
   match f with
    | Falsum | Atom _ -> subst, f
    | And(a,b) ->
         let subst1, a' = lp_free subst a in
         let subst2, b' = lp_free subst1 b in
         subst2, And(a',b')
    | Or(a,b) ->
         let subst1, a' = lp_free subst a in
         let subst2, b' = lp_free subst1 b in
         subst2, Or(a',b')
    | Neg a ->
         let subst1, a' = lp_free subst a in
         subst1, Neg(a')
    | Implies(a,b) ->
         let subst1, a' = lp_free subst a in
         let subst2, b' = lp_free subst1 b in
         subst2, Implies(a',b')
    | Box(agent, a) ->
         let subst1, a' = lp_free subst a in
         subst1, Box(agent, a')
    | Pr(Plus(_,_),_) ->
         subst, f
    | Pr(_,_) ->
         try 
            let v = FMap.find subst f in
            subst, Atom v
         with Not_found ->
            let v = new_symbol_string "Pr" in
            let subst' = FMap.add subst f v in
            subst', Atom v

let tC, c, proof = realize proof1 in
   Lm_printf.printf "result: %a\nproof: %a\n" print_formula (Pr(tC, c)) print_hproof proof;
   let check, hidden = check_proof_hidden [] proof (Pr(tC, c)) FSet.empty in
   assert check;
   Lm_printf.printf "hidden assumptions:\n";
   let hidden' = FSet.map (fun f -> snd (lp_free FMap.empty f)) hidden in
   FSet.iter (Lm_printf.printf "%a\n" print_formula) hidden'
(*
Pr((PropTaut (PropTaut (PropTaut ((C13 !PropTaut) ((((C2 ((C2 (C1 C2)) ((C2 ((C2 (C1 C2)) ((C2 (C1 C1)) (C1 C2)))) ((C2 ((C2 (C1 C2)) ((C2 (C1 C1)) (C1 C1)))) ((C2 ((C2 (C1 C2)) (C1 C1))) (C1 C1)))))) ((C2 ((C2 (C1 C2)) ((C2 ((C2 (C1 C2)) ((C2 (C1 C1)) (C1 C2)))) ((C2 ((C2 (C1 C2)) ((C2 (C1 C1)) (C1 C1)))) ((C2 (C1 C1)) ((C2 C1) C1)))))) ((C2 ((C2 (C1 C2)) ((C2 ((C2 (C1 C2)) ((C2 (C1 C1)) (C1 C2)))) ((C2 (C1 C1)) (C1 C1))))) ((C2 (C1 C1)) (C1 C1))))) ((((C2 ((C2 (C1 C2)) ((C2 ((C2 (C1 C2)) ((C2 (C1 C1)) (C1 C2)))) ((C2 ((C2 (C1 C2)) ((C2 (C1 C1)) (C1 C1)))) ((C2 ((C2 (C1 C2)) (C1 C1))) (C1 C1)))))) ((C2 ((C2 (C1 C2)) ((C2 ((C2 (C1 C2)) ((C2 (C1 C1)) (C1 C2)))) ((C2 ((C2 (C1 C2)) ((C2 (C1 C1)) (C1 C1)))) ((C2 (C1 C1)) ((C2 C1) C1)))))) ((C2 ((C2 (C1 C2)) ((C2 ((C2 (C1 C2)) ((C2 (C1 C1)) (C1 C2)))) ((C2 (C1 C1)) (C1 C1))))) ((C2 (C1 C1)) (C1 C1))))) ((C2 (C1 C14)) ((C2 C1) C1))) (C12 !(PropTaut (PropTaut (PropTaut PropTaut)))))) (C13 !PropTaut)))))), Implies(Pr(V1, Neg Implies(Atom s, Pr(((PropTaut (PropTaut (PropTaut PropTaut))) !V1), Atom s))), Falsum))
*)
