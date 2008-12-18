open Lm_symbol
open Lm_printf

open Term_sig
open Refiner.Refiner
open Term
open RefineError

open Hilbert_internal
open S4_logic
open LP
open S4G

module Structured_S4_Logic =
struct

   open Jlogic_sig

   let is_and_term = S4_Logic.is_and_term
   let dest_and = S4_Logic.dest_and
   let is_or_term = S4_Logic.is_or_term
   let dest_or = S4_Logic.dest_or
   let is_implies_term = S4_Logic.is_implies_term
   let dest_implies = S4_Logic.dest_implies
   let is_not_term = S4_Logic.is_not_term
   let dest_not = S4_Logic.dest_not

   let is_box_term = S4_Logic.is_box_term
   let dest_box = S4_Logic.dest_box

   let is_exists_term = S4_Logic.is_exists_term
   let dest_exists = S4_Logic.dest_exists
   let is_all_term = S4_Logic.is_all_term
   let dest_all = S4_Logic.dest_all

   type inference = gentzen list
   let empty_inf = []

   let rec term2formula t =
      if is_and_term t then
         let a, b = dest_and t in
         And(term2formula a,term2formula  b)
      else if is_or_term t then
         let a, b = dest_or t in
         Or(term2formula a, term2formula b)
      else if is_not_term t then
         Neg(term2formula (dest_not t))
      else if is_implies_term t then
         let a, b = dest_implies t in
         Implies(term2formula a, term2formula b)
      else if is_box_term t then
         let f, a = dest_box t in
         Box(Modal f, term2formula a)
      else if is_false_term t then
         Falsum
      else if is_var_term t then
         Atom (dest_var t)
      else
         raise (RefineError("s4_internal.term2formula, unsupported term", TermError(t)))

	let rec formula2term = function
		Falsum ->
			false_term
	 | Atom a ->
	 		mk_var_term a
	 | And(a,b) ->
	 		mk_and_term (formula2term a) (formula2term b)
	 | Or(a,b) ->
	 		mk_or_term (formula2term a) (formula2term b)
	 | Neg a ->
	 		mk_not_term (formula2term a)
	 | Implies(a,b) ->
	 		mk_implies_term (formula2term a) (formula2term b)
	 | Box(Modal i, a) ->
	 		mk_box_term (Lm_num.num_of_int i) (formula2term a)
	 | Box(Evidence _, _) ->
	 		raise (Invalid_argument "Evidence modality can be used only for internal purposes")
	 | Pr(t, a) ->
	 		raise (Invalid_argument "Pr(t,a) can not be used in an input")

   let append_inf inf hyp _ r =
      match r, inf with
         Ax, _ ->
            (Axiom(term2formula hyp), FSet.empty, FSet.empty) :: inf
       | Negl,t::ts ->
		 		begin match term2formula hyp with
					Neg a ->
		  				(NegLeft(a, t), FSet.empty, FSet.empty) :: ts
				 | _ ->
				 		raise (RefineError("Structured_S4_Logic.append_inf unexpected argument of NegLeft", TermError hyp))
				end
		 | Negr, t::ts ->
		 		begin match term2formula hyp with
					Neg a ->
						(NegRight(a, t), FSet.empty, FSet.empty) :: ts
				 | _ ->
                  raise (RefineError("Structured_S4_Logic.append_inf unexpected argument of NegRight", TermError hyp))
				end
       | Impl,t1::t2::ts ->
            let implication = term2formula hyp in
            begin match implication with
               Implies(a, b) ->
                  (ImplLeft(a, b, t1, t2), FSet.empty, FSet.empty) :: ts
             | _ ->
                  raise (RefineError("Structured_S4_Logic.append_inf unexpected argument of ImplLeft", TermError hyp))
            end
       | Impr,t::ts ->
            let implication = term2formula hyp in
            begin match implication with
               Implies(a, b) ->
                  (ImplRight(a, b, t), FSet.empty, FSet.empty) :: ts
             | _ ->
                  raise (RefineError("Structured_S4_Logic.append_inf unexpected argument of ImplRight", TermError hyp))
            end
		 | Andl, t::ts ->
		 		let conjunction = term2formula hyp in
				begin match conjunction with
					And(a,b) ->
						(AndLeft(a, b, t), FSet.empty, FSet.empty) :: ts
				 | _ ->
				 		raise (RefineError("Structured_S4_Logic.append_inf unexpected argument of AndLeft", TermError hyp))
				end
		 | Andr, t1::t2::ts ->
		 		let conjunction = term2formula hyp in
				begin match conjunction with
					And(a,b) ->
						(AndRight(a, b, t1, t2), FSet.empty, FSet.empty) :: ts
				 | _ ->
				 		raise (RefineError("Structured_S4_Logic.append_inf unexpected argument of AndRight", TermError hyp))
				end
		 | Orl, t1::t2::ts ->
		 		let disjunction = term2formula hyp in
				begin match disjunction with
					Or(a,b) ->
						(OrLeft(a, b, t1, t2), FSet.empty, FSet.empty) :: ts
				 | _ ->
				 		raise (RefineError("Structured_S4_Logic.append_inf unexpected argument of OrLeft", TermError hyp))
				end
		 | Orr, t::ts ->
		 		let disjunction = term2formula hyp in
				begin match disjunction with
					Or(a,b) ->
						(OrRight(a, b, t), FSet.empty, FSet.empty) :: ts
				 | _ ->
				 		raise (RefineError("Structured_S4_Logic.append_inf unexpected argument of OrRight", TermError hyp))
				end
       | Boxr,t::ts ->
            let f = term2formula hyp in
            begin match f with
               Box(Modal i, a) ->
               (BoxRight(i, a, t), FSet.empty, FSet.empty) :: ts
             | _ ->
                  raise (RefineError("Structured_S4_Logic.append_inf unexpected argument of BoxRight", TermError hyp))
            end
       | Boxl,t::ts ->
		 		let f = match term2formula hyp with
					Box(_,a) -> a
				 | _ -> raise (Invalid_argument "Structured_S4_Logic.append_inf: a box formula expected in Boxl")
				in
            (BoxLeft(f, t), FSet.empty, FSet.empty) :: ts
       | Fail,_ -> raise (RefineError("Structured_S4_Logic.append_inf", StringError "failed"))
       | _ ->
            raise (Invalid_argument "Structured_S4_Logic.append_inf: unsupported inference rule")

end

open Structured_S4_Logic

module Structured_S4_Prover = Jall.JProver(Structured_S4_Logic)
open Structured_S4_Prover

let rec fill_sequents hyps concls derivation =
printf "\n%a\n>-\n%a\n" FSet.print hyps FSet.print concls;
match derivation with
	Axiom f as r, _, _ ->
		r, hyps, concls
 | AxiomFalsum as r, _, _ ->
 		r, hyps, concls
 | NegLeft(a, subder), _, _ ->
 		let hyps0 = FSet.remove hyps (Neg a) in
		let concls0 = FSet.add concls a in
		NegLeft(a, fill_sequents hyps0 concls0 subder), hyps, concls
 | NegRight(a, subder), _, _ ->
 		let hyps0 = FSet.add hyps a in
		let concls0 = FSet.remove concls (Neg a) in
		NegRight(a, fill_sequents hyps0 concls0 subder), hyps, concls
 | ImplLeft(a, b, left, right), _, _ ->
 		let gamma = FSet.remove hyps (Implies(a,b)) in
		ImplLeft(a,b,
			fill_sequents gamma (FSet.add concls a) left,
			fill_sequents (FSet.add gamma b) concls right
		),
		hyps,
		concls
 | ImplRight(a, b, subder), _, _ ->
 		let delta = FSet.remove concls (Implies(a,b)) in
		ImplRight(a, b, fill_sequents (FSet.add hyps a) (FSet.add delta b) subder), hyps, concls
 | AndLeft(a, b, subder), _, _ ->
 		let gamma = FSet.remove hyps (And(a, b)) in
		AndLeft(a, b, fill_sequents (FSet.add (FSet.add gamma a) b) concls subder), hyps, concls
 | AndRight(a, b, left, right), _, _ ->
 		let delta = FSet.remove concls (And(a,b)) in
		AndRight(a, b,
			fill_sequents hyps (FSet.add delta a) left,
			fill_sequents hyps (FSet.add delta b) right
		),
		hyps,
		concls
 | OrLeft(a, b, left, right), _, _ ->
 		let gamma = FSet.remove hyps (Or(a,b)) in
		OrLeft(a, b,
			fill_sequents (FSet.add gamma a) concls left,
			fill_sequents (FSet.add gamma b) concls right
		),
		hyps,
		concls
 | OrRight(a, b, subder), _, _ ->
 		let delta = FSet.remove concls (Or(a,b)) in
		OrRight(a, b,
				fill_sequents hyps (FSet.add (FSet.add delta a) b) subder
		),
		hyps,
		concls
 | BoxLeft(a, subder), _, _ ->
		BoxLeft(a, fill_sequents (FSet.add hyps a) concls subder), hyps, concls
 | BoxRight(i, b, subder), _, _ ->
 		let boxB = Box(Modal i, b) in
 		let boxAi = FSet.filter (weaker_or_equal boxB) hyps in
		BoxRight(i, b, fill_sequents boxAi (FSet.singleton b) subder), hyps, concls

let _ =
	let s = Atom(add "s") in
	let f = (Box(Modal 0, Neg(Implies(s, Box(Modal 0, s))))) in
	let tm = formula2term f in
	let infs = gen_prover (Some 100) Jlogic_sig.S4 [tm] [] in
	match infs with
		[inf] ->
			printf "Filling in sequents\n";
			let g = fill_sequents (FSet.singleton f) FSet.empty inf in
			realize g
	 | _ -> raise (Invalid_argument "resulting inference has more than one root")

let _ = (* AndRight test *)
   let a = Atom(add "a") in
	let b = Atom(add "b") in
	let af = Box(Modal 0, a) in
	let bf = Box(Modal 0, b) in
	let abf = Box(Modal 0, And(a,b)) in
   let atm = formula2term af in
	let btm = formula2term bf in
	let abtm = formula2term abf in
   let infs = gen_prover (Some 100) Jlogic_sig.S4 [atm;btm] [abtm] in
   match infs with
      [inf] ->
         printf "Filling in sequents\n";
         let g = fill_sequents (FSet.add (FSet.singleton af) bf) (FSet.singleton abf) inf in
         realize g
    | _ -> raise (Invalid_argument "resulting inference has more than one root")

let _ = (* AndLeft test *)
   let a = Atom(add "a") in
   let b = Atom(add "b") in
   let af = Box(Modal 0, a) in
   let abf = Box(Modal 0, And(a,b)) in
   let atm = formula2term af in
   let abtm = formula2term abf in
   let infs = gen_prover (Some 100) Jlogic_sig.S4 [abtm] [atm] in
   match infs with
      [inf] ->
         printf "Filling in sequents\n";
         let g = fill_sequents (FSet.singleton abf) (FSet.singleton af) inf in
         realize g
    | _ -> raise (Invalid_argument "resulting inference has more than one root")

let _ = (* OrLeft test *)
   let a = Atom(add "a") in
   let b = Atom(add "b") in
   let abf = Box(Modal 0, Or(a,b)) in
   let atm = formula2term a in
	let btm = formula2term b in
   let abtm = formula2term abf in
   let infs = gen_prover (Some 100) Jlogic_sig.S4 [abtm] [btm;atm] in
   match infs with
      [inf] ->
         printf "Filling in sequents\n";
         let g = fill_sequents (FSet.singleton abf) (FSet.add (FSet.singleton a) b) inf in
         realize g
    | _ -> raise (Invalid_argument "resulting inference has more than one root")

let _ = (* OrRight test *)
   let a = Atom(add "a") in
   let b = Atom(add "b") in
   let af = Box(Modal 0, a) in
   let abf = Box(Modal 0, Or(a,b)) in
   let atm = formula2term af in
   let abtm = formula2term abf in
   let infs = gen_prover (Some 100) Jlogic_sig.S4 [atm] [abtm] in
   match infs with
      [inf] ->
         printf "Filling in sequents\n";
         let g = fill_sequents (FSet.singleton af) (FSet.singleton abf) inf in
         realize g
    | _ -> raise (Invalid_argument "resulting inference has more than one root")

let _ = (* NegLeft test *)
   let a = Atom(add "a") in
   let af = Neg a in
   let atm = formula2term af in
   let infs = gen_prover (Some 100) Jlogic_sig.S4 [formula2term a; atm] [] in
   match infs with
      [inf] ->
         printf "Filling in sequents\n";
         let g = fill_sequents (FSet.add (FSet.singleton a) af) FSet.empty inf in
         realize g
    | _ -> raise (Invalid_argument "resulting inference has more than one root")

let _ = (* NegRight test *)
   let a = Atom(add "a") in
   let af = Neg(Box(Modal 0, Neg a)) in
   let atm = formula2term af in
   let infs = gen_prover (Some 100) Jlogic_sig.S4 [formula2term a] [atm] in
   match infs with
      [inf] ->
         printf "Filling in sequents\n";
         let g = fill_sequents (FSet.singleton a) (FSet.singleton af) inf in
         realize g
    | _ -> raise (Invalid_argument "resulting inference has more than one root")

let _ =
   let a = Atom(add "a") in
   let c = Box(Modal 1, Implies(a,a)) in
   let ctm = formula2term c in
   let infs = gen_prover (Some 100) Jlogic_sig.S4 [] [ctm] in
   match infs with
      [inf] ->
         printf "Filling in sequents\n";
         let g = fill_sequents (FSet.empty) (FSet.singleton c) inf in
         realize g
    | _ -> raise (Invalid_argument "resulting inference has more than one root")

(* test0: box[0]{'a} >- concl{| box[1]{'a} |} *)
let _ =
	let a = Atom(add "a") in
	let h = Box(Modal 0, a) in
	let c = Box(Modal 1, a) in
	let htm = formula2term h in
	let ctm = formula2term c in
	let infs = gen_prover (Some 100) Jlogic_sig.S4 [htm] [ctm] in
	match infs with
		[inf] ->
         printf "Filling in sequents\n";
         let g = fill_sequents (FSet.singleton h) (FSet.singleton c) inf in
         realize g
    | _ -> raise (Invalid_argument "resulting inference has more than one root")

(* test1: box[2]{box[0]{'a}} >- concl{| box[1]{'a} |} *)
let _ =
   let a = Atom(add "a") in
   let h = Box(Modal 2, Box(Modal 0, a)) in
   let c = Box(Modal 1, a) in
   let htm = formula2term h in
   let ctm = formula2term c in
   let infs = gen_prover (Some 100) Jlogic_sig.S4 [htm] [ctm] in
   match infs with
      [inf] ->
         printf "Filling in sequents\n";
         let g = fill_sequents (FSet.singleton h) (FSet.singleton c) inf in
         realize g
    | _ -> raise (Invalid_argument "resulting inference has more than one root")

(* test1a: box[0]{box[2]{box[0]{'a}}} >- concl{| box[1]{'a} |} *)
let _ =
   let a = Atom(add "a") in
   let h = Box(Modal 0, Box(Modal 2, Box(Modal 0, a))) in
   let c = Box(Modal 1, a) in
   let htm = formula2term h in
   let ctm = formula2term c in
   let infs = gen_prover (Some 100) Jlogic_sig.S4 [htm] [ctm] in
   match infs with
      [inf] ->
         printf "Filling in sequents\n";
         let g = fill_sequents (FSet.singleton h) (FSet.singleton c) inf in
         realize g
    | _ -> raise (Invalid_argument "resulting inference has more than one root")

(* Wise men *)

let m1 = Atom(add "m1")
let m2 = Atom(add "m2")
let m3 = Atom(add "m3")

let kwh i a = Or(Box(Modal i, a), Box(Modal i, Neg a))
(*
let kao = And(kwh 1 m2, And(kwh 1 m3, And(kwh 2 m1, kwh 2 m3)))

let w0 = And(Box(Modal 0, kao), Box(Modal 0, Neg(And(Neg m1, And(Neg m2, Neg m3)))))

let w2 = And(w0, And(Box(Modal 0, Neg(kwh 1 m1)), Box(Modal 0, Neg(kwh 2 m2))))

let _= (* sequent { w2 >- concl{| box[0]{m3} |} } *)
   let h = w2 in
   let c = Box(Modal 0, m3) in
   let htm = formula2term h in
   let ctm = formula2term c in
   let infs = gen_prover (Some 100) Jlogic_sig.S4 [htm] [ctm] in
   match infs with
      [inf] ->
         printf "Filling in sequents\n";
         let g = fill_sequents (FSet.singleton h) (FSet.singleton c) inf in
         realize g
    | _ -> raise (Invalid_argument "resulting inference has more than one root")
*)
(* Muddy children, 4 children *)

let c1 = Atom(add "c1")
let c2 = Atom(add "c2")
let c3 = Atom(add "c3")
let c4 = Atom(add "c4")

let mch4_KAO = Box(Modal 0,
   List.fold_left (fun x acc -> And(x, acc)) (kwh 1 c2)
		[	kwh 1 c3 ; kwh 1 c4 ;
      	kwh 2 c1 ; kwh 2 c3 ; kwh 2 c4 ;
      	kwh 3 c1 ; kwh 3 c2 ; kwh 3 c4 ;
      	kwh 4 c1 ; kwh 4 c2 ; kwh 4 c3
		]
)

let s = Or(kwh 1 c1, Or(kwh 2 c2, Or(kwh 3 c3, kwh 4  c4)))

let nbk = Box(Modal 0,
	And(Neg(kwh 1 c1), And(Neg(kwh 2 c2), And(Neg(kwh 3 c3), Neg(kwh 4 c4))))
)

let s0 = And(c1, And(c2, And(Neg c3, Neg c4)))
let s1 = Box(Modal 0, Or(c1, Or(c2, Or(c3, c4))))
let s2 =
   Box(Modal 0,
      Or(And(c1, c2),
      Or(And(c1, c3),
      Or(And(c1, c4),
      Or(And(c2, c3),
      Or(And(c2, c4),
      And(c3, c4))))))
   )

let s3 =
   Box(Modal 0,
      And(kwh 1 c1,
      kwh 2 c2)
   )

let short_KAO =
   Box(Modal 0,
      And(kwh 1 c2, And(kwh 1 c3, And(kwh 1 c4,
      And(kwh 2 c1, And(kwh 2 c3, kwh 2 c4)))))
   )

(*
interactive muddy_children :
   sequent { s0; s2; NBK; mch4_KAO >- concl {| box[1]{c1} & box[2]{c2} & box[3]{not{c3}} & box[4]{not{c4}} |} }
*)
let _=
   let h = [s0;s2;nbk;mch4_KAO] in
   let c = And(Box(Modal 1, c1), And(Box(Modal 2, c2), And(Box(Modal 3, Neg c3), Box(Modal 4, Neg c4)))) in
	let goal = Implies(And(s0,And(s2,And(nbk,mch4_KAO))), c) in
(*   let htm = List.map formula2term h in
   let ctm = formula2term c in*)
	let goal_tm = formula2term goal in
   let infs = gen_prover (Some 100) Jlogic_sig.S4 [] [goal_tm] in
   match infs with
      [inf] ->
         printf "Filling in sequents\n";
			let hyps = FSet.of_list h in
         let g = fill_sequents hyps (FSet.empty) inf in
         full g
    | _ -> raise (Invalid_argument "resulting inference has more than one root")

