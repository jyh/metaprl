extends Itt_bisect
extends Itt_cyclic_group
extends Itt_list2
extends Itt_ring_uce

open Lm_symbol
open Lm_printf
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermSubst
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermOp
open Refiner.Refiner.RefineError
open Simple_print
open Tactic_type
open Tactic_type.Conversionals
open Tactic_type.Tacticals
open Top_conversionals
open Top_tacticals
open Dtactic
open Itt_equal
open Itt_struct
open Itt_rfun
open Itt_record
open Itt_list
open Itt_ring2

define unfold_monom : monom{'R; 'n} <--> 'R^car * (nat{'n} -> nat)
define unfold_mpoly : mpoly{'R; 'n} <--> list{monom{'R; 'n}}

declare add_monom{'m1; 'm2; 'R}

prim_rw reduce_add_monom : add_monom{('k1, 'f1); ('k2, 'f2); 'R} <--> ('k1 +['R] 'k2, 'f1)

define unfold_add_monom_mpoly : add_monom_mpoly{'mon; 'p} <--> cons{'mon; 'p}

declare add_mpoly{'p; 'q}

prim_rw reduce_add_mpolyNil : add_mpoly{nil; 'q}<--> 'q
prim_rw reduce_add_mpolyCons : add_mpoly{cons{'m; 'p}; 'q}<--> add_mpoly{'p; cons{'m; 'q}}

let reduce_add_mpolyC = sweepDnC reduce_add_mpolyCons thenC higherC reduce_add_mpolyNil thenC reduceC

declare mul_monom{'m1; 'm2; 'R}

prim_rw reduce_mul_monom : mul_monom{('k1, 'f1); ('k2, 'f2); 'R} <--> ('k1 *['R] 'k2, lambda{i.(('f1 'i) +@ ('f2 'i))})

define unfold_const_mpoly : const_mpoly{'c} <--> cons{('c, lambda{i.0}); nil}
define unfold_zero_mpoly : zero_mpoly <--> nil

define unfold_mul_monom_mpoly :
	mul_monom_mpoly{'m; 'p; 'R} <-->
	list_ind{'p; zero_mpoly; h,t,f.cons{mul_monom{'m; 'h; 'R}; 'f}}

define unfold_mul_mpoly : mul_mpoly{'p; 'q; 'R} <-->
	list_ind{'p; zero_mpoly; h,t,f.add_mpoly{mul_monom_mpoly{'h; 'q; 'R}; 'f}}

define unfold_id_mpoly : id_mpoly{'R; 'n} <--> cons{('R^"1", lambda{i.if 'i=@'n then 1 else 0}); nil}

declare eval_monomAux{'m; 'vals; 'i; 'R}

define unfold_eval_monom : eval_monom{'m; 'vals; 'R} <-->
	eval_monomAux{'m; 'vals; 0; 'R}

prim_rw reduce_eval_monomAuxNil : eval_monomAux{('k, 'f); nil; 'i; 'R} <--> 'k

prim_rw reduce_eval_monomAuxCons :
	eval_monomAux{('k, 'f); cons{'v;'vals}; 'i; 'R} <-->
	(natpower{'R; 'v; ('f 'i)} *['R] eval_monomAux{('k, 'f); 'vals; 'i +@ 1; 'R})

let reduce_eval_monomAuxC = sweepDnC reduce_eval_monomAuxCons thenC higherC reduce_eval_monomAuxNil thenC reduceC
let reduce_eval_monomC = unfold_eval_monom thenC reduce_eval_monomAuxC

define unfold_eval_mpoly : eval_mpoly{'p; 'vals; 'R} <-->
	list_ind{'p; 'R^"0"; h,t,f.(eval_monom{'h; 'vals; 'R} +['R] 'f)}

declare cmp_lexi{'m1; 'm2; 'n; 'cmp; 'eq}

prim_rw reduce_cmp_lexi : cmp_lexi{('k1,'f1); ('k2,'f2); 'n; 'cmp; 'eq} <-->
	ind{'n -@ 1;
		'cmp ('f1 ('n -@ 1)) ('f2 ('n -@ 1));
		i,f.(if 'eq ('f1 ('n -@ 'i -@ 1)) ('f2 ('n -@ 'i -@ 1))
				then 'f
				else 'cmp ('f1 ('n -@ 'i -@ 1)) ('f2 ('n -@ 'i -@ 1)))}

declare eq_monom{'m1; 'm2; 'n}

prim_rw reduce_eq_monom : eq_monom{('k1, 'f1); ('k2, 'f2); 'n} <-->
	ind{'n -@ 1; ('f1 0) =@ ('f2 0); i,f.(if ('f1 'i) =@ ('f2 'i) then 'f else bfalse)}

define unfold_inject : inject{'m; 'p; 'R; 'n} <-->
	list_ind{'p; cons{'m;nil};
		h,t,f.(if cmp_lexi{'m; 'h; 'n; lambda{x.lambda{y.'x <@ 'y}}; lambda{x.lambda{y.'x =@ 'y}}}
					then cons{'m; cons{'h; 't}}
					else if eq_monom{'m; 'h; 'n} then cons{add_monom{'m; 'h; 'R}; 't}
							else cons{'h;'f})}

define unfold_standardize : standardize{'p; 'R; 'n} <-->
	list_ind{'p; nil; h,t,f.inject{'h; 'f; 'R; 'n}}

interactive eval_standardizeIntro unitringCE[i:l] :
	[wf] sequent{ <H> >- 'p in mpoly{'R; length{'vals}} } -->
	[wf] sequent{ <H> >- 'vals in list{'R^car} } -->
	[wf] sequent{ <H> >- 'R in unitringCE[i:l] } -->
	sequent{ <H> >-
		eval_mpoly{'p; 'vals; 'R} =
		eval_mpoly{standardize{'p; 'R; length{'vals}}; 'vals; 'R} in 'R^car }

interactive eval_standardizeAssert unitringCE[i:l] eval_mpoly{'p; 'vals; 'R} :
	[wf] sequent{ <H> >- 'p in mpoly{'R; length{'vals}} } -->
	[wf] sequent{ <H> >- 'vals in list{'R^car} } -->
	[wf] sequent{ <H> >- 'R in unitringCE[i:l] } -->
	sequent{ <H>;
		( eval_mpoly{'p; 'vals; 'R}
		 =eval_mpoly{standardize{'p; 'R; length{'vals}}; 'vals; 'R}
		 in 'R^car) >- 'C } -->
	sequent{ <H> >- 'C }

interactive eval_standardizeElim {| elim [elim_typeinf <<'R>>] |} 'H unitringCE[i:l] :
	[wf] sequent{ <H> >- 'p in mpoly{'R; length{'vals}} } -->
	[wf] sequent{ <H> >- 'vals in list{'R^car} } -->
	[wf] sequent{ <H> >- 'R in unitringCE[i:l] } -->
	sequent{ <H>; ('t
		=eval_mpoly{standardize{'p; 'R; length{'vals}}; 'vals; 'R} in 'R^car); <J> >- 'C } -->
	sequent{ <H>; 't = eval_mpoly{'p; 'vals; 'R} in 'R^car; <J> >- 'C }

declare mpolyTerm{'R;'nvars}

define unfold_polyOp : polyOp <--> unit + unit
define unfold_addOp : addOp <--> inl{it}
define unfold_mulOp : mulOp <--> inl{it}
define unfold_addTerm : addTerm{'l;'r} <--> inl{(addOp,('l,'r))}
define unfold_mulTerm : mulTerm{'l;'r} <--> inl{(mulOp,('l,'r))}
define unfold_constTerm : constTerm{'c} <--> inr{inl{'c}}
define unfold_varTerm : varTerm{'i} <--> inr{inr{'i}}

prim_rw unfold_mpolyTerm : mpolyTerm{'R;'nvars} <-->
	((polyOp * (mpolyTerm{'R;'nvars} * mpolyTerm{'R;'nvars})) + ('R^car + nat{'nvars}))

interactive addTerm_wf {| intro [intro_typeinf <<'R>>] |} unitringCE[i:l] :
	sequent { <H> >- 'l in mpolyTerm{'R; 'n} } -->
	sequent { <H> >- 'r in mpolyTerm{'R; 'n} } -->
	sequent { <H> >- 'R in unitringCE[i:l] } -->
	sequent { <H> >- 'n in nat } -->
	sequent { <H> >- addTerm{'l;'r} in mpolyTerm{'R; 'n} }

interactive mulTerm_wf {| intro [intro_typeinf <<'R>>] |} unitringCE[i:l] :
	sequent { <H> >- 'l in mpolyTerm{'R; 'n} } -->
	sequent { <H> >- 'r in mpolyTerm{'R; 'n} } -->
	sequent { <H> >- 'R in unitringCE[i:l] } -->
	sequent { <H> >- 'n in nat } -->
	sequent { <H> >- mulTerm{'l;'r} in mpolyTerm{'R; 'n} }

interactive constTerm_wf {| intro [intro_typeinf <<'R>>] |} unitringCE[i:l] :
	sequent { <H> >- 'c in 'R^car } -->
	sequent { <H> >- 'R in unitringCE[i:l] } -->
	sequent { <H> >- 'n in nat } -->
	sequent { <H> >- constTerm{'c} in mpolyTerm{'R; 'n} }

interactive varTerm_wf {| intro [intro_typeinf <<'R>>] |} unitringCE[i:l] :
	sequent { <H> >- 'j in nat{'n} } -->
	sequent { <H> >- 'R in unitringCE[i:l] } -->
	sequent { <H> >- 'n in nat } -->
	sequent { <H> >- varTerm{'j} in mpolyTerm{'R; 'n} }

declare eval_mpolyTerm{'pt; 'vals; 'R}

prim_rw reduce_eval_mpolyTerm : eval_mpolyTerm{'pt; 'vals; 'R} <-->
	decide{'pt;
		node.spread{'node; op,args.spread{'args; l,r.decide{'op;
			add.(eval_mpolyTerm{'l; 'vals; 'R} +['R] eval_mpolyTerm{'r; 'vals; 'R});
			mul.(eval_mpolyTerm{'l; 'vals; 'R} *['R] eval_mpolyTerm{'r; 'vals; 'R})}}};
		leaf.decide{'leaf; const.'const; var.nth{'vals; 'var}}}

interactive_rw reduce_eval_mpolyTermAdd :
	eval_mpolyTerm{addTerm{'l;'r}; 'vals; 'R} <-->
	(eval_mpolyTerm{'l; 'vals; 'R} +['R] eval_mpolyTerm{'r; 'vals; 'R})

interactive_rw reduce_eval_mpolyTermMul :
	eval_mpolyTerm{mulTerm{'l;'r}; 'vals; 'R} <-->
	(eval_mpolyTerm{'l; 'vals; 'R} *['R] eval_mpolyTerm{'r; 'vals; 'R})

interactive_rw reduce_eval_mpolyTermConst :
	eval_mpolyTerm{constTerm{'c}; 'vals; 'R} <-->
	'c

interactive_rw reduce_eval_mpolyTermVar :
	eval_mpolyTerm{varTerm{'i}; 'vals; 'R} <-->
	nth{'vals; 'i}

declare mpoly_ofTerm{'pt; 'R}

prim_rw reduce_mpoly_ofTerm : mpoly_ofTerm{'pt; 'R} <-->
	decide{'pt;
		node.spread{'node; op,args.spread{'args; l,r.decide{'op;
			add.(add_mpoly{mpoly_ofTerm{'l; 'R}; mpoly_ofTerm{'r; 'R}});
			mul.(mul_mpoly{mpoly_ofTerm{'l; 'R}; mpoly_ofTerm{'r; 'R};'R})}}};
		leaf.decide{'leaf; const.const_mpoly{'const}; var.id_mpoly{'R;'var}}}

interactive_rw reduce_mpoly_ofTermAdd :
	mpoly_ofTerm{addTerm{'l;'r}; 'R} <-->
	add_mpoly{mpoly_ofTerm{'l; 'R}; mpoly_ofTerm{'r; 'R}}

interactive_rw reduce_mpoly_ofTermMul :
	mpoly_ofTerm{mulTerm{'l;'r}; 'R} <-->
	mul_mpoly{mpoly_ofTerm{'l; 'R}; mpoly_ofTerm{'r; 'R}; 'R}

interactive_rw reduce_mpoly_ofTermConst :
	mpoly_ofTerm{constTerm{'c}; 'R} <-->
	const_mpoly{'c}

interactive_rw reduce_mpoly_ofTermVar :
	mpoly_ofTerm{varTerm{'i}; 'R} <-->
	id_mpoly{'R; 'i}

interactive_rw mpolyTerm2mpoly :
	eval_mpolyTerm{'pt; 'vals; 'R} <-->
	eval_mpoly{mpoly_ofTerm{'pt;'R}; 'vals; 'R}

interactive mpoly_of_Term_wf {| intro [intro_typeinf <<'R>>] |} unitringCE[i:l] :
	sequent { <H> >- 'pt in mpolyTerm{'R;'n} } -->
	sequent { <H> >- 'R in unitringCE[i:l] } -->
	sequent { <H> >- 'n in nat } -->
	sequent { <H> >- mpoly_ofTerm{'pt;'R} in mpoly{'R; 'n} }

let resource reduce += [
	<<mpoly{'R; number[i:n]}>>, (unfold_mpoly thenC (addrC [0] unfold_monom));
	<<const_mpoly{'c}>>, (unfold_const_mpoly thenC reduceC);
	<<eval_monom{('k,'f); 'vals; 'R}>>, reduce_eval_monomC;
	<<eval_mpoly{'p; 'vals; 'R}>>, (unfold_eval_mpoly thenC reduceC);
	<<add_mpoly{nil; 'q}>>, (reduce_add_mpolyNil thenC reduceC);
	<<add_mpoly{cons{'m; 'p}; 'q}>>, (reduce_add_mpolyCons thenC reduceC);
	<<mul_monom{('k1,'f1); ('k2,'f2); 'R}>>, (reduce_mul_monom thenC reduceC);
	<<mul_monom_mpoly{'m; 'p; 'R}>>, (unfold_mul_monom_mpoly thenC reduceC);
	<<mul_mpoly{'p; 'q; 'R}>>, (unfold_mul_mpoly thenC reduceC);

	<<id_mpoly{'R; number[i:n]}>>, unfold_id_mpoly;
	<<zero_mpoly>>, unfold_zero_mpoly;

	<<add_monom{('k1,'f1); ('k2,'f2); 'R}>>, (reduce_add_monom thenC reduceC);
	<<cmp_lexi{('k1,'f1); ('k2,'f2); number[i:n]; 'cmp; 'eq}>>, (reduce_cmp_lexi thenC reduceC);
	<<eq_monom{('k1,'f1); ('k2,'f2); number[i:n]}>>, (reduce_eq_monom thenC reduceC);
	<<inject{('k,'f); 'p; 'R; number[i:n]}>>, (unfold_inject thenC reduceC);
	<<standardize{'p; 'R; number[i:n]}>>, (unfold_standardize thenC reduceC);

	<<eval_mpolyTerm{addTerm{'l;'r}; 'vals; 'R}>>, (reduce_eval_mpolyTermAdd thenC reduceC);
	<<eval_mpolyTerm{mulTerm{'l;'r}; 'vals; 'R}>>, (reduce_eval_mpolyTermMul thenC reduceC);
	<<eval_mpolyTerm{constTerm{'c}; 'vals; 'R}>>, (reduce_eval_mpolyTermConst thenC reduceC);
	<<eval_mpolyTerm{varTerm{number[i:n]}; 'vals; 'R}>>, (reduce_eval_mpolyTermVar thenC reduceC);

	<<mpoly_ofTerm{addTerm{'l;'r}; 'R}>>, (reduce_mpoly_ofTermAdd thenC reduceC);
	<<mpoly_ofTerm{mulTerm{'l;'r}; 'R}>>, (reduce_mpoly_ofTermMul thenC reduceC);
	<<mpoly_ofTerm{constTerm{'c}; 'R}>>, (reduce_mpoly_ofTermConst thenC reduceC);
	<<mpoly_ofTerm{varTerm{number[i:n]}; 'R}>>, (reduce_mpoly_ofTermVar thenC reduceC);
(**)
	<<field[t:t]{Z}>>, ((addrC [0] unfold_Z) thenC reduceTopC);
]

let add info t =
	if List.exists (alpha_equal t) info then info
	else t::info

let rec find_item_aux f i = function
   h::t ->
      if f h then
         Some i
      else
         find_item_aux f (i + 1) t
 | [] ->
      None

let find_index info t = find_item_aux (alpha_equal t) 0 info

let mk_intnum_term i = Itt_int_base.mk_number_term (Lm_num.num_of_int i)

let rec mk_list_of_list = function
	h::t -> mk_cons_term h (mk_list_of_list t)
 | [] -> nil_term

let mpoly_term = << mpoly{'F; 'nvars} >>
let mpoly_opname = opname_of_term mpoly_term
let is_mpoly_term = is_dep0_dep0_term mpoly_opname
let mk_mpoly_term = mk_dep0_dep0_term mpoly_opname
let dest_mpoly = dest_dep0_dep0_term mpoly_opname

let eval_mpoly_term = << eval_mpoly{'p; 'vals; 'F} >>
let eval_mpoly_opname = opname_of_term eval_mpoly_term
let is_eval_mpoly_term = is_dep0_dep0_dep0_term eval_mpoly_opname
let mk_eval_mpoly_term = mk_dep0_dep0_dep0_term eval_mpoly_opname
let dest_eval_mpoly = dest_dep0_dep0_dep0_term eval_mpoly_opname

let eval_mpolyTerm_term = << eval_mpolyTerm{'p; 'vals; 'F} >>
let eval_mpolyTerm_opname = opname_of_term eval_mpolyTerm_term
let is_eval_mpolyTerm_term = is_dep0_dep0_dep0_term eval_mpolyTerm_opname
let mk_eval_mpolyTerm_term = mk_dep0_dep0_dep0_term eval_mpolyTerm_opname
let dest_eval_mpolyTerm = dest_dep0_dep0_dep0_term eval_mpolyTerm_opname

let id_mpoly_term = << id_mpoly{'F; 'i} >>
let id_mpoly_opname = opname_of_term id_mpoly_term
let is_id_mpoly_term = is_dep0_dep0_term id_mpoly_opname
let mk_id_mpoly_term = mk_dep0_dep0_term id_mpoly_opname
let dest_id_mpoly = dest_dep0_dep0_term id_mpoly_opname

let const_mpoly_term = << const_mpoly{'v} >>
let const_mpoly_opname = opname_of_term const_mpoly_term
let is_const_mpoly_term = is_dep0_term const_mpoly_opname
let mk_const_mpoly_term = mk_dep0_term const_mpoly_opname
let dest_const_mpoly = dest_dep0_term const_mpoly_opname

let constTerm_term = << constTerm{'v} >>
let constTerm_opname = opname_of_term constTerm_term
let is_constTerm_term = is_dep0_term constTerm_opname
let mk_constTerm_term = mk_dep0_term constTerm_opname
let dest_constTerm = dest_dep0_term constTerm_opname

let varTerm_term = << varTerm{'v} >>
let varTerm_opname = opname_of_term varTerm_term
let is_varTerm_term = is_dep0_term varTerm_opname
let mk_varTerm_term = mk_dep0_term varTerm_opname
let dest_varTerm = dest_dep0_term varTerm_opname

let addTerm_term = << addTerm{'l; 'r} >>
let addTerm_opname = opname_of_term addTerm_term
let is_addTerm_term = is_dep0_dep0_term addTerm_opname
let mk_addTerm_term = mk_dep0_dep0_term addTerm_opname
let dest_addTerm = dest_dep0_dep0_term addTerm_opname

let mulTerm_term = << mulTerm{'l; 'r} >>
let mulTerm_opname = opname_of_term mulTerm_term
let is_mulTerm_term = is_dep0_dep0_term mulTerm_opname
let mk_mulTerm_term = mk_dep0_dep0_term mulTerm_opname
let dest_mulTerm = dest_dep0_dep0_term mulTerm_opname

let var2mpolyTerm f vars v =
	match find_index vars v with
		Some i ->
			mk_varTerm_term (mk_intnum_term i)
	 | None ->
			mk_constTerm_term v

let rec term2mpolyTerm f vars t =
	match explode_term t with
		<<'a 'b>> ->
			(match explode_term a with
				<<'c 'd>> ->
					let (f',fname) = dest_field c in
					(* if alpha_equal f f' *)
					if fname="*" then
						mk_mulTerm_term (term2mpolyTerm f vars d) (term2mpolyTerm f vars b)
					else if fname="+" then
						mk_addTerm_term (term2mpolyTerm f vars d) (term2mpolyTerm f vars b)
					else
						var2mpolyTerm f vars t
			 | _ -> var2mpolyTerm f vars t
			)
	 | _ -> var2mpolyTerm f vars t

let rec proveVarTypesT f_car = function
	[] -> idT
 | h::t ->
		assertT (mk_equal_term f_car h h) thenMT
		(rw (addrC [0] reduceC) (-1)) thenMT
		proveVarTypesT f_car t

let stdT ft f vars i = funT (fun p ->
	let t = if i=0 then Sequent.concl p else Sequent.nth_hyp p i in
	let f_car = mk_field_term f "car" in
	match explode_term t with
		<<'a='b in 'T>> ->
			let a' = mk_eval_mpolyTerm_term (term2mpolyTerm f vars a) (mk_list_of_list vars) f in
			let eqt = mk_equal_term f_car a a' in
			proveVarTypesT f_car vars thenMT
			(assertT eqt thenAT rw reduceC 0) thenMT
			rw (addrC [2] mpolyTerm2mpoly) (-1) thenMT
			eval_standardizeElim (-1) ft thenMT
			rw (addrC [2] reduceC) (-1) thenMT
			hypSubstT (-1) i
	 | _ -> failT
)

interactive test4 :
	sequent { <H> >-
		eval_mpoly{id_mpoly{Z; 1}; cons{2;cons{3;cons{4;nil}}}; Z}=3 in int }

interactive test5 :
	sequent { <H> >- eval_mpoly{id_mpoly{Z; 0}; cons{2;cons{3;cons{4;nil}}}; Z}=2 in int }

interactive test6 :
	sequent { <H> >- eval_mpoly{id_mpoly{Z; 3}; cons{2;cons{3;cons{4;nil}}}; Z}=1 in int }

interactive test7 :
	sequent { <H> >- eval_mpoly{id_mpoly{Z; 2}; cons{2;cons{3;cons{4;nil}}}; Z}=4 in int }

interactive test8 :
	sequent { <H> >- 'x in int } -->
	sequent { <H> >- 'y in int } -->
	sequent { <H> >-
		eval_mpoly{
			add_mpoly{id_mpoly{Z; 0};
				add_mpoly{const_mpoly{1};id_mpoly{Z; 1}}};
			cons{'x;
				cons{'y; nil}};
			Z}
		= 1 +@ 'x +@ 'y in int }

interactive test9 :
	sequent { <H> >-
		eval_mpoly{
			id_mpoly{Z;0};
			cons{2;cons{3;nil}};Z}
		= 2 in int }

interactive test11 :
	sequent { <H> >- 'x in int } -->
	sequent { <H> >- 'y in int } -->
	sequent { <H> >-
		eval_mpoly{
			add_mpoly{id_mpoly{Z;0};
				add_mpoly{mul_mpoly{id_mpoly{Z;0};id_mpoly{Z;1};Z};
					add_mpoly{id_mpoly{Z;1};const_mpoly{1}}}};
			cons{'x; cons{'y; nil}}; Z}
		='x +@ ('x *@ 'y) +@ 'y +@ 1 in int }

interactive test12 :
	sequent { <H> >- 'x in int } -->
	sequent { <H> >- 'y in int } -->
	sequent { <H> >-
		eval_mpoly{
			standardize{
				add_mpoly{id_mpoly{Z;0};
					add_mpoly{mul_mpoly{id_mpoly{Z;0};id_mpoly{Z;1};Z};
						add_mpoly{id_mpoly{Z;1};const_mpoly{1}}}};
				Z;2};
			cons{'x; cons{'y; nil}}; Z}
		=1 +@ 'y +@ 'x +@ ('x *@ 'y) in int }

interactive test13 :
	sequent { <H> >- 'x in int } -->
	sequent { <H> >- 'y in int } -->
	sequent { <H> >-
		'x +@ ('x *@ 'y) +@ 'y +@ 1 =
		eval_mpolyTerm{
			addTerm{
				varTerm{0};
				addTerm{
					mulTerm{varTerm{0};varTerm{1}};
					addTerm{varTerm{1};constTerm{1}}}};
			cons{'x; cons{'y; nil}}; Z} in int }


interactive test14 :
	sequent { <H> >- 'x in Z^car } -->
	sequent { <H> >- 'y in Z^car } -->
	sequent { <H>;
		'x +@ ('x *@ 'y) +@ 'y +@ 1 =
		eval_mpolyTerm{
			addTerm{
				varTerm{0};
				addTerm{
					mulTerm{varTerm{0};varTerm{1}};
					addTerm{varTerm{1};constTerm{1}}}};
			cons{'x; cons{'y; nil}}; Z} in Z^car
	>- 'x +@ ('x *@ 'y) +@ 'y +@ 1 = 1 +@ ('y +@ ('x +@ ('x *@ 'y))) in Z^car }

interactive test15 :
	sequent { <H> >- 'x in Z^car } -->
	sequent { <H> >- 'y in Z^car } -->
	sequent { <H> >-
		'x +[Z] ('x *[Z] 'y) +[Z] 'y +[Z] 1
		= 1 +@ ('y +@ ('x +@ ('x *@ 'y))) in Z^car }
