extends Itt_bisect
extends Itt_poly
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
open Itt_poly
open Itt_ring2

define unfold_monom : monom{'R; 'n} <--> 'R * (nat{'n} -> nat)
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
(**)
	<<field[t:t]{Z}>>, ((addrC [0] unfold_Z) thenC reduceTopC);
]

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
