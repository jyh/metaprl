extends Itt_bisect
extends Itt_cyclic_group
extends Itt_list2
extends Itt_ring_uce
extends Itt_w

open Lm_debug
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

let debug_mpoly_eval =
   create_debug (**)
      { debug_name = "debug_mpoly_eval";
        debug_description = "display mpoly_eval steps";
        debug_value = false
      }

(*
 * RESOURCES USED BY standardizeT
 *)
let extract_data tbl =
   let rw e =
      let t = env_term e in
      let conv =
         try
            (* Find and apply the right tactic *)
            if !debug_mpoly_eval then
               Lm_printf.eprintf "Conversionals: lookup %a%t" debug_print t eflush;
            Term_match_table.lookup tbl Term_match_table.select_all t
         with
            Not_found ->
               raise (RefineError ("Conversionals.extract_data", StringTermError ("no reduction for", t)))
      in
         if !debug_mpoly_eval then
            Lm_printf.eprintf "Conversionals: applying %a%t" debug_print t eflush;
         conv
   in
      funC rw

let process_mpoly_eval_resource_rw_annotation =
   Rewrite.redex_and_conv_of_rw_annotation "mpoly_eval"

(*
 * Resource.
 *)
let resource (term * conv, conv) mpoly_eval =
   Term_match_table.table_resource_info extract_data

let mpoly_evalTopC_env e =
   Sequent.get_resource_arg (env_arg e) get_mpoly_eval_resource

let mpoly_evalTopC = funC mpoly_evalTopC_env

let mpoly_evalC = repeatC (higherC mpoly_evalTopC)
(*let mpoly_evalC = repeatC (lowerC mpoly_evalTopC)*)
(*slow:
let mpoly_evalC = repeatC (lowerC reduceTopC)
*)
(*let mpoly_evalC = reduceC*)
(*******************************************************************)

define unfold_list_n : list{'T; 'n} <--> {l: list{'T} | length{'l}='n in int}

declare list_ind2{'l1; 'l2; 'base; h1,t1,h2,t2,f. 'step['h1;'t1;'h2;'t2;'f]}

prim_rw reduce_list_ind2Nil : list_ind2{nil; nil; 'base; h1, t1, h2, t2, f. 'step['h1; 't1; 'h2; 't2; 'f]} <--> 'base

prim_rw reduce_list_ind2Cons : list_ind2{cons{'ah;'at}; cons{'bh;'bt}; 'base; h1,t1,h2,t2,f. 'step['h1;'t1;'h2;'t2;'f]} <-->
	'step['ah;'at;'bh;'bt;list_ind2{'at;'bt;'base;h1,t1,h2,t2,f. 'step['h1;'t1;'h2;'t2;'f]}]

define unfold_map2 : map2{'f; 'l1; 'l2} <--> list_ind2{'l1; 'l2; nil; h1,t1,h2,t2,step.cons{'f 'h1 'h2;'step}}

define unfold_monom : monom{'R; 'n} <--> 'R^car * list{nat; 'n}
define unfold_mpoly : mpoly{'R; 'n} <--> list{monom{'R; 'n}}

declare add_monom{'m1; 'm2; 'R}

prim_rw reduce_add_monom : add_monom{('k1, 'f); ('k2, 'f); 'R} <--> ('k1 +['R] 'k2, 'f)

define unfold_add_monom_mpoly : add_monom_mpoly{'mon; 'p} <--> cons{'mon; 'p}

declare add_mpoly{'p; 'q}

prim_rw reduce_add_mpolyNil : add_mpoly{nil; 'q}<--> 'q
prim_rw reduce_add_mpolyCons : add_mpoly{cons{'m; 'p}; 'q}<--> add_mpoly{'p; cons{'m; 'q}}

let reduce_add_mpolyC = sweepDnC reduce_add_mpolyCons thenC higherC reduce_add_mpolyNil

declare mul_monom{'m1; 'm2; 'R}

prim_rw reduce_mul_monom : mul_monom{('k1, 'f1); ('k2, 'f2); 'R} <-->
	('k1 *['R] 'k2, map2{lambda{x.lambda{y.('x +@ 'y)}}; 'f1; 'f2})

define unfold_const_mpoly : const_mpoly{'c; 'n} <--> cons{('c, mklist{'n; lambda{x.0}}); nil}
define unfold_zero_mpoly : zero_mpoly <--> nil

define unfold_mul_monom_mpoly :
	mul_monom_mpoly{'m; 'p; 'R} <-->
	list_ind{'p; zero_mpoly; h,t,f.cons{mul_monom{'m; 'h; 'R}; 'f}}

define unfold_mul_mpoly : mul_mpoly{'p; 'q; 'R} <-->
	list_ind{'p; zero_mpoly; h,t,f.add_mpoly{mul_monom_mpoly{'h; 'q; 'R}; 'f}}

define unfold_id_mpoly : id_mpoly{'i; 'R; 'n} <--> cons{('R^"1", mklist{'n;lambda{i_id.if 'i_id=@'i then 1 else 0}}); nil}

declare eval_monom{'m; 'vals; 'R}

prim_rw reduce_eval_monom : eval_monom{('k,'f); 'vals; 'R} <-->
	('k *['R] list_ind2{'f; 'vals; 'R^"1"; exp,t1,v,t2,step.(natpower{'R; 'v; 'exp} *['R] 'step)})

define unfold_eval_mpoly : eval_mpoly{'p; 'vals; 'R} <-->
	list_ind{'p; 'R^"0"; h,t,f.(eval_monom{'h; 'vals; 'R} +['R] 'f)}

declare cmp_lexi{'m1; 'm2; 'cmp; 'eq}

prim_rw reduce_cmp_lexi : cmp_lexi{('k1,'f1); ('k2,'f2); 'cmp; 'eq} <-->
	list_ind2{'f1; 'f2; bfalse; h1,t1,h2,t2,step.(if 'eq 'h1 'h2 then 'step else 'cmp 'h1 'h2)}

declare eq_monom{'m1; 'm2}

prim_rw reduce_eq_monom : eq_monom{('k1, 'f1); ('k2, 'f2)} <-->
	list_ind2{'f1; 'f2; btrue; h1,t1,h2,t2,step.(if 'h1 =@ 'h2 then 'step else bfalse)}

define unfold_inject : inject{'m; 'p; 'R; 'n} <-->
	list_ind{'p; cons{'m;nil};
		h,t,f.(if cmp_lexi{'m; 'h; lambda{x.lambda{y.'x <@ 'y}}; lambda{x.lambda{y.'x =@ 'y}}}
					then cons{'m; cons{'h; 't}}
					else if eq_monom{'m; 'h} then cons{add_monom{'m; 'h; 'R}; 't}
							else cons{'h;'f})}

define unfold_standardize : standardize{'p; 'R; 'n} <-->
	list_ind{'p; nil; h,t,f.inject{'h; 'f; 'R; 'n}}

interactive monom_wf {| intro [] |} :
	sequent { <H> >- 'R^car Type } -->
	sequent { <H> >- 'n in nat } -->
	sequent { <H> >- monom{'R; 'n} Type }

interactive mpoly_wf {| intro [] |} :
	sequent { <H> >- 'R^car Type } -->
	sequent { <H> >- 'n in nat } -->
	sequent { <H> >- mpoly{'R; 'n} Type }

interactive nil_in_mpoly {| intro [] |} :
	sequent { <H> >- 'R^car Type } -->
	sequent { <H> >- 'n in nat } -->
	sequent { <H> >- nil in mpoly{'R; 'n} }

interactive cons_in_mpoly {| intro [] |} :
	sequent { <H> >- 'm in monom{'R; 'n} } -->
	sequent { <H> >- 'p in mpoly{'R; 'n} } -->
	sequent { <H> >- cons{'m;'p} in mpoly{'R; 'n} }

interactive zero_mpoly_wf {| intro [] |} :
	sequent { <H> >- 'R^car Type } -->
	sequent { <H> >- 'n in nat } -->
	sequent { <H> >- zero_mpoly in mpoly{'R; 'n} }

interactive add_mpoly_wf {| intro [intro_typeinf <<'R>>] |} unitringCE[i:l] :
	sequent { <H> >- 'p in mpoly{'R; 'n} } -->
	sequent { <H> >- 'q in mpoly{'R; 'n} } -->
	[wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
	[wf] sequent { <H> >- 'n in nat } -->
	sequent { <H> >- add_mpoly{'p; 'q} in mpoly{'R; 'n} }

interactive mul_monom_wf {| intro [intro_typeinf <<'R>>] |} unitringCE[i:l] :
	sequent { <H> >- 'm1 in monom{'R; 'n} } -->
	sequent { <H> >- 'm2 in monom{'R; 'n} } -->
	[wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
	[wf] sequent { <H> >- 'n in nat } -->
	sequent { <H> >- mul_monom{'m1; 'm2; 'R} in monom{'R; 'n} }

interactive mul_monom_mpoly_wf {| intro [intro_typeinf <<'R>>] |} unitringCE[i:l] :
	sequent { <H> >- 'm in monom{'R; 'n} } -->
	sequent { <H> >- 'p in mpoly{'R; 'n} } -->
	[wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
	[wf] sequent { <H> >- 'n in nat } -->
	sequent { <H> >- mul_monom_mpoly{'m; 'p; 'R} in mpoly{'R; 'n} }

interactive mul_mpoly_wf {| intro [intro_typeinf <<'R>>] |} unitringCE[i:l] :
	sequent { <H> >- 'p in mpoly{'R; 'n} } -->
	sequent { <H> >- 'q in mpoly{'R; 'n} } -->
	[wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
	[wf] sequent { <H> >- 'n in nat } -->
	sequent { <H> >- mul_mpoly{'p; 'q; 'R} in mpoly{'R; 'n} }

interactive const_mpoly_wf {| intro [] |} :
	sequent { <H> >- 'c in 'R^car } -->
	sequent { <H> >- 'n in nat } -->
	sequent { <H> >- const_mpoly{'c; 'n} in mpoly{'R; 'n} }

interactive id_mpoly_wf {| intro [] |} :
	sequent { <H> >- 'i in nat{'n} } -->
	sequent { <H> >- 'R^"1" in 'R^car } -->
	sequent { <H> >- 'n in nat } -->
	sequent { <H> >- id_mpoly{'i; 'R; 'n} in mpoly{'R; 'n} }

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

interactive eval_standardizeElim 'H unitringCE[i:l] :
	[wf] sequent{ <H> >- 'p in mpoly{'R; length{'vals}} } -->
	[wf] sequent{ <H> >- 'vals in list{'R^car} } -->
	[wf] sequent{ <H> >- 'R in unitringCE[i:l] } -->
	sequent{ <H>; ('t
		=eval_mpoly{standardize{'p; 'R; length{'vals}}; 'vals; 'R} in 'R^car); <J> >- 'C } -->
	sequent{ <H>; 't = eval_mpoly{'p; 'vals; 'R} in 'R^car; <J> >- 'C }

define unfold_mpolyTerm : mpolyTerm{'R;'nvars} <-->
	w{(unit + unit) + ('R^car + nat{'nvars});
		node.decide{'node;
			op.(unit + unit);
			leaf.void}}

define unfold_addOp : addOp <--> inl{inl{it}}
define unfold_mulOp : mulOp <--> inl{inr{it}}
define unfold_constLeaf : constLeaf{'c} <--> inr{inl{'c}}
define unfold_varLeaf : varLeaf{'v} <--> inr{inr{'v}}

define unfold_addTerm : addTerm{'l;'r} <-->
	tree{addOp; lambda{child.decide{'child; x.'l; x.'r}}}

define unfold_mulTerm : mulTerm{'l;'r} <-->
	tree{mulOp; lambda{child.decide{'child; x.'l; x.'r}}}

define unfold_constTerm : constTerm{'c} <--> tree{constLeaf{'c}; lambda{x.'x}}
define unfold_varTerm : varTerm{'i} <--> tree{varLeaf{'i}; lambda{x.'x}}

define unfold_leftOperand : leftOperand <--> inl{it}
define unfold_rightOperand : rightOperand <--> inr{it}

define unfold_eval_mpolyTerm : eval_mpolyTerm{'pt; 'vals; 'R} <-->
	tree_ind{'pt; a,f,g.(
		decide{'a;
			op.decide{'op;
				l.(('g leftOperand) +['R] ('g rightOperand));
				r.(('g leftOperand) *['R] ('g rightOperand))};
			leaf.decide{'leaf; c.'c; var.nth{'vals; 'var}}})}

define unfold_mpoly_ofTerm : mpoly_ofTerm{'pt; 'R; 'n} <-->
	tree_ind{'pt; a,f,g.(
		decide{'a;
			op.decide{'op;
				l.add_mpoly{('g leftOperand); ('g rightOperand)};
				r.mul_mpoly{('g leftOperand); ('g rightOperand); 'R}};
			leaf.decide{'leaf; c.const_mpoly{'c; 'n}; var.id_mpoly{'var; 'R; 'n}}})}

interactive mpolyTerm_wf {| intro [] |} :
	sequent { <H> >- 'R^car Type } -->
	sequent { <H> >- 'n in nat } -->
	sequent { <H> >- mpolyTerm{'R; 'n} Type }

interactive addTerm_wf {| intro [] |} :
	sequent { <H> >- 'l in mpolyTerm{'R; 'n} } -->
	sequent { <H> >- 'r in mpolyTerm{'R; 'n} } -->
	[wf] sequent { <H> >- 'R^car Type } -->
	[wf] sequent { <H> >- 'n in nat } -->
	sequent { <H> >- addTerm{'l;'r} in mpolyTerm{'R; 'n} }

interactive mulTerm_wf {| intro [] |} :
	sequent { <H> >- 'l in mpolyTerm{'R; 'n} } -->
	sequent { <H> >- 'r in mpolyTerm{'R; 'n} } -->
	[wf] sequent { <H> >- 'R^car Type } -->
	[wf] sequent { <H> >- 'n in nat } -->
	sequent { <H> >- mulTerm{'l;'r} in mpolyTerm{'R; 'n} }

interactive constTerm_wf {| intro [] |} :
	sequent { <H> >- 'c in 'R^car } -->
	sequent { <H> >- 'R^car Type } -->
	sequent { <H> >- 'n in nat } -->
	sequent { <H> >- constTerm{'c} in mpolyTerm{'R; 'n} }

interactive varTerm_wf {| intro [] |} :
	sequent { <H> >- 'j in nat{'n} } -->
	sequent { <H> >- 'R^car Type } -->
	sequent { <H> >- 'n in nat } -->
	sequent { <H> >- varTerm{'j} in mpolyTerm{'R; 'n} }

interactive mpoly_ofTerm_wf {| intro [intro_typeinf <<'R>>] |} unitringCE[i:l] :
	sequent { <H> >- 'pt in mpolyTerm{'R; 'n} } -->
	[wf] sequent { <H> >- 'R in unitringCE[i:l] } -->
	[wf] sequent { <H> >- 'n in nat } -->
	sequent { <H> >- mpoly_ofTerm{'pt; 'R; 'n} in mpoly{'R; 'n} }

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

interactive_rw reduce_mpoly_ofTermAdd :
	mpoly_ofTerm{addTerm{'l;'r}; 'R; 'n} <-->
	add_mpoly{mpoly_ofTerm{'l; 'R; 'n}; mpoly_ofTerm{'r; 'R; 'n}}

interactive_rw reduce_mpoly_ofTermMul :
	mpoly_ofTerm{mulTerm{'l;'r}; 'R; 'n} <-->
	mul_mpoly{mpoly_ofTerm{'l; 'R; 'n}; mpoly_ofTerm{'r; 'R; 'n}; 'R}

interactive_rw reduce_mpoly_ofTermConst :
	mpoly_ofTerm{constTerm{'c}; 'R; 'n} <-->
	const_mpoly{'c; 'n}

interactive_rw reduce_mpoly_ofTermVar :
	mpoly_ofTerm{varTerm{'i}; 'R; 'n} <-->
	id_mpoly{'i; 'R; 'n}

interactive_rw mpolyTerm2mpoly :
	eval_mpolyTerm{'pt; 'vals; 'R} <-->
	eval_mpoly{mpoly_ofTerm{'pt; 'R; length{'vals}}; 'vals; 'R}

let tailC = mpoly_evalC (*thenC reduceC*)

let resource mpoly_eval (*reduce*) += [
	<<list_ind2{nil; nil; 'base; h1,t1,h2,t2,f.'step['h1;'t2;'h2;'t2;'f]}>>, (reduce_list_ind2Nil thenC tailC);
	<<list_ind2{cons{'ha;'at}; cons{'bh;'bt}; 'base; h1,t1,h2,t2,f.'step['h1;'t2;'h2;'t2;'f]}>>, (reduce_list_ind2Cons thenC tailC);
	<<map2{'f; 'l1; 'l2}>>, (unfold_map2 thenC tailC);
	<<mklist{number[i:n]; 'f}>>, (Itt_list2.unfold_mklist thenC tailC);
(**)
	<<mpoly{'R; number[i:n]}>>, (unfold_mpoly thenC (addrC [0] unfold_monom));
	<<const_mpoly{'c; number[i:n]}>>, (unfold_const_mpoly thenC tailC);
	<<eval_monom{('k,'f); 'vals; 'R}>>, (reduce_eval_monom thenC tailC);
	<<eval_mpoly{cons{'h;'t}; 'vals; 'R}>>, (unfold_eval_mpoly thenC tailC);
	<<eval_mpoly{nil; 'vals; 'R}>>, (unfold_eval_mpoly thenC tailC);
	<<add_mpoly{nil; 'q}>>, (reduce_add_mpolyNil thenC tailC);
	<<add_mpoly{cons{'m; 'p}; 'q}>>, (reduce_add_mpolyCons thenC tailC);
	<<mul_monom{('k1,'f1); ('k2,'f2); 'R}>>, (reduce_mul_monom thenC tailC);
	<<mul_monom_mpoly{('k,'f); cons{'h;'t}; 'R}>>, (unfold_mul_monom_mpoly thenC tailC);
	<<mul_monom_mpoly{('k,'f); nil; 'R}>>, (unfold_mul_monom_mpoly thenC tailC);
	<<mul_mpoly{cons{'h;'t}; 'q; 'R}>>, (unfold_mul_mpoly thenC tailC);
	<<mul_mpoly{nil; 'q; 'R}>>, (unfold_mul_mpoly thenC tailC);

	<<id_mpoly{number[i:n]; 'R; number[n:n]}>>, (unfold_id_mpoly thenC mpoly_evalC);
	<<zero_mpoly>>, (unfold_zero_mpoly thenC mpoly_evalC);

	<<add_monom{('k1,'f1); ('k2,'f2); 'R}>>, (reduce_add_monom thenC tailC);
	<<cmp_lexi{('k1,'f1); ('k2,'f2); 'cmp; 'eq}>>, (reduce_cmp_lexi thenC tailC);
	<<eq_monom{('k1,'f1); ('k2,'f2)}>>, (reduce_eq_monom thenC tailC);
	<<inject{('k,'f); 'p; 'R; number[i:n]}>>, (unfold_inject thenC tailC);
	<<standardize{cons{'h;'t}; 'R; number[i:n]}>>, (unfold_standardize thenC tailC);
	<<standardize{nil; 'R; number[i:n]}>>, (unfold_standardize thenC tailC);

	<<eval_mpolyTerm{addTerm{'l;'r}; 'vals; 'R}>>, (reduce_eval_mpolyTermAdd thenC tailC);
	<<eval_mpolyTerm{mulTerm{'l;'r}; 'vals; 'R}>>, (reduce_eval_mpolyTermMul thenC tailC);
	<<eval_mpolyTerm{constTerm{'c}; 'vals; 'R}>>, (reduce_eval_mpolyTermConst thenC tailC);
	<<eval_mpolyTerm{varTerm{number[i:n]}; 'vals; 'R}>>, (reduce_eval_mpolyTermVar thenC tailC);

	<<mpoly_ofTerm{addTerm{'l;'r}; 'R; number[n:n]}>>, (reduce_mpoly_ofTermAdd thenC tailC);
	<<mpoly_ofTerm{mulTerm{'l;'r}; 'R; number[n:n]}>>, (reduce_mpoly_ofTermMul thenC tailC);
	<<mpoly_ofTerm{constTerm{'c}; 'R; number[n:n]}>>, (reduce_mpoly_ofTermConst thenC tailC);
	<<mpoly_ofTerm{varTerm{number[i:n]}; 'R; number[n:n]}>>, (reduce_mpoly_ofTermVar thenC tailC);
(**)
	<<field[t:t]{Z}>>, ((addrC [0] unfold_Z) thenC reduceC);
	<<'a +[Z] 'b>>, ((addrC [0;0;0] unfold_Z) thenC (addrC [0;0] reduceC) thenC tailC);
	<<'a *[Z] 'b>>, ((addrC [0;0;0] unfold_Z) thenC (addrC [0;0] reduceC) thenC tailC);
]

let resource mpoly_eval += [
	<<'f 'arg>>, (reduceTopC thenC tailC);
	<<length{cons{'h;'t}}>>, (reduceTopC thenC mpoly_evalC);
	<<length{nil}>>, reduceC;
	<<if 'c then 'o1 else 'o2>>, (reduceTopC thenC tailC);
	<<list_ind{'l;'b;h,t,f.'step['h;'t;'f]}>>, (reduceTopC thenC tailC);
	<<ind{'n;'b;i,f.'step['i;'f]}>>, (reduceTopC thenC tailC);
	<<ind{'n;i,f.'down['i;'f];'b;i,f.'step['i;'f]}>>, (reduceTopC thenC tailC);
	<<field[t:t]{'F}>>, (reduceTopC thenC tailC);
	<<number[i:n] +@ number[j:n]>>, reduceC;
	<<number[i:n] -@ number[j:n]>>, reduceC;
	<<number[i:n] *@ number[j:n]>>, reduceC;
	<<number[i:n] =@ number[j:n]>>, reduceC;
	<<number[i:n] <@ number[j:n]>>, reduceC;
	<<natpower{'g; 'a; 'n}>>, (reduceTopC thenC tailC);
	<<nth{cons{'h;'t}; number[n:n]}>>, (reduceTopC thenC tailC);
]

type var_set = term list

let empty _ = []

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

let rec vars_of_term info f t =
	match explode_term t with
		<<'a 'b>> ->
			(match explode_term a with
				<<'c 'd>> ->
					let (f',fname) = dest_field c in
					(* if alpha_equal f f' *)
					if fname="*" then
						let info' = vars_of_term info f d in
						vars_of_term info' f b
					else if fname="+" then
						let info' = vars_of_term info f d in
						vars_of_term info' f b
					else
						add info t
			 | _ -> add info t
			)
	 | _ -> add info t

let var_list info = info

let mk_intnum_term i = Itt_int_base.mk_number_term (Lm_num.num_of_int i)

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

let id_mpoly_term = << id_mpoly{'i; 'F; 'n} >>
let id_mpoly_opname = opname_of_term id_mpoly_term
let is_id_mpoly_term = is_dep0_dep0_dep0_term id_mpoly_opname
let mk_id_mpoly_term = mk_dep0_dep0_dep0_term id_mpoly_opname
let dest_id_mpoly = dest_dep0_dep0_dep0_term id_mpoly_opname

let const_mpoly_term = << const_mpoly{'v; 'n} >>
let const_mpoly_opname = opname_of_term const_mpoly_term
let is_const_mpoly_term = is_dep0_dep0_term const_mpoly_opname
let mk_const_mpoly_term = mk_dep0_dep0_term const_mpoly_opname
let dest_const_mpoly = dest_dep0_dep0_term const_mpoly_opname

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
		assertT (mk_equal_term f_car h h) thenAT
		(rw (addrC [0] mpoly_evalC) 0) thenMT
		proveVarTypesT f_car t

let assertEqT f f_car vars varlist t =
	let t' = mk_eval_mpolyTerm_term (term2mpolyTerm f vars t) varlist f in
	let eqt = mk_equal_term f_car t t' in
	assertT eqt

let standardizeT ft f f_car vars varlist t =
	(assertEqT f f_car vars varlist t thenAT rw mpoly_evalC 0) thenMT
	rw (addrC [2] mpolyTerm2mpoly) (-1) thenMT
	eval_standardizeElim (-1) ft thenMT
	rw (addrC [2] mpoly_evalC) (-1)

let stdT ft f vars i = funT (fun p ->
	let t = if i=0 then Sequent.concl p else Sequent.nth_hyp p i in
	let f_car = mk_field_term f "car" in
	let varlist = mk_list_of_list vars in
	match explode_term t with
		<<'a='b in 'T>> ->
			proveVarTypesT f_car vars thenMT
			standardizeT ft f f_car vars varlist a thenMT
			hypSubstT (-1) i
	 | _ -> failT
)

interactive test4 :
	sequent { <H> >-
		eval_mpoly{id_mpoly{1; Z; 3}; cons{2;cons{3;cons{4;nil}}}; Z}=3 in int }

interactive test5 :
	sequent { <H> >- eval_mpoly{id_mpoly{0; Z; 3}; cons{2;cons{3;cons{4;nil}}}; Z}=2 in int }

interactive test6 :
	sequent { <H> >- eval_mpoly{id_mpoly{3; Z; 3}; cons{2;cons{3;cons{4;nil}}}; Z}=1 in int }

interactive test7 :
	sequent { <H> >- eval_mpoly{id_mpoly{2; Z; 3}; cons{2;cons{3;cons{4;nil}}}; Z}=4 in int }

interactive test8 :
	sequent { <H> >- 'x in int } -->
	sequent { <H> >- 'y in int } -->
	sequent { <H> >-
		eval_mpoly{
			add_mpoly{id_mpoly{0; Z; 2};
				add_mpoly{const_mpoly{1; 2};id_mpoly{1; Z; 2}}};
			cons{'x;
				cons{'y; nil}};
			Z}
		= 1 +@ 'x +@ 'y in int }

interactive test9 :
	sequent { <H> >-
		eval_mpoly{
			id_mpoly{0;Z;2};
			cons{2;cons{3;nil}};Z}
		= 2 in int }

interactive test11 :
	sequent { <H> >- 'x in int } -->
	sequent { <H> >- 'y in int } -->
	sequent { <H> >-
		eval_mpoly{
			add_mpoly{id_mpoly{0;Z;2};
				add_mpoly{mul_mpoly{id_mpoly{0;Z;2};id_mpoly{1;Z;2};Z};
					add_mpoly{id_mpoly{1;Z;2};const_mpoly{1;2}}}};
			cons{'x; cons{'y; nil}}; Z}
		='x +@ ('x *@ 'y) +@ 'y +@ 1 in int }

interactive test12 :
	sequent { <H> >- 'x in int } -->
	sequent { <H> >- 'y in int } -->
	sequent { <H> >-
		eval_mpoly{
			standardize{
				add_mpoly{id_mpoly{0;Z;2};
					add_mpoly{mul_mpoly{id_mpoly{0;Z;2};id_mpoly{1;Z;2};Z};
						add_mpoly{id_mpoly{1;Z;2};const_mpoly{1;2}}}};
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
	sequent { <H> >- 'x in int } -->
	sequent { <H> >- 'y in int } -->
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
	sequent { <H> >- 'x in int } -->
	sequent { <H> >- 'y in int } -->
	sequent { <H> >-
		'x +[Z] ('x *[Z] 'y) +[Z] 'y +[Z] 1
		= 1 +@ ('y +@ ('x +@ ('x *@ 'y))) in Z^car }
