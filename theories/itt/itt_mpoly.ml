extends Itt_ring_uce
extends Itt_bisect
extends Itt_poly
extends Itt_list2

open Lm_symbol
open Refiner.Refiner.Term
open Refiner.Refiner.TermSubst
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermOp
open Tactic_type.Conversionals
open Top_conversionals
open Dtactic
open Itt_rfun
open Itt_record
open Itt_list
open Itt_poly

(*
define unfold_isMonoidC1 : isMonoidC{'f} <-->
   isMonoid{'f} & isCommutative{'f}

define unfold_monoidC1 : monoidC[i:l] <-->
   {f: premonoid[i:l] | isMonoidC{'f}}

define unfold_monom : monom[i:l,rel:t] <--> monoidC[i:l] isect unstrictTotalOrder[i:l,rel:t]

define unfold_ring_ext : ring_ext{'r;'m} <-->
   {car=(fset{unstrict2eq{'m^eq}; 'm^car} -> 'r);
	"*"=lambda{x. lambda{y. 'x *@ 'y}}; "+"=lambda{x. lambda{y. 'x +@ 'y}}; "0"=0; neg=lambda{x. (-'x)}}
*)

define unfold_const_poly : const_poly{'a; 'F} <-->
	(0,lambda{i.'a})

define unfold_raw_add_poly : raw_add_poly{'p; 'q; 'F} <-->
   (max{fst{'p}; fst{'q}}, lambda{x. coeff{'p;'x;'F} +['F] coeff{'q;'x;'F}})

define unfold_raw_mul_poly : raw_mul_poly{'p; 'q; 'F} <-->
   (fst{'p} +@ fst{'q}, lambda{x. sum{0; 'x; y. (coeff{'p;'y;'F} *['F] coeff{'q;('x-@'y);'F}); 'F}})

define unfold_Poly : Poly{'F} <-->
{
	car=poly{'F};
	ext_of='F;
	"+"=lambda{x.lambda{y.raw_add_poly{'x;'y;'F}}};
	"*"=lambda{x.lambda{y.raw_mul_poly{'x;'y;'F}}};
	"0"=zero_poly{'F};
	"1"=unit_poly{'F};
	neg=lambda{x.neg_poly{'x;'F}};
	eq=lambda{x.lambda{y.eq_poly{'x;'y;'F}}}
}

let fold_Poly = makeFoldC <<Poly{'F}>> unfold_Poly

define unfold_mpoly : mpoly{'F;'nvars} <-->
   ind{'nvars; 'F; i,up.Poly{'up}}

define unfold_const_mpoly : const_mpoly{'v; 'F; 'nvars} <-->
	ind{'nvars; 'v; i,f.const_poly{'f; mpoly{'F; 'i -@ 1}}}

(*
	fix{f.
		lambda{l.lambda{p.
			list_ind{'l; 'p;
				h,t,fake.('f 't eval_poly{'p; 'h; mpoly{'F; length{'l}}})}}}}
	'vals 'poly
*)
(*	list_ind{'vals; 'poly; h,t,f.eval_poly{'f; 'h; mpoly{'F; length{'t}}}}*)
(*
define unfold_eval_mpoly : eval_mpoly_fun{'vals; 'F} <-->
	list_ind{'vals; lambda{x.'x};
		h,t,f.lambda{p.eval_poly{('f );'h;'F}}}
define unfold_eval_mpoly : eval_mpoly{'poly; 'vals; 'F} <-->
	(eval_mpoly_fun{'vals;'F} 'poly)
*)

declare eval_mpoly{'poly; 'vals; 'F}

prim_rw unfold_eval_mpoly : eval_mpoly{'poly; 'vals; 'F} <-->
	list_ind{
		'vals;
		'poly;
		h,t,f.eval_mpoly{
			eval_poly{
				'poly;
				const_mpoly{'h; 'F; length{'t}};
				mpoly{'F; length{'t}}};
			't;
			'F}}

interactive eval_mpoly_wf :
	[wf] sequent { <H> >- 'vals in list{'F} } -->
	[wf] sequent { <H> >- 'p in mpoly{'F; length{'vals}} }	-->
	sequent { <H> >- eval_mpoly{'p; 'vals; 'F} in 'F }

(*
interactive
	sequent { <H> >- 'vals in list{'F}	-->
	sequent { <H> >- 'p in mpoly{'F; length{'vals}} }	-->
	sequent { <H> >- 'a=eval_mpoly{'p; 'vals; 'F} in 'F } -->
	sequent { <H> >- 'a in 'F }
*)

(*
interactive
	sequent { >- 'p in mpoly{'F; 'n} }	-->
	sequent { >- 'vals in list{'F} }	-->
	sequent { >- length{'vals}='n in int } -->
	sequent { >- 'a in 'F } -->
	sequent { >- 'b in 'F }	-->
	sequent { >- 'a=eval_mpoly{'p; 'vals; 'F} in 'F } -->
	sequent { >- 'b=eval_mpoly{'p; 'vals; 'F} in 'F } -->
	sequent { >- 'a='b in 'F }
*)

interactive eval_add_distrib {| intro [intro_typeinf <<'F>>] |} unitringCE[i:l] :
	[wf] sequent { <H> >- 'vals in list{'F} }	-->
   [wf] sequent { <H> >- 'p in mpoly{'F; length{'vals}} } -->
   [wf] sequent { <H> >- 'q in mpoly{'F; length{'vals}} } -->
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   sequent { <H> >- eval_mpoly{'p; 'vals; 'F} +['F] eval_mpoly{'q; 'vals; 'F} = eval_mpoly{'p +[mpoly{'F; length{'vals}}] 'q; 'vals; 'F} in 'F^car }

interactive eval_mul_distrib {| intro [intro_typeinf <<'F>>] |} unitringCE[i:l] :
	[wf] sequent { <H> >- 'vals in list{'F} }	-->
   [wf] sequent { <H> >- 'p in mpoly{'F; length{'vals}} } -->
   [wf] sequent { <H> >- 'q in mpoly{'F; length{'vals}} } -->
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   sequent { <H> >- eval_mpoly{'p; 'vals; 'F} *['F] eval_mpoly{'q; 'vals; 'F} = eval_mpoly{'p *[mpoly{'F; length{'vals}}] 'q; 'vals; 'F} in 'F^car }

define unfold_id_poly : id_poly{'F} <-->
   (1, lambda{i. if 'i=@0 then 'F^"0" else 'F^"1"})

define unfold_id_mpoly : id_mpoly{'F; 'nvars; 'i} <-->
	ind{'nvars; 'F^"1";
		j,up.if 'j >@ 'i then const_poly{'up; mpoly{'F; 'j -@ 1}}
			  else if 'j =@ 'i then id_poly{mpoly{'F; 'j -@ 1}}
			  else zero_poly{mpoly{'F; 'j -@ 1}}
		}

interactive as_id_poly {| intro [intro_typeinf <<'F>>] |} unitringCE[i:l] :
	[wf] sequent { <H> >- 'x in 'F^car } -->
	[wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
	sequent { <H> >- 'x = eval_poly{id_poly{'F}; cons{'x;nil}; 'F} in 'F^car }

let add info t =
	if List.exists (alpha_equal t) info then info
	else t::info

let find info t =
	List.find (alpha_equal t) info

let find_index info t = Lm_list_util.find_item (alpha_equal t) info

(*
let is_bin_op op f t =
	match explode_term t with
		<<'a 'b>> ->
			(match explode_term a with
				<<'c 'd>> ->
					let (f',fname) = dest_field c in
					fname=op (* && alpha_equal f f' *)
			 | _ -> false
			)
	 | _ -> false

let is_mul f t = is_bin_op "*" f t
let is_add f t = is_bin_op "+" f t

let dest_bin_op f t =
	let a,b = dest_apply t in
	let c,d = dest_apply a in
	d,b

let dest_mul f t = dest_bin_op f t
let dest_add f t = dest_bin_op f t
*)

let rec vars_of_term_aux info f t =
	match explode_term t with
		<<'a 'b>> ->
			(match explode_term a with
				<<'c 'd>> ->
					let (f',fname) = dest_field c in
					(* if alpha_equal f f' *)
					if fname="*" then
						let info' = vars_of_term_aux info f d in
						vars_of_term_aux info' f b
					else if fname="+" then
						let info' = vars_of_term_aux info f d in
						vars_of_term_aux info' f b
					else
						add info t
			 | _ -> add info t
			)
	 | _ -> add info t

let vars_of_term = vars_of_term_aux []

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

let id_mpoly_term = << id_mpoly{'F; 'nvars; 'i} >>
let id_mpoly_opname = opname_of_term id_mpoly_term
let is_id_mpoly_term = is_dep0_dep0_dep0_term id_mpoly_opname
let mk_id_mpoly_term = mk_dep0_dep0_dep0_term id_mpoly_opname
let dest_id_mpoly = dest_dep0_dep0_dep0_term id_mpoly_opname

let var2mpoly f nvars vars v =
	let i = find_index vars v in
	let idp = mk_id_mpoly_term f (mk_intnum_term nvars) (mk_intnum_term i) in
	mk_eval_mpoly_term idp (mk_list_of_list vars) f

let rec term2mpoly_aux f nvars vars t =
	match explode_term t with
		<<'a 'b>> ->
			(match explode_term a with
				<<'c 'd>> ->
					let (f',fname) = dest_field c in
					(* if alpha_equal f f' *)
					if fname="*" then
						mk_apply_term (mk_apply_term (mk_field_term f "*") (term2mpoly_aux f nvars vars d)) (term2mpoly_aux f nvars vars b)
					else if fname="+" then
						mk_apply_term (mk_apply_term (mk_field_term f "+") (term2mpoly_aux f nvars vars d)) (term2mpoly_aux f nvars vars b)
					else
						var2mpoly f nvars vars t
			 | _ -> var2mpoly f nvars vars t
			)
	 | _ -> var2mpoly f nvars vars t

let term2mpoly f t =
	let vars = vars_of_term f t in
	let nvars = List.length vars in
	term2mpoly_aux f nvars vars t

(*
let stdT f t =
	let t' = term2mpoly f t in
	let eqt = mk_eq_term f t t'
	assertT
*)

(*EXAMPLE*)
define unfold_poly_of_list : poly_of_list{'l} <-->
	((length{'l} -@ 1), lambda{n. if 'n<@length{'l} then nth{'l; 'n} else it})

define unfold_Zuce : Zuce <-->
   {
		car=int;
		"*"=lambda{x. lambda{y. 'x *@ 'y}};
		"+"=lambda{x. lambda{y. 'x +@ 'y}};
		"0"=0;
		neg=lambda{x. (-'x)};
		eq=lambda{x.lambda{y.beq_int{'x;'y}}};
		"1"=1
	}

let fold_Zuce = makeFoldC <<Zuce>> unfold_Zuce

let atIndAuxC c t =
	if Itt_nat.is_ind_term t then
		c
	else
		failC

let atIndC c = termC (atIndAuxC c)
let atIndArgC c = atIndC (addrC [0] c)

let atTermAuxC c t1 t2 =
	let op1=opname_of_term t1 in
	let op2=opname_of_term t2 in
	if Opname.eq op1 op2 then
		c
	else
		failC

let atTermC t c = termC (atTermAuxC c t)
let atTermHC t c = atTermC t (higherC c)

let resource reduce += [
	<<field[t:t]{Poly{'F}}>>, (someSubC unfold_Poly);
	<<mpoly{'F; number[i:n]}>>, unfold_mpoly;
	<<isZeroPoly{(number[i:n], lambda{i.'f['i]}); 'F}>>, unfold_isZeroPoly;
	<<coeff{(number[i:n], lambda{i.'f['i]}); number[j:n]; 'F}>>, unfold_coeff;
	<<isZero{'v; 'F}>>, unfold_isZero;
	<<const_mpoly{'v; 'F; number[i:n]}>>, unfold_const_mpoly;
	<<normalize{(number[i:n], lambda{i.'f['i]}); 'F}>>, unfold_normalize1;

	<<sum{number[i:n]; number[j:n]; x.'P['x]; 'F}>>, unfold_sum;
	(*<<ind{'n; 'base; i,f.'up['i;'f]}>>, ((addrC [0] reduceC) thenC reduceTopC);*)
(**)
	<<eval_mpoly{(number[i:n], lambda{i.'f['i]}); cons{'h;'t}; 'F}>>, unfold_eval_mpoly;
	<<eval_mpoly{'p; nil; 'F}>>, unfold_eval_mpoly;
	<<eval_poly{(number[i:n], lambda{i.'f['i]}); 'a; 'F}>>, unfold_eval_poly;
	<<raw_add_poly{(number[i:n], lambda{i.'f['i]});(number[j:n],lambda{i.'g['i]});'F}>>, unfold_raw_add_poly;
	<<raw_mul_poly{(number[i:n], lambda{i.'f['i]});(number[j:n],lambda{i.'g['i]});'F}>>, unfold_raw_mul_poly;
	<<id_mpoly{'F; number[i:n]; number[j:n]}>>, unfold_id_mpoly;
	<<const_poly{'a;'F}>>, unfold_const_poly;
	<<unit_poly{'F}>>, unfold_unit_poly;
	<<zero_poly{'F}>>, unfold_zero_poly;
	<<id_poly{'F}>>, unfold_id_poly;
(**)
	<<field[t:t]{Zuce}>>, (someSubC unfold_Zuce);
]

dform id_poly_df : except_mode[src] :: id_poly{'F} =
	`"id_poly{" slot{'F} `"}"

dform poly_ring_uce_df : except_mode[src] :: Poly{'F} =
	`"Poly" sub{'F}

dform mpoly_ring_uce_df : except_mode[src] :: mpoly{'F; 'nvars} =
	`"mpoly" sub{'F} `"[" slot{'nvars} `"]"

dform raw_add_poly_df : except_mode[src] :: raw_add_poly{'p;'q;'F} =
	slot{'p} `" +_Poly{" slot{'F} `"} " slot{'q}

dform raw_mul_poly_df : except_mode[src] :: raw_mul_poly{'p;'q;'F} =
	slot{'p} `" *_Poly{" slot{'F} `"} " slot{'q}

dform eval_mpoly_df : except_mode[src] :: eval_mpoly{'p;'vals;'F} =
	slot{'p} `"_" slot{'F} `"(" slot{'vals} `")"

dform eval_id_mpoly_df : except_mode[src] :: id_mpoly{'F;'nvars;'i} =
	slot{'F} `"[" slot{'nvars} `"]_x" slot{'i}

dform int_ring_uce_df : except_mode[src] :: Zuce = mathbbZ

dform const_poly : const_poly{'a;'F} = `"const_poly{" slot{'a} `";" slot{'F} `"}"

interactive test1 :
	sequent { <H> >- poly_of_list{cons{1;cons{2;nil}}} in poly{Zuce} }

interactive test2 :
	sequent { <H> >- eval_poly{poly_of_list{cons{1;cons{2;nil}}}; 2; Zuce}=5 in int }

interactive test3 :
	sequent { <H> >- id_mpoly{Zuce; 3; 2} in mpoly{Zuce; 3}^car }

interactive test4 :
	sequent { <H> >-
		eval_mpoly{id_mpoly{Zuce; 3; 2}; cons{2;cons{3;cons{4;nil}}}; Zuce}=3 in int }

interactive test5 :
	sequent { <H> >- eval_mpoly{id_mpoly{Zuce; 3; 0}; cons{2;cons{3;cons{4;nil}}}; Zuce}=1 in int }

interactive test6 :
	sequent { <H> >- eval_mpoly{id_mpoly{Zuce; 3; 4}; cons{2;cons{3;cons{4;nil}}}; Zuce}=0 in int }

interactive test7 :
	sequent { <H> >- eval_mpoly{id_mpoly{Zuce; 3; 3}; cons{2;cons{3;cons{4;nil}}}; Zuce}=2 in int }

interactive test8 :
	sequent { <H> >- 'x in int } -->
	sequent { <H> >- 'y in int } -->
	sequent { <H> >-
		eval_poly{
			eval_poly{
				raw_add_poly{
					const_poly{
						raw_add_poly{
							unit_poly{Zuce};
							id_poly{Zuce};Zuce};Poly{Zuce}};
					id_poly{Poly{Zuce}}; Poly{Zuce}};
				const_poly{'x;Poly{Zuce}};Poly{Zuce}};
			'y; Zuce}
		= 1 +@ 'x +@ 'y in int }

interactive test9 :
	sequent { <H> >-
		eval_mpoly{
			id_mpoly{Zuce;2;2};
			cons{2;cons{3;nil}};Zuce}
		= 2 in int }
