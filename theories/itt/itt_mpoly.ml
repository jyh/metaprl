extends Itt_bisect
extends Itt_poly
extends Itt_list2
extends Itt_ring_uce

open Lm_printf
open Base_tactics
open Itt_equal
open Itt_struct
open Itt_rfun
open Itt_record
open Itt_list
open Itt_poly
open Itt_ring2

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

interactive eval_mpoly_wf {| intro [] |} :
	[wf] sequent { <H> >- 'vals in list{'F^car} } -->
	[wf] sequent { <H> >- 'p in mpoly{'F; length{'vals}}^car }	-->
	sequent { <H> >- eval_mpoly{'p; 'vals; 'F} in 'F^car }

interactive mpoly_wf {| intro [intro_typeinf <<'F>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'nvars in nat } -->
	sequent { <H> >- mpoly{'F; 'nvars} in unitringCE[i:l] }

interactive add_in_car {| intro [AutoMustComplete; intro_typeinf <<'F>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in mpoly{'F; 'nvars}^car } -->
   [wf] sequent { <H> >- 'b in mpoly{'F; 'nvars}^car } -->
   sequent { <H> >- 'a +[mpoly{'F; 'nvars}] 'b in mpoly{'F; 'nvars}^car }

interactive mul_in_car {| intro [AutoMustComplete; intro_typeinf <<'F>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'a in mpoly{'F; 'nvars}^car } -->
   [wf] sequent { <H> >- 'b in mpoly{'F; 'nvars}^car } -->
   sequent { <H> >- 'a *[mpoly{'F; 'nvars}] 'b in mpoly{'F; 'nvars}^car }

(*
interactive
	sequent { <H> >- 'vals in list{'F^car}	-->
	sequent { <H> >- 'p in mpoly{'F; length{'vals}}^car }	-->
	sequent { <H> >- 'a=eval_mpoly{'p; 'vals; 'F} in 'F^car } -->
	sequent { <H> >- 'a in 'F^car }
*)

(*
interactive
	sequent { >- 'p in mpoly{'F; 'n}^car }	-->
	sequent { >- 'vals in list{'F^car} }	-->
	sequent { >- length{'vals}='n in int } -->
	sequent { >- 'a in 'F^car } -->
	sequent { >- 'b in 'F^car }	-->
	sequent { >- 'a=eval_mpoly{'p; 'vals; 'F} in 'F^car } -->
	sequent { >- 'b=eval_mpoly{'p; 'vals; 'F} in 'F^car } -->
	sequent { >- 'a='b in 'F^car }
*)

interactive eval_add_distrib {| intro [intro_typeinf <<'F>>] |} unitringCE[i:l] :
	[wf] sequent { <H> >- 'vals in list{'F^car} }	-->
   [wf] sequent { <H> >- 'p in mpoly{'F; length{'vals}}^car } -->
   [wf] sequent { <H> >- 'q in mpoly{'F; length{'vals}}^car } -->
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   sequent { <H> >- eval_mpoly{'p; 'vals; 'F} +['F] eval_mpoly{'q; 'vals; 'F} = eval_mpoly{'p +[mpoly{'F; length{'vals}}] 'q; 'vals; 'F} in 'F^car }

interactive eval_mul_distrib {| intro [intro_typeinf <<'F>>] |} unitringCE[i:l] :
	[wf] sequent { <H> >- 'vals in list{'F^car} }	-->
   [wf] sequent { <H> >- 'p in mpoly{'F; length{'vals}}^car } -->
   [wf] sequent { <H> >- 'q in mpoly{'F; length{'vals}}^car } -->
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   sequent { <H> >- eval_mpoly{'p; 'vals; 'F} *['F] eval_mpoly{'q; 'vals; 'F} = eval_mpoly{'p *[mpoly{'F; length{'vals}}] 'q; 'vals; 'F} in 'F^car }

interactive eval_add_distribElim unitringCE[i:l] 'F 'vals 'p 'q :
	[wf] sequent { <H> >- 'vals in list{'F^car} }	-->
   [wf] sequent { <H> >- 'p in mpoly{'F; length{'vals}}^car } -->
   [wf] sequent { <H> >- 'q in mpoly{'F; length{'vals}}^car } -->
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   sequent { <H>; (eval_mpoly{'p; 'vals; 'F} +['F] eval_mpoly{'q; 'vals; 'F} = eval_mpoly{'p +[mpoly{'F; length{'vals}}] 'q; 'vals; 'F} in 'F^car) >- 'C } -->
	sequent { <H> >- 'C }

interactive eval_mul_distribElim unitringCE[i:l] 'F 'vals 'p 'q :
	[wf] sequent { <H> >- 'vals in list{'F^car} }	-->
   [wf] sequent { <H> >- 'p in mpoly{'F; length{'vals}}^car } -->
   [wf] sequent { <H> >- 'q in mpoly{'F; length{'vals}}^car } -->
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   sequent { <H>; (eval_mpoly{'p; 'vals; 'F} *['F] eval_mpoly{'q; 'vals; 'F} = eval_mpoly{'p *[mpoly{'F; length{'vals}}] 'q; 'vals; 'F} in 'F^car) >- 'C } -->
	sequent { <H> >- 'C }

define unfold_id_poly : id_poly{'F} <-->
   (1, lambda{i. if 'i=@0 then 'F^"0" else 'F^"1"})

define unfold_id_mpoly : id_mpoly{'F; 'nvars; 'i} <-->
	ind{'nvars; 'F^"1";
		j,up.if 'j >@ 'i then const_poly{'up; mpoly{'F; 'j -@ 1}}
			  else if 'j =@ 'i then id_poly{mpoly{'F; 'j -@ 1}}
			  else zero_poly{mpoly{'F; 'j -@ 1}}
		}

interactive id_mpoly_wf {| intro [intro_typeinf <<'F>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'nvars in nat } -->
   [wf] sequent { <H> >- 'k in nat } -->
	sequent { <H> >- id_mpoly{'F; 'nvars; 'k} in mpoly{'F; 'nvars}^car }

interactive const_mpoly_wf {| intro [intro_typeinf <<'F>>] |} unitringCE[i:l] :
   [wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
   [wf] sequent { <H> >- 'nvars in nat } -->
   [wf] sequent { <H> >- 'v in 'F^car } -->
	sequent { <H> >- const_mpoly{'v; 'F; 'nvars} in mpoly{'F; 'nvars}^car }

interactive as_id_poly {| intro [intro_typeinf <<'F>>] |} unitringCE[i:l] :
	[wf] sequent { <H> >- 'x in 'F^car } -->
	[wf] sequent { <H> >- 'F in unitringCE[i:l] } -->
	sequent { <H> >- 'x = eval_poly{id_poly{'F}; cons{'x;nil}; 'F} in 'F^car }

interactive length_nat {| intro [intro_typeinf <<'l>>] |} list{'T} :
	sequent { <H> >- 'l in list{'T} } -->
	sequent { <H> >- length{'l} in nat }

let add info t =
	if List.exists (alpha_equal t) info then info
	else t::info

let find info t =
	List.find (alpha_equal t) info

let rec find_item_aux f i = function
   h::t ->
      if f h then
         Some i
      else
         find_item_aux f (i + 1) t
 | [] ->
      None

let find_index info t = find_item_aux (alpha_equal t) 0 info

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

let const_mpoly_term = << const_mpoly{'v; 'F; 'nvars} >>
let const_mpoly_opname = opname_of_term const_mpoly_term
let is_const_mpoly_term = is_dep0_dep0_dep0_term const_mpoly_opname
let mk_const_mpoly_term = mk_dep0_dep0_dep0_term const_mpoly_opname
let dest_const_mpoly = dest_dep0_dep0_dep0_term const_mpoly_opname

let var2mpoly f nvars vars v =
	let lst = mk_list_of_list vars in
	let len = Itt_list2.mk_length_term lst in
	match find_index vars v with
		Some i ->
			let idp = mk_id_mpoly_term f len (mk_intnum_term (nvars-i)) in
			mk_eval_mpoly_term idp lst f
	 | None ->
			let constp = mk_const_mpoly_term v f len in
			mk_eval_mpoly_term constp lst f

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

let term2mpoly f vars t =
	(*let vars = vars_of_term f t in*)
	let nvars = List.length vars in
	term2mpoly_aux f nvars vars t

let rec proveVarTypesT f_car = function
	[] -> idT
 | h::t ->
		assertT (mk_equal_term f_car h h) thenMT
		(rw (addrC [0] reduceC) (-1)) thenMT
		proveVarTypesT f_car t

let stdT f vars i = funT (fun p ->
	let t = if i=0 then Sequent.concl p else Sequent.nth_hyp p i in
	let f_car = mk_field_term f "car" in
	match explode_term t with
		<<'a='b in 'T>> ->
			let a' = term2mpoly f vars a in
			let eqt = mk_equal_term f_car a a' in
			proveVarTypesT f_car vars thenMT assertT eqt
	 | _ -> failT
)

type subterms = Eval of term | Mul of term * term | Add of term * term

let rec lowerOp f t =
	match explode_term t with
		<<eval_mpoly{'p; 'vals; 'field}>> when alpha_equal f field -> Eval p
	 | <<apply{'a;'b}>> ->
			(match explode_term a with
				<<'c 'd>> ->
					let (f',fname) = dest_field c in
					(* if alpha_equal f f' *)
					let l = lowerOp f d in
						(match l with
							Eval t1 ->
								let r = lowerOp f b in
								(match r with
									Eval t2 ->
										(match fname with
											"*" -> Mul (t1,t2)
										 | "+" -> Add (t1,t2)
										 | _ -> raise (RefineError ("Itt_mpoly.lowerOp", StringTermError ("unknown field name", c)))
										)
								 | _ -> r
								)
						 | _ -> l
						)
			 | _ -> raise (RefineError ("Itt_mpoly.lowerOp", StringTermError ("unknown operation", a)))
			)
	 | <<'p='q in 'T>> ->
			lowerOp f q
	 | _ -> raise (RefineError ("Itt_mpoly.lowerOp", StringTermError ("unknown operation", t)))

let stepT ftype f vals i = funT (fun p ->
	let t = if i=0 then Sequent.concl p else Sequent.nth_hyp p i in
	match lowerOp f t with
		Mul (l,r) ->
			eval_mul_distribElim ftype f vals l r thenMT hypSubstT (-1) i thenMT thinT (-1)
	 | Add (l,r) ->
			eval_add_distribElim ftype f vals l r thenMT hypSubstT (-1) i thenMT thinT (-1)
	 | Eval _ -> failT
)

let convT ft f vals i =
	let vterm = mk_list_of_list vals in
	repeatMT (stepT ft f vterm i)

(*
define unfoldPolyTermAux : PolyTermAux{'t; 'n; 'vars; 'F} <-->
	ind{'n;
		exists_list{'vars; x.('t='x in 'F^car)};
		i,f.('f or
			(x:'F^car * (y:'F^car * (PolyTermAux{'x;'i -@ 1;'vars;'F} and
				PolyTermAux{'y;'i -@ 1;'vars;'F} and
					(('t=('x 'F^"*" 'y) in 'F^car) or ('t=('x 'F^"+" 'y) in 'F^car))))))}

define unfoldPolyTerm : PolyTerm{'t; 'vars; 'F} <-->
	n:nat * PolyTerm{'t; 'n; 'vars; 'F}
*)

(*EXAMPLE*)
define unfold_poly_of_list : poly_of_list{'l} <-->
	((length{'l} -@ 1), lambda{n. if 'n<@length{'l} then nth{'l; 'n} else it})

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
	<<field[t:t]{Poly{'F}}>>, ((addrC [0] unfold_Poly) thenC reduceC);
	<<mpoly{'F; number[i:n]}>>, unfold_mpoly;
	<<isZeroPoly{(number[i:n], lambda{i.'f['i]}); 'F}>>, (unfold_isZeroPoly thenC reduceC);
	<<coeff{(number[i:n], lambda{i.'f['i]}); number[j:n]; 'F}>>, (unfold_coeff  thenC reduceC);
	<<coeff{(number[i:n], lambda{j.'f}); 'k; 'F}>>, (unfold_coeff thenC reduceC);
(*	<<coeff{(number[i:n], lambda{i.'f}); 'i; 'F}>>, unfold_coeff;*)
	<<isZero{'v; 'F}>>, (unfold_isZero thenC reduceC);
	<<const_mpoly{'v; 'F; number[i:n]}>>, (unfold_const_mpoly thenC reduceC);
	<<normalize{(number[i:n], lambda{i.'f['i]}); 'F}>>, unfold_normalize1;

	<<sum{number[i:n]; number[j:n]; x.'P['x]; 'F}>>, (unfold_sum thenC reduceC);
	(*<<ind{'n; 'base; i,f.'up['i;'f]}>>, ((addrC [0] reduceC) thenC reduceTopC);*)
(**)
	<<eval_mpoly{(number[i:n], lambda{i.'f['i]}); cons{'h;'t}; 'F}>>, unfold_eval_mpoly;
	<<eval_mpoly{'p; nil; 'F}>>, (unfold_eval_mpoly thenC reduceC);
	<<eval_poly{(number[i:n], lambda{i.'f['i]}); 'a; 'F}>>, unfold_eval_poly;
	<<raw_add_poly{(number[i:n], lambda{i.'f['i]});(number[j:n],lambda{i.'g['i]});'F}>>, (unfold_raw_add_poly thenC reduceC);
	<<raw_mul_poly{(number[i:n], lambda{i.'f['i]});(number[j:n],lambda{i.'g['i]});'F}>>, (unfold_raw_mul_poly thenC reduceC);
	<<id_mpoly{'F; number[i:n]; number[j:n]}>>, (unfold_id_mpoly thenC reduceC);
	<<const_poly{'a;'F}>>, unfold_const_poly;
	<<unit_poly{'F}>>, unfold_unit_poly;
	<<zero_poly{'F}>>, unfold_zero_poly;
	<<id_poly{'F}>>, unfold_id_poly;
(**)
	<<field[t:t]{Z}>>, ((addrC [0] unfold_Z) thenC reduceTopC);
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

dform const_poly : const_poly{'a;'F} = `"const_poly{" slot{'a} `";" slot{'F} `"}"

interactive test1 :
	sequent { <H> >- poly_of_list{cons{1;cons{2;nil}}} in poly{Z} }

interactive test2 :
	sequent { <H> >- eval_poly{poly_of_list{cons{1;cons{2;nil}}}; 2; Z}=5 in int }

interactive test3 :
	sequent { <H> >- id_mpoly{Z; 3; 2} in mpoly{Z; 3}^car }

interactive test4 :
	sequent { <H> >-
		eval_mpoly{id_mpoly{Z; 3; 2}; cons{2;cons{3;cons{4;nil}}}; Z}=3 in int }

interactive test5 :
	sequent { <H> >- eval_mpoly{id_mpoly{Z; 3; 0}; cons{2;cons{3;cons{4;nil}}}; Z}=1 in int }

interactive test6 :
	sequent { <H> >- eval_mpoly{id_mpoly{Z; 3; 4}; cons{2;cons{3;cons{4;nil}}}; Z}=0 in int }

interactive test7 :
	sequent { <H> >- eval_mpoly{id_mpoly{Z; 3; 3}; cons{2;cons{3;cons{4;nil}}}; Z}=2 in int }

interactive test8 :
	sequent { <H> >- 'x in int } -->
	sequent { <H> >- 'y in int } -->
	sequent { <H> >-
		eval_poly{
			eval_poly{
				raw_add_poly{
					const_poly{
						raw_add_poly{
							unit_poly{Z};
							id_poly{Z};Z};Poly{Z}};
					id_poly{Poly{Z}}; Poly{Z}};
				const_poly{'x;Poly{Z}};Poly{Z}};
			'y; Z}
		= 1 +@ 'x +@ 'y in int }

interactive test9 :
	sequent { <H> >-
		eval_mpoly{
			id_mpoly{Z;2;2};
			cons{2;cons{3;nil}};Z}
		= 2 in int }

interactive test10 :
	sequent { <H> >- 'x in int } -->
	sequent { <H> >- 'y in int } -->
	sequent { <H> >- 'x +[Z] 'y +[Z] 1 in int }

interactive test11 :
	sequent { <H> >- 'x in int } -->
	sequent { <H> >- 'y in int } -->
	sequent { <H> >- 'x +[Z] ('x *[Z] 'y) +[Z] 'y +[Z] 1 in int }

interactive test12 :
	sequent { <H> >- 'x in Z^car } -->
	sequent { <H> >- 'y in Z^car } -->
	sequent { <H> >- ('x +[Z] ('x *[Z] 'y) +[Z] 'y +[Z] 1) in Z^car }
