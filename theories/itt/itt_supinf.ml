extends Itt_equal
extends Itt_rfun
extends Itt_logic
extends Itt_bool
extends Itt_int_ext
extends Itt_rat

open Printf
open Lm_debug
open Opname
open Term_sig
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.TermType
open Refiner.Refiner.RefineError

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Conversionals

open Dtactic

open Top_conversionals

open Itt_equal
open Itt_struct
open Itt_logic
open Itt_bool

open Itt_int_base
open Itt_int_ext
open Itt_int_arith
open Itt_rat

let _ = show_loading "Loading Itt_supinf%t"

let debug_supinf_trace =
   create_debug (**)
      { debug_name = "debug_supinf_trace";
        debug_description = "Print out (low-level) trace of supinf execution";
        debug_value = false
      }

let debug_supinf_steps =
   create_debug (**)
      { debug_name = "debug_supinf_steps";
        debug_description = "Print out (high-level) steps to be proved";
        debug_value = true
      }

module type BoundFieldSig =
sig
	type bfield

	val fieldUnit : bfield
	val fieldZero : bfield
	val plusInfinity : bfield
	val minusInfinity : bfield
	val mul : bfield -> bfield -> bfield
	val add : bfield -> bfield -> bfield
	val neg : bfield -> bfield
	val sub : bfield -> bfield -> bfield
	val inv : bfield -> bfield
	val div : bfield -> bfield -> bfield
	val compare : bfield -> bfield -> int
	val isInfinite : bfield -> bool

	val term_of : bfield -> term
	val mul_term : term -> term -> term
	val add_term : term -> term -> term
	val neg_term : term -> term
	val sub_term : term -> term -> term
	val inv_term : term -> term
	val div_term : term -> term -> term
	val ge_term : term -> term -> term
	val max_term : term -> term -> term
	val min_term : term -> term -> term

	val print : bfield -> unit
end

module RationalBoundField =
struct
	open Lm_num

	type bfield = Number of (num * num) | MinusInfinity | PlusInfinity

	let num0=num_of_int 0
	let num1=num_of_int 1
	let fieldUnit = Number (num1, num1)
	let fieldZero = Number (num0,num1)
	let plusInfinity=PlusInfinity
	let minusInfinity=MinusInfinity

	let isInfinite = function
		Number _ -> false
	 | _ -> true

	let mul a b =
		match a with
		 |	Number (a1,a2) ->
				begin
					match b with
						Number (b1,b2) -> Number(mult_num a1 b1, mult_num a2 b2)
					 | PlusInfinity ->
							if lt_num a1 num0 then MinusInfinity
							else b
					 | MinusInfinity ->
							if lt_num a1 num0 then PlusInfinity
							else b
				end
		 | _ -> raise (Invalid_argument "Multiplications by infinities are not defined")

	let add a b =
		match a,b with
			MinusInfinity, MinusInfinity -> a
		 | MinusInfinity, PlusInfinity -> raise (Invalid_argument "MinusInfinity+PlusInfinity is not supported")
		 | PlusInfinity, MinusInfinity -> raise (Invalid_argument "PlusInfinity+MinusInfinity is not supported")
		 | PlusInfinity, PlusInfinity -> a
		 | PlusInfinity, _ -> a
		 | _, PlusInfinity -> b
		 | MinusInfinity, _ -> a
		 | _, MinusInfinity -> b
		 | Number (a1,a2), Number (b1,b2) -> Number(add_num (mult_num a1 b2) (mult_num a2 b1), mult_num a2 b2)

	let sub a b =
		match a,b with
			Number (a1,a2), Number (b1,b2) -> Number(sub_num (mult_num a1 b2) (mult_num b1 a2), mult_num a2 b2)
		 | _,_ -> raise (Invalid_argument "Subtraction defined only on proper numbers")

	let neg a =
		match a with
			Number (a1,a2) -> Number(sub_num num0 a1,a2)
		 | PlusInfinity -> MinusInfinity
		 | MinusInfinity -> PlusInfinity

	let inv a =
		match a with
			Number (a1,a2) ->
				if eq_num a2 num0 then raise (Invalid_argument "Division by zero")
				else Number(a2,a1)
		 | _ -> raise (Invalid_argument "Division defined only on proper numbers")

	let div a b =
		match a,b with
			Number (a1,a2), Number (b1,b2) ->
				if eq_num b1 num0 then raise (Invalid_argument "Division by zero")
				else Number(mult_num a1 b2, mult_num a2 b1)
		 | _,_ -> raise (Invalid_argument "Division defined only on proper numbers")

	let compare a b =
		match a,b with
			MinusInfinity, MinusInfinity -> 0
		 | MinusInfinity, _ -> -1
		 | _, MinusInfinity -> 1
		 | PlusInfinity, PlusInfinity -> 0
		 | PlusInfinity, _ -> 1
		 | _, PlusInfinity -> -1
		 | Number (a1,a2), Number (b1,b2) -> compare_num (mult_num a1 b2) (mult_num a2 b1)

	let print r =
		match r with
(*			Number (a,b) -> printf "rat(%s,%s)" (string_of_num a) (string_of_num b)*)
			Number (a,b) ->
				if eq_num a num0 then printf "0*"
				else if eq_num b num1 then printf "(%s)" (string_of_num a)
				else printf "(%s/%s)" (string_of_num a) (string_of_num b)
		 | MinusInfinity -> printf "(-oo)"
		 | PlusInfinity -> printf "(+oo)"

	let term_of = function
		Number (a,b) -> mk_rat_term (mk_number_term a) (mk_number_term b)
(*	 | _ -> raise (Invalid_argument "Infinities have no projections to terms")*)
	 | PlusInfinity -> mk_rat_term (mk_number_term num1) (mk_number_term num0)
	 | MinusInfinity -> mk_rat_term (mk_number_term (sub_num num0 num1)) (mk_number_term num0)


	let add_term = mk_add_rat_term
	let mul_term = mk_mul_rat_term
	let neg_term = mk_neg_rat_term
	let sub_term a b = mk_add_rat_term a (mk_neg_rat_term b)
	let inv_term = mk_inv_rat_term
	let div_term a b = mk_mul_rat_term a (mk_inv_rat_term b)
	let ge_term a b = mk_assert_term (mk_ge_bool_rat_term a b)
	let max_term a b = mk_max_rat_term a b
	let min_term a b = mk_min_rat_term a b
end

module VarType =
struct
	type t=int
   let compare a b = a-b

	let print v =
		if v>0 then printf "v%i" v
		else if v=0 then printf "1"
		else raise (Invalid_argument "Variable index should be non-negative")
end

module Var =
struct
	type t = term
	let equal = alpha_equal
	let hash = Hashtbl.hash
end

module Var2Index(BField : BoundFieldSig) =
struct
	module Table=Hashtbl.Make(Var)

	type t=int ref * int Table.t

	let create n = (ref 0, Table.create n)

	let lookup (info:t) v =
		let (count,table)=info in
		if Table.mem table v then
			Table.find table v
		else
			let index=(!count)+1 in
			begin
				Table.add table v index;
				count:=index;
				index
			end

	let print info =
		let count,table=info in
		let aux k d = printf "%a ->v%i%t" print_term k d eflush in
		(*printf "count=%i%t" !count eflush;*)
		Table.iter aux table

	let invert ((count,table) : t) =
		let ar=Array.make !count (BField.term_of BField.fieldZero) in
		let aux key data = (ar.(data-1)<-key) in
		Table.iter aux table;
		ar

	let restore inverted index =
		if index=0 then
			BField.term_of (BField.fieldUnit)
		else
			inverted.(index-1)
end

module MakeMonom(BField : BoundFieldSig) =
struct
	type elt = VarType.t
	type data = BField.bfield

	let compare = VarType.compare

	let print (v:elt) (kl: data list) =
		match kl with
			[k] -> BField.print k; (*printf"*";*) VarType.print v
		 | _ -> raise (Invalid_argument "More than one coefficient is associated with one variable")

	let append l1 l2 =
		match l1,l2 with
			[],[] -> [BField.fieldZero]
		 | [],[a] -> [a]
		 | [a],[] -> [a]
		 | [a],[b] -> [BField.add a b]
		 | _,_ -> raise (Invalid_argument "Addition non-trivial lists are not supported")

end

module type AF_Sig =
sig
	type vars=int
	type af
	type bfield

	val constvar : vars

   val mk_number: bfield -> af
   val mk_var: vars -> af
   val scale: bfield -> af -> af
   val add: af -> af -> af

   val coef: af -> vars -> bfield
   val remove: af -> vars -> af
   val split: af -> (bfield * vars * af)
   val isNumber: af -> bool
	val isInfinite: af -> bool

	val minusInfinity : af
	val plusInfinity : af

	val term_of : (term array) -> af -> term

	val print : af -> unit
	val print_var : vars -> unit
end

module MakeAF(BField : BoundFieldSig)
	: AF_Sig with type bfield=BField.bfield and type vars=VarType.t =
struct
	module Monom=MakeMonom(BField)
	module Table=Lm_splay_table.MakeTable(Monom)
	module VI=Var2Index(BField)

	type bfield=BField.bfield
	type vars=Monom.elt
	type af=Table.t

	let constvar = 0

	let print_var = VarType.print

	let print f =
		let aux key data =
			printf "+"; Monom.print key [data]
		in
		(*printf "(";*) Table.iter aux f; (*printf")";*) flush stdout

	let mk_number k = Table.add Table.empty constvar k
   let mk_var v = Table.add Table.empty v BField.fieldUnit

	let scale_aux k v d =
		BField.mul k d

   let scale k f =
		if BField.compare k BField.fieldZero =0 then Table.empty
		else if BField.compare k BField.fieldUnit =0 then f
		else Table.map (scale_aux k) f

   let add f1 f2 = Table.union f1 f2

   let coef f v =
		try Table.find f v
		with Not_found -> BField.fieldZero

   let remove = Table.remove

   let split f =
		if !debug_supinf_trace then
			(printf "split "; print f; eflush stdout);
		let (v,coefs,rest)=Table.deletemax f in
		match coefs with
			[c] ->
				if !debug_supinf_trace then
					(Monom.print v coefs; printf" "; print rest; eflush stdout);
				(c,v,rest)
		 | _ -> raise (Invalid_argument "More than one coefficient associated with a variable")

   let isNumber f =
		let test=ref true in
		let aux v c =
			if v<>constvar && compare c BField.fieldZero <>0 then
				test:=false
		in
		Table.iter aux f;
		!test

	let minusInfinity = Table.add Table.empty constvar BField.minusInfinity
	let plusInfinity = Table.add Table.empty constvar BField.plusInfinity

	let isInfinite f =
		BField.isInfinite (coef f constvar)

	let term_of_monom info k v =
		if v=constvar then
			BField.term_of k
		else
			BField.mul_term (BField.term_of k) (VI.restore info v)

	let rec term_of_aux info = function
		[] -> BField.term_of BField.fieldZero
	 | [(v,k)] -> term_of_monom info k v
	 | (v,k)::tl -> BField.add_term (term_of_monom info k v) (term_of_aux info tl)

	let rec term_of info f =
		let l=Table.list_of f in
		let aux = function
			(k,[d]) -> (k,d)
		 | (k,[]) -> raise (Invalid_argument "MakeAF.term_of - empty data list linked to a key in list_of")
		 | (k,_) -> raise (Invalid_argument "MakeAF.term_of - more than one data item per key in list_of")
		in
		let aux2 (k,d) = if BField.compare d BField.fieldZero = 0 then false else true in
		term_of_aux info (List.filter aux2 (List.map aux l))

end

module type SAF_Sig =
sig
	type bfield
	type vars
	type af
	type saf = Affine of af | Max of saf*saf | Min of saf*saf
	type step =
		Assert of string * saf * saf * tactic
	 |	Transitive of string * saf * saf * saf
	 | Tactic of string * tactic

	val affine: af -> saf
   val min: saf -> saf -> saf
   val max: saf -> saf -> saf

   val scale: bfield -> saf -> saf
   val add: saf -> saf -> saf

   val occurs: vars -> saf -> bool
	val isInfinite: saf -> bool
	val isAffine: saf -> bool

	val term_of: (term array) -> saf -> term

	val print : saf -> unit
end

module MakeSAF(BField : BoundFieldSig)(AF : AF_Sig  with type bfield=BField.bfield)
	: SAF_Sig with type bfield=BField.bfield and type vars=AF.vars and type af=AF.af =
struct
	open BField

	type vars=AF.vars
	type af=AF.af
	type bfield=BField.bfield

	type saf = Affine of af | Max of saf*saf | Min of saf*saf
	type step =
		Assert of string * saf * saf * tactic
	 |	Transitive of string * saf * saf * saf
	 | Tactic of string * tactic

	let affine af = Affine af

	let min_aff_simple f1 f =
		match f1 with
			Affine f1' ->
				if AF.isNumber f1' then
					let c=AF.coef f1' AF.constvar in
					if BField.compare c BField.plusInfinity = 0 then Affine f
					else if BField.compare c BField.minusInfinity =0 then f1
					else Min (f1, Affine f)
				else
					Min (f1, Affine f)
		 |	_ -> Min (f1, Affine f)

	let min_aff f1 f =
		if AF.isNumber f then
			let c=AF.coef f AF.constvar in
			if BField.compare c BField.plusInfinity = 0 then f1
			else if BField.compare c BField.minusInfinity =0 then Affine f
			else min_aff_simple f1 f
		else
			min_aff_simple f1 f

   let min f1 f2 =
		match f1,f2 with
			_, Affine f -> min_aff f1 f
		 | Affine f, _ -> min_aff f2 f
		 | Min (f11,f12), Min (f21,f22) -> Min (f1,f2)
		 | _,_ -> raise (Invalid_argument "SAF.min: detected a mixture of min and max")

	let max_aff_simple f1 f =
		match f1 with
			Affine f1' ->
				if AF.isNumber f1' then
					let c=AF.coef f1' AF.constvar in
					if BField.compare c BField.plusInfinity = 0 then f1
					else if BField.compare c BField.minusInfinity =0 then Affine f
					else Max (f1, Affine f)
				else
					Max (f1, Affine f)
		 |	_ -> Max (f1, Affine f)

	let max_aff f1 f =
		if AF.isNumber f then
			let c=AF.coef f AF.constvar in
			if BField.compare c BField.plusInfinity = 0 then Affine f
			else if BField.compare c BField.minusInfinity =0 then f1
			else max_aff_simple f1 f
		else
			max_aff_simple f1 f

   let max f1 f2 =
		match f1,f2 with
			_, Affine f -> max_aff f1 f
		 | Affine f, _ -> max_aff f2 f
		 | Max(f11,f12),Max(f21,f22) -> Max (f1,f2)
		 | _,_ -> raise (Invalid_argument "SAF.min: detected a mixture of min and max")


   let rec scale k f =
		match f with
			Affine f' -> Affine (AF.scale k f')
		 | Min (a,b) ->
				let cmp=compare k fieldZero in
				if cmp<0 then Max (scale k a, scale k b)
				else if cmp=0 then Affine(AF.mk_number(fieldZero))
				else Min (scale k a, scale k b)
		 | Max (a,b) ->
				let cmp=compare k fieldZero in
				if cmp<0 then Min (scale k a, scale k b)
				else if cmp=0 then Affine(AF.mk_number(fieldZero))
				else Max (scale k a, scale k b)

   let rec add f1 f2 =
		match f1,f2 with
			Affine f1', Affine f2' -> Affine (AF.add f1' f2')
		 | Min (a,b), _ -> Min (add a f2, add b f2)
		 | _, Min (a,b) -> Min (add f1 a, add f1 b)
		 | Max (a,b), _ -> Max (add a f2, add b f2)
		 | _, Max (a,b) -> Max (add f1 a, add f1 b)

   let rec occurs v f =
		match f with
			Affine f' -> (compare (AF.coef f' v) fieldZero <>0)
		 | Min (a,b) -> (occurs v a) || (occurs v b)
		 | Max (a,b) -> (occurs v a) || (occurs v b)

	let isInfinite = function
		Affine f ->
			AF.isInfinite f
	 | _ -> false

	let isAffine = function
		Affine _ -> true
	 | _ -> false

	let rec print f =
		match f with
			Affine f' -> AF.print f'
		 | Max (a,b) ->
				printf "max("; print a; printf"; "; print b; printf ")"
		 | Min (a,b) ->
				printf "min("; print a; printf"; "; print b; printf ")"

	let rec term_of info = function
		Affine f -> AF.term_of info f
	 | Max (a,b) -> BField.max_term (term_of info a) (term_of info b)
	 | Min (a,b) -> BField.min_term (term_of info a) (term_of info b)
end

module type SACS_Sig =
sig
	type vars
	type af
	type saf
	type step
	type sacs

   val empty: sacs
   val addConstr: sacs -> af -> sacs

   val upper: (term array) -> sacs -> vars -> (saf * step list)
   val lower: (term array) -> sacs -> vars -> (saf * step list)

	val print: sacs -> unit
end

module MakeSACS(BField : BoundFieldSig)
					(AF : AF_Sig  with type bfield=BField.bfield)
					(SAF : SAF_Sig  with type bfield=BField.bfield and type af=AF.af)
	: SACS_Sig with type vars=AF.vars and type af=AF.af and type saf=SAF.saf
					and type step=SAF.step =
struct
	type vars=AF.vars
	type af=AF.af
	type saf=SAF.saf
	type step=SAF.step
	type sacs=af list

   let empty = []
   let addConstr s f = f::s

	let print s =
		(*printf "{";*)
		List.iter (fun x -> let _=AF.print x in printf ">=0\n") s (*; printf"}"*)

	let rec upper' info s v =
		match s with
			[] -> SAF.affine AF.plusInfinity, []
		 | f::tl ->
				if BField.compare (AF.coef f v) BField.fieldZero >=0 then
					upper' info tl v
				else
					let k=BField.neg (BField.inv (AF.coef f v)) in
					let rest=AF.remove f v in
					let r0,a0=upper' info tl v in
					let r1=SAF.min r0 (SAF.affine (AF.scale k rest)) in
					if SAF.isAffine r1 then
						r1,(SAF.Assert ("upper 0",r1,SAF.affine (AF.mk_var v), idT))::a0
					else
						r1,(SAF.Assert ("upper 1",r1,SAF.affine (AF.mk_var v), ge_minLeftIntro))::a0

	let upper info s v =
		let result,actions = upper' info s v in
		if !debug_supinf_steps then
			begin
				printf "upper: "; AF.print_var v; printf "<="; SAF.print result; eflush stdout;
			end;
		result,actions

   let rec lower' info s v =
		match s with
			[] -> SAF.affine AF.minusInfinity,[]
		 | f::tl ->
				if BField.compare (AF.coef f v) BField.fieldZero <=0 then
					lower' info tl v
				else
					let k=BField.neg (BField.inv (AF.coef f v)) in
					let rest=AF.remove f v in
					let r0,a0=lower' info tl v in
					let r1=SAF.max r0 (SAF.affine (AF.scale k rest)) in
					if SAF.isAffine r1 then
						r1,(SAF.Assert ("lower 0",SAF.affine (AF.mk_var v), r1, idT))::a0
					else
						r1,(SAF.Assert ("lower 1",SAF.affine (AF.mk_var v), r1, ge_maxRightIntro))::a0

	let lower info s v =
		let result,actions = lower' info s v in
		if !debug_supinf_steps then
			begin
				printf "lower: "; SAF.print result; printf"<="; AF.print_var v; eflush stdout;
			end;
		result,actions
end

module type CS_Sig =
sig
	type t
	type elt

   val empty: t
   val add: t -> elt -> t

   val mem: t -> elt -> bool
end

module AF=MakeAF(RationalBoundField)
module SAF=MakeSAF(RationalBoundField)(AF)
module SACS=MakeSACS(RationalBoundField)(AF)(SAF)
module CS=Lm_set.LmMakeDebug(VarType)
module VI=Var2Index(RationalBoundField)

open RationalBoundField

let suppa' info (x:AF.vars) (f:AF.af) =
	if !debug_supinf_trace then
		(printf"suppa: ";	AF.print_var x; AF.print f; eflush stdout);
	let b = AF.coef f x in
	let c = AF.remove f x in
	let saf_x=SAF.affine (AF.mk_var x) in
   if compare b fieldUnit < 0 then
		let result=AF.scale (inv (sub fieldUnit b)) c in
		(result, [SAF.Assert("suppa case 0",SAF.affine result, saf_x, idT)])
		(* SAF.AssertT <<'x <= result>> thenAT
			'x<='y <-->
			(1-'b)*'x <= (1-'b)*'y <-->
			'x <= 'b*'x + (1-'b)*'y <-->(normalize) 'x <= 'f *)
	else
      if (compare b fieldUnit = 0) && (AF.isNumber c) then
			let cmp=compare (AF.coef c AF.constvar) fieldZero in
			if cmp<0 then
				(AF.minusInfinity, [SAF.Assert ("suppa case 100",SAF.affine f, saf_x, idT)])
			else
				if cmp=0 then
					(f, [SAF.Assert("suppa case 1010",SAF.affine f, saf_x, idT)])
				else
					(AF.plusInfinity, [])
		else
			(AF.plusInfinity, [])

let suppa info x f =
	let (result,actions)=suppa' info x f in
	if !debug_supinf_steps then
		begin
			printf"suppa<: "; AF.print_var x; printf"<="; AF.print f; eflush stdout;
			printf"suppa>: "; AF.print_var x; printf"<="; AF.print result; eflush stdout;
		end;
	(result,actions)

let rec supp' info (x:AF.vars) (s:SAF.saf) =
	match s with
		SAF.Affine f ->
			let r,a=suppa info x f in
			SAF.affine r, a
	 | SAF.Min (a,b) ->
			let f1,a1=supp' info x a in
			let f2,a2=supp' info x b in
			let result=SAF.min f1 f2 in
			let act=SAF.Assert ("supp",result,
			                 (SAF.affine (AF.mk_var x)),
								  (ge_minLeftIntro)
								)
			in
			result, act::(a1@a2)
			(*result, act::(a1@(a2@[SAF.Tactic (tryT (ge_minLeftElim (-1)))]))*)
	 | SAF.Max _ -> raise (Invalid_argument "Itt_supinf.supp applied to max(...,...)")
	(* SAF.AssertT << 'x <= min('a;'b) >> thenAT
		'x <= min('a;'b) <-->
		'x <= 'a & 'x <= 'b *)

let supp info x s =
	let result,actions=supp' info x s in
	if !debug_supinf_steps then
		begin
			printf"supp<: "; AF.print_var x; printf"<="; SAF.print s; eflush stdout;
			printf"supp>: "; AF.print_var x; printf"<="; SAF.print result; eflush stdout;
		end;
	result,actions

let inffa' info (x:AF.vars) (f:AF.af) =
	if !debug_supinf_trace then
		(printf"inffa: ";	AF.print_var x; printf" "; AF.print f; eflush stdout);
	let b = AF.coef f x in
	let c = AF.remove f x in
	let saf_x=SAF.affine (AF.mk_var x) in
   if compare b fieldUnit < 0 then
		let result=AF.scale (inv (sub fieldUnit b)) c in
		(result, [SAF.Assert ("inffa case 0",saf_x,SAF.affine result, idT)])
		(* SAF.AssertT <<'x >= result>> thenAT
			'x>='y <-->
			(1-'b)*'x >= (1-'b)*'y <-->
			'x >= 'b*'x + (1-'b)*'y <-->(normalize) 'x >= 'f *)
	else
      if (compare b fieldUnit = 0) && (AF.isNumber c) then
			let cmp=compare (AF.coef c AF.constvar) fieldZero in
			if cmp>0 then
				(AF.plusInfinity, [SAF.Assert ("inffa case 100",saf_x, SAF.affine f, idT)])
			else
				if cmp=0 then
					(f,[SAF.Assert("inffa case 1010",saf_x, SAF.affine f, idT)])
				else
					(AF.minusInfinity,[])
		else
			(AF.minusInfinity,[])

let inffa info x f =
	let result,actions=inffa' info x f in
	if !debug_supinf_steps then
		begin
			printf"inffa<: "; AF.print f; printf"<="; AF.print_var x; eflush stdout;
			printf"inffa>: "; AF.print result; printf"<="; AF.print_var x; eflush stdout;
		end;
	(result,actions)

let rec inff' info (x:AF.vars) (s:SAF.saf) =
	match s with
		SAF.Affine f ->
			let r,a=inffa info x f in
			SAF.affine r, a
	 | SAF.Max (a,b) ->
			let f1,a1=inff' info x a in
			let f2,a2=inff' info x b in
			let result=SAF.max f1 f2 in
			result, (SAF.Assert ("inff",SAF.affine (AF.mk_var x), result, ge_maxRightIntro))::(a1@a2)
(*			result, (SAF.Assert (SAF.affine (AF.mk_var x), result, (addHiddenLabelT "inff" thenT ge_maxRightIntro)))::(a1@(a2@[SAF.Tactic (tryT (ge_maxRightElim (-1)))]))*)
	 | SAF.Min _ -> raise (Invalid_argument "Itt_supinf.inff applied to min(...,...)")
	(* SAF.AssertT << 'x >= max('a;'b) >> thenAT
		'x >= max('a;'b) <-->
		'x >= 'a & 'x >= 'b *)

let inff info x s =
	let result,actions=inff' info x s in
	if !debug_supinf_steps then
		begin
			printf"inff<: "; SAF.print s; printf"<="; AF.print_var x; eflush stdout;
			printf"inff>: "; SAF.print result; printf"<="; AF.print_var x; eflush stdout;
		end;
	(result,actions)

let rec supa info (c:SACS.sacs) (f:AF.af) (h:CS.t) =
	if !debug_supinf_trace then
		begin
			printf"supa:\n";	SACS.print c; eflush stdout;
			AF.print f; eflush stdout;
			CS.print h; eflush stdout
		end;
	let (r,v,b) = AF.split f in
	if v=AF.constvar then
		(SAF.affine (AF.mk_number r), [])
	else
		let af_v=AF.mk_var v in
		let saf_v = SAF.affine af_v in
		if (AF.isNumber b) && (compare (AF.coef b AF.constvar) fieldZero =0) then
			if compare r fieldUnit = 0 then
				if CS.mem h v then
					(saf_v, [])
				else
					begin
						if !debug_supinf_trace then
							(printf "case 1001"; eflush stdout);
						let r0,a0=SACS.upper info c v in
						let saf_v=SAF.affine (AF.mk_var v) in
						(*let a0=[r0, saf_v, addHiddenLabelT "supa 1001 a0"] in*)
						let r1,a1=sup info c r0 (CS.add h v) in
						let a11=[SAF.Transitive("supa 1001 a11",r1,r0,saf_v)] in
						let r2,a2=supp info v r1 in
						(r2,a2@(a11@(a1@a0)))
					end
			else
				if compare r fieldZero < 0 then
					let r0,a0=inf info c saf_v h in
					(SAF.scale r r0, a0)
				else
					let r0,a0=sup info c saf_v h in
					(SAF.scale r r0, a0)
		else
         let b',a0 = sup info c (SAF.affine b) (CS.add h v) in
			let scaled_v=SAF.affine (AF.scale r af_v) in
			let f'=SAF.add scaled_v b' in
			let saf_f=SAF.affine f in
			let a01=SAF.Assert("supa 11",f', saf_f, idT) in
			if SAF.occurs v b' then
				let r1,a1=sup info c f' h in
				(r1,a1@(a01::a0))
			else
				let r1,a1=sup info c scaled_v h in
				let r2=SAF.add r1 b' in
				let b''=SAF.scale (neg fieldUnit) b' in
				let a2=SAF.Assert("supa case 1110",r2,f',ge_addMono (SAF.term_of info b'')) in
				let a3=SAF.Transitive("supa case 1111",r2,f',saf_f) in
				(r2, (a3::(a2::(a1@(a01::a0)))))

and sup' info (c:SACS.sacs) (s:SAF.saf) (h:CS.t) =
	match s with
		SAF.Affine f -> supa info c f h
	 | SAF.Min (a,b) ->
			let f1,a1=sup' info c a h in
			let f2,a2=sup' info c b h in
			let result=SAF.min f1 f2 in
			let actions=
				if SAF.isAffine result then
					(SAF.Assert("sup 0",result, s, ge_minLeftIntro))::(a1@a2)
				else
					(SAF.Assert("sup 1",result, s, (tryT min_ge_minIntro)))::(a1@a2)
			in
			result, actions
	 | SAF.Max _ -> raise (Invalid_argument "Itt_supinf.sup applied to max(...,...)")

and sup info (c:SACS.sacs) (s:SAF.saf) (h:CS.t) =
	let result,actions=sup' info c s h in
	if !debug_supinf_steps then
		begin
			printf"sup: "; SAF.print s; printf"<="; SAF.print result; eflush stdout;
		end;
	(result,actions)

and infa info (c:SACS.sacs) (f:AF.af) (h:CS.t) =
	if !debug_supinf_trace then
		begin
			printf"infa:\n";
			SACS.print c; eflush stdout;
			AF.print f; eflush stdout;
			CS.print h; eflush stdout
		end;
   let (r,v,b) = AF.split f in
	if v=AF.constvar then
		begin
			if !debug_supinf_trace then
				(printf "case 0"; eflush stdout);
			(SAF.affine (AF.mk_number r), [])
		end
	else
		begin
			if !debug_supinf_trace then
				(printf "case 1"; eflush stdout);
			let af_v=AF.mk_var v in
			let saf_v = SAF.affine af_v in
			if (AF.isNumber b) && (compare (AF.coef b AF.constvar) fieldZero =0) then
				begin
					if !debug_supinf_trace then
						(printf "case 10"; eflush stdout);
					if compare r fieldUnit = 0 then
						begin
							if !debug_supinf_trace then
								(printf "case 100"; eflush stdout);
							if CS.mem h v then
								begin
									if !debug_supinf_trace then
										(printf "case 1000"; eflush stdout);
									(saf_v, [])
								end
							else
								begin
									if !debug_supinf_trace then
										(printf "case 1001"; eflush stdout);
									let r0,a0=SACS.lower info c v in
									(*let a0=[saf_v, r0, addHiddenLabelT "infa 1001 a0"] in*)
									let r1,a1=inf info c r0 (CS.add h v) in
									let a11=[SAF.Transitive("infa 1001 a11",saf_v,r0,r1)] in
									let r2,a2=inff info v r1 in
									(r2, a2@(a11@(a1@a0)))
								end
						end
					else
						begin
							if !debug_supinf_trace then
								(printf "case 101"; eflush stdout);
							if compare r fieldZero < 0 then
								begin
									if !debug_supinf_trace then
										(printf "case 1010"; eflush stdout);
									let result,actions=sup info c saf_v h in
									(SAF.scale r result, actions)
								end
							else
								begin
									if !debug_supinf_trace then
										(printf "case 1011"; eflush stdout);
									let result,actions=inf info c saf_v h in
									(SAF.scale r result, actions)
								end
						end
				end
			else
				begin
					if !debug_supinf_trace then
						(printf "case 11"; eflush stdout);
					let b',a0 = inf info c (SAF.affine b) (CS.add h v) in
					let scaled_v=SAF.affine (AF.scale r af_v) in
					let f'=SAF.add scaled_v b' in
					let saf_f=SAF.affine f in
					let a01=SAF.Assert("infa 11",saf_f, f', idT) in
					if SAF.occurs v b' then
						begin
							if !debug_supinf_trace then
								(printf "case 110"; eflush stdout);
							let r1,a1=inf info c f' h in
							r1, a1@(a01::a0)
						end
					else
						begin
							if !debug_supinf_trace then
								(printf "case 111"; eflush stdout);
							let r1,a1=inf info c scaled_v h in
							let r2=SAF.add r1 b' in
							let b''=SAF.scale (neg fieldUnit) b' in
							let a2=SAF.Assert("infa case 1110",f',r2,ge_addMono (SAF.term_of info b'')) in
							let a3=SAF.Transitive("infa case 1111",saf_f,f',r2) in
							(r2, (a3::(a2::(a1@(a01::a0)))))
						end
				end
		end

and inf' info (c:SACS.sacs) (s:SAF.saf) (h:CS.t) =
	match s with
		SAF.Affine f -> infa info c f h
	 | SAF.Max (a,b) ->
			let f1,a1=inf' info c a h in
			let f2,a2=inf' info c b h in
			let result=SAF.max f1 f2 in
			let actions=
				if SAF.isAffine result then
					(SAF.Assert("inf 0",s, result, ge_maxRightIntro))::(a1@a2)
				else
					(SAF.Assert("inf 1",s, result, (tryT max_ge_maxIntro)))::(a1@a2)
			in
			result, actions
	 | SAF.Min _ -> raise (Invalid_argument "Itt_supinf.inf applied to min(...,...)")

and inf info (c:SACS.sacs) (s:SAF.saf) (h:CS.t) =
	let result,actions=inf' info c s h in
	if !debug_supinf_steps then
		begin
			printf"inf: "; SAF.print result; printf"<="; SAF.print s; eflush stdout;
		end;
	(result,actions)

let monom2af var2index t =
	if is_mul_rat_term t then
		let t1,t2=dest_mul_rat t in
		if is_rat_term t1 then
			let k1,k2=dest_rat t1 in
			let i=VI.lookup var2index t2 in
			let f=AF.mk_var i in
			AF.scale (Number (dest_number k1, dest_number k2)) f
		else
			let i=VI.lookup var2index t in
			AF.mk_var i
	else
		if is_rat_term t then
			let k1,k2=dest_rat t in
			AF.mk_number (Number (dest_number k1, dest_number k2))
		else
			let i=VI.lookup var2index t in
			AF.mk_var i

let rec linear2af var2index t =
	if is_add_rat_term t then
		let t1,t2=dest_add_rat t in
		let f1=linear2af var2index t1 in
		let f2=linear2af var2index t2 in
		AF.add f1 f2
	else
		monom2af var2index t

let ge2af var2index t =
	let left,right=dest_ge_rat t in
	let f1=linear2af var2index left in
	let f2=linear2af var2index right in
	let neg_f2=AF.scale (neg fieldUnit) f2 in
	AF.add f1 neg_f2

let make_sacs var2index p =
   let l = List.filter is_ge_rat_term (Sequent.all_hyps p) in
	let afs=List.map (ge2af var2index) l in
	List.fold_left SACS.addConstr SACS.empty afs

let assert_geT info f1 f2 =
	assertT (mk_ge_rat_term (SAF.term_of info f1) (SAF.term_of info f2))
(*	let f=SAF.add f1 (SAF.scale (neg fieldZero) f2) in
	assertT (mk_ge_rat_term (SAF.term_of info f) (term_of fieldZero))
*)

let runAssertT info label f1 f2 tac =
		assert_geT info f1 f2 thenAT (addHiddenLabelT label thenT tryT tac)

let rec runAssertStepT info label tac f1 f2 =
	match f1,f2 with
		SAF.Affine _, SAF.Affine _ -> runAssertT info label f1 f2 tac
	 |	SAF.Affine _, SAF.Max(s21,s22) -> runAssertStepListT info label tac [(f1,s21);(f1,s22)]
	 | SAF.Min(s11,s12), SAF.Affine _ -> runAssertStepListT info label tac [(s11,f2);(s12,f2)]
	 | SAF.Min(s11,s12),SAF.Max(s21,s22) ->
			runAssertStepListT info label tac [(s11,s21);(s11,s22);(s12,s21);(s12,s22)]
	 | SAF.Max(s11,s12),SAF.Max(s21,s22) -> runAssertStepListT info label tac [(s11,s21);(s12,s22)]
	 | SAF.Min(s11,s12),SAF.Min(s21,s22) -> runAssertStepListT info label tac [(s11,s21);(s12,s22)]
	 | _,_ -> runAssertT info label f1 f2 tac

and runAssertStepListT info label tac = function
	[(f1,f2)] -> runAssertStepT info label tac f1 f2
 | (f1,f2)::tl -> (runAssertStepT info label tac f1 f2) thenMT runAssertStepListT info label tac tl
 | [] -> raise (Invalid_argument "runAssertStepListT applied to an empty list")

let runTransitiveT info label f1 f2 f3=
	runAssertT info label f1 f3 (geTransitive (SAF.term_of info f2))

let rec runTransitiveStepT info label f1 f2 f3 =
	match f1,f2,f3 with
		SAF.Affine _, SAF.Affine _, SAF.Affine _ -> runTransitiveT info label f1 f2 f3
	 |	_, SAF.Max(s21,s22), SAF.Max(s31,s32) -> runTransitiveStepListT info label [(f1,s21,s31);(f1,s22,s32)]
	 |	SAF.Min (s11,s12), SAF.Min(s21,s22), _ -> runTransitiveStepListT info label [(s11,s21,f3);(s12,s22,f3)]
	 |	_, SAF.Affine _, SAF.Max(s31,s32) -> runTransitiveStepListT info label [(f1,f2,s31);(f1,f2,s32)]
	 |	SAF.Min (s11,s12), SAF.Affine _, _ -> runTransitiveStepListT info label [(s11,f2,f3);(s12,f2,f3)]
	 | _,_,_ -> runTransitiveT info label f1 f2 f3

and runTransitiveStepListT info label = function
	[(f1,f2,f3)] -> runTransitiveStepT info label f1 f2 f3
 | (f1,f2,f3)::tl -> (runTransitiveStepT info label f1 f2 f3) thenMT runTransitiveStepListT info label tl
 | [] -> raise (Invalid_argument "runTransitiveStepListT applied to an empty list")

let rec runListT info = function
	[] -> idT
 | [SAF.Assert (label,f1,f2,tac)] ->
		begin
			if !debug_supinf_steps then
				(printf "%s " label;SAF.print f1;printf">=";SAF.print f2;eflush stdout);
			if SAF.isInfinite f1 || SAF.isInfinite f2 then
				idT
			else
				runAssertStepT info label tac f1 f2
		end
 | [SAF.Transitive (label,f1,f2,f3)] ->
		begin
			if !debug_supinf_steps then
				(printf "%s " label;SAF.print f1;printf">=";SAF.print f2;printf">=";SAF.print f3;eflush stdout);
			if SAF.isInfinite f1 || SAF.isInfinite f2 || SAF.isInfinite f3 then
				idT
			else
				runTransitiveStepT info label f1 f2 f3
		end
 | [SAF.Tactic(label,tac)] ->
		begin
			if !debug_supinf_steps then
				printf "%s%t" label eflush;
			addHiddenLabelT label thenT tac
		end
 | (SAF.Assert (label,f1,f2,tac))::tl ->
		begin
			if !debug_supinf_steps then
				(printf "%s " label;SAF.print f1;printf">=";SAF.print f2;eflush stdout);
			if SAF.isInfinite f1 || SAF.isInfinite f2 then
				runListT info tl
			else
				runAssertStepT info label tac f1 f2 thenMT runListT info tl
		end
 | (SAF.Transitive (label,f1,f2,f3))::tl ->
		begin
			if !debug_supinf_steps then
				(printf "%s " label;SAF.print f1;printf">=";SAF.print f2;printf">=";SAF.print f3;eflush stdout);
			if SAF.isInfinite f1 || SAF.isInfinite f2 || SAF.isInfinite f3 then
				runListT info tl
			else
				runTransitiveStepT info label f1 f2 f3 thenMT runListT info tl
		end
 | (SAF.Tactic(label,tac))::tl ->
		begin
			if !debug_supinf_steps then
				printf "%s%t" label eflush;
			addHiddenLabelT label thenT (tac thenMT runListT info tl)
		end

let testT = funT (fun p ->
	let var2index = VI.create 13 in
	let constrs=make_sacs var2index p in
	let info=VI.invert var2index in
	printf "Vars:\n";
	VI.print var2index;
	printf "SACS:\n"; SACS.print constrs;
	eflush stdout;
	begin
		let saf'=SAF.affine (AF.mk_var 1) in
		let sup',a1=sup info constrs saf' CS.empty in
		let inf',a2=inf info constrs saf' CS.empty in
		printf "start=";SAF.print saf'; eflush stdout;
		printf"sup=";SAF.print sup'; eflush stdout;
		printf"inf=";SAF.print inf'; eflush stdout;
		SAF.print inf'; printf "<="; SAF.print saf'; printf "<="; SAF.print sup'; eflush stdout;
		let actions=List.rev (SAF.Transitive("final",sup',(SAF.affine (AF.mk_var 1)),inf')::(a1@a2)) in
		runListT info actions
	end
)

interactive test 'a 'b 'c :
sequent { <H> >- 'a in rationals } -->
sequent { <H> >- 'b in rationals } -->
sequent { <H> >- 'c in rationals } -->
sequent { <H>; ge_rat{'a; add_rat{'b; rat{1;1}}};
               ge_rat{'c; add_rat{'b; rat{3;1}}};
               ge_rat{'b; add_rat{'a; rat{0;1}}}
               >- "assert"{bfalse} }

interactive test2 'a 'b 'c :
sequent { <H> >- 'a in rationals } -->
sequent { <H> >- 'b in rationals } -->
sequent { <H> >- 'c in rationals } -->
sequent { <H>; ge_rat{'a; rat{0;1}};
					ge_rat{'b; rat{0;1}};
					ge_rat{rat{-1;1}; add_rat{'a; 'b}}
					>- "assert"{bfalse} }

interactive test3 'a 'b 'c :
sequent { <H> >- 'x in rationals } -->
sequent { <H> >- 'y in rationals } -->
sequent { <H>;
					ge_rat{mul_rat{rat{-1;1};'x}; mul_rat{rat{-1;1};'y}};
					ge_rat{'y; rat{0;1}};
					ge_rat{add_rat{rat{1;1}; mul_rat{rat{-1;1};'y}};'x}
					>- "assert"{bfalse} }

interactive test4 'a 'b 'c :
sequent { <H> >- 'a in rationals } -->
sequent { <H> >- 'b in rationals } -->
sequent { <H> >- 'c in rationals } -->
sequent { <H>; ge_rat{'a; add_rat{'b;rat{3;1}}};
					ge_rat{'a; add_rat{rat{3;1};mul_rat{rat{-1;1};'b}}};
					ge_rat{add_rat{'b;rat{2;1}}; 'a}
					>- "assert"{bfalse} }

(*
interactive test 'H 'a 'b 'c :
sequent { <H> >- 'a in rationals } -->
sequent { <H> >- 'b in rationals } -->
sequent { <H> >- 'c in rationals } -->
sequent { <H>; ge_rat{add_rat{rat{-1;1};add_rat{mul_rat{rat{1;1};'a};mul_rat{rat{-1;1};'b}}}; rat{0;1}};
					ge_rat{add_rat{rat{-3;1};add_rat{mul_rat{rat{-1;1};'b};mul_rat{rat{1;1};'c}}}; rat{0;1}};
					ge_rat{add_rat{mul_rat{rat{-1;1};'a};mul_rat{rat{1;1};'b}}; rat{0;1}}
               >- "assert"{bfalse} }

interactive test2 'H 'a 'b 'c :
sequent { <H> >- 'a in rationals } -->
sequent { <H> >- 'b in rationals } -->
sequent { <H> >- 'c in rationals } -->
sequent { <H>; ge_rat{mul_rat{rat{1;1};'a}; rat{0;1}};
					ge_rat{mul_rat{rat{1;1};'b}; rat{0;1}};
					ge_rat{add_rat{rat{-1;1};add_rat{mul_rat{rat{-1;1};'a};mul_rat{rat{-1;1};'b}}}; rat{0;1}}
					>- "assert"{bfalse} }
*)
