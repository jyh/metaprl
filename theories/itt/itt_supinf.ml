extends Itt_equal
extends Itt_rfun
extends Itt_logic
extends Itt_bool
extends Itt_int_ext
extends Itt_rat

open Printf
open Lm_debug
open Refiner.Refiner.Term
open Refiner.Refiner.TermSubst

open Tactic_type
open Tactic_type.Tacticals

open Itt_struct
open Itt_bool

open Itt_int_base
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
	type vars
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

	let list_of tb =
		let lst = ref [] in
		let aux e d = (lst:=(e,d)::!lst) in
		Table.iter aux tb;
		!lst

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
		term_of_aux info (list_of f)

end

module type SAF_Sig =
sig
	type bfield
	type vars
	type af
	type saf

	val affine: af -> saf
   val min: saf -> saf -> saf
   val max: saf -> saf -> saf

   val scale: bfield -> saf -> saf
   val add: saf -> saf -> saf

   val decompose: saf -> af list
   val occurs: vars -> saf -> bool

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

	type saf = Affine of af | Max of (saf list) | Min of (saf list)

	let affine af = Affine af

	let min_aff_simple f1 f =
		match f1 with
			Affine f1' ->
				if AF.isNumber f1' then
					let c=AF.coef f1' AF.constvar in
					if BField.compare c BField.plusInfinity = 0 then Affine f
					else if BField.compare c BField.minusInfinity =0 then f1
					else Min [f1; Affine f]
				else
					Min [f1; Affine f]
		 |	Min l -> Min ((Affine f)::l)
		 | Max l -> Min [Affine f; f1]

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
			Min l1, Min l2 -> Min(l1 @ l2)
		 | _, Affine f -> min_aff f1 f
		 | Affine f, _ -> min_aff f2 f
		 | _,_ -> Min [f1;f2]

	let max_aff_simple f1 f =
		match f1 with
			Affine f1' ->
				if AF.isNumber f1' then
					let c=AF.coef f1' AF.constvar in
					if BField.compare c BField.plusInfinity = 0 then f1
					else if BField.compare c BField.minusInfinity =0 then Affine f
					else Max [f1; Affine f]
				else
					Max [f1; Affine f]
		 |	Max l -> Max ((Affine f)::l)
		 | Min l -> Max [Affine f; f1]

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
			Max l1, Max l2 -> Max(l1 @ l2)
		 | _, Affine f -> max_aff f1 f
		 | Affine f, _ -> max_aff f2 f
		 | _,_ -> Max [f1;f2]


   let rec scale k f =
		match f with
			Affine f' -> Affine (AF.scale k f')
		 | Min l ->
				let cmp=compare k fieldZero in
				if cmp<0 then Max (List.map (scale k) l)
				else if cmp=0 then Affine(AF.mk_number(fieldZero))
				else Min (List.map (scale k) l)
		 | Max l ->
				let cmp=compare k fieldZero in
				if cmp<0 then Min (List.map (scale k) l)
				else if cmp=0 then Affine(AF.mk_number(fieldZero))
				else Max (List.map (scale k) l)

   let rec add f1 f2 =
		match f1,f2 with
			Affine f1', Affine f2' -> Affine (AF.add f1' f2')
		 | Min l1, _ -> Min (List.map (add f2) l1)
		 | _, Min l2 -> Min (List.map (add f1) l2)
		 | Max l1, _ -> Max (List.map (add f2) l1)
		 | _, Max l2 -> Max (List.map (add f1) l2)

   let rec decompose f =
		match f with
			Affine f' -> [f']
		 | Min l -> List.concat (List.map decompose l)
		 | Max l -> List.concat (List.map decompose l)

   let rec occurs v f =
		match f with
			Affine f' -> (compare (AF.coef f' v) fieldZero <>0)
		 | Min l -> List.exists (occurs v) l
		 | Max l -> List.exists (occurs v) l

	let rec print f =
		match f with
			Affine f' -> AF.print f'
		 | Max fl ->
				printf "max("; List.iter (fun x -> let _=print x in printf";") fl; printf")"
		 | Min fl ->
				printf "min("; List.iter (fun x -> let _=print x in printf";") fl; printf")"

	let rec term_of_max info = function
		[] -> raise (Invalid_argument "Maximum of empty list")
	 | [f] -> term_of info f
	 | hd::tl -> BField.max_term (term_of info hd) (term_of_max info tl)

	and term_of_min info = function
		[] -> raise (Invalid_argument "Minimum of empty list")
	 | [f] -> term_of info f
	 | hd::tl -> BField.min_term (term_of info hd) (term_of_max info tl)

	and term_of info = function
		Affine f -> AF.term_of info f
	 | Max sl -> term_of_max info sl
	 | Min sl -> term_of_min info sl
end

module type SACS_Sig =
sig
	type vars
	type af
	type saf
	type sacs

   val empty: sacs
   val addConstr: sacs -> af -> sacs

   val upper: sacs -> vars -> saf
   val lower: sacs -> vars -> saf

	val print: sacs -> unit
end

module MakeSACS(BField : BoundFieldSig)
					(AF : AF_Sig  with type bfield=BField.bfield)
					(SAF : SAF_Sig  with type bfield=BField.bfield and type af=AF.af)
	: SACS_Sig with type vars=AF.vars and type af=AF.af and type saf=SAF.saf =
struct
	type vars=AF.vars
	type af=AF.af
	type saf=SAF.saf
	type sacs=af list

   let empty = []
   let addConstr s f = f::s

	let print s =
		(*printf "{";*)
		List.iter (fun x -> let _=AF.print x in printf ">=0\n") s (*; printf"}"*)

	let rec upper' s v =
		match s with
			[] -> SAF.affine AF.plusInfinity
		 | f::tl ->
				if BField.compare (AF.coef f v) BField.fieldZero >=0 then
					upper' tl v
				else
					let k=BField.neg (BField.inv (AF.coef f v)) in
					let rest=AF.remove f v in
					SAF.min (upper' tl v) (SAF.affine (AF.scale k rest))

	let upper s v =
		let result = upper' s v in
		if !debug_supinf_steps then
			begin
				printf "upper: "; AF.print_var v; printf "<="; SAF.print result; eflush stdout;
			end;
		result

   let rec lower' s v =
		match s with
			[] -> SAF.affine AF.minusInfinity
		 | f::tl ->
				if BField.compare (AF.coef f v) BField.fieldZero <=0 then
					lower' tl v
				else
					let k=BField.neg (BField.inv (AF.coef f v)) in
					let rest=AF.remove f v in
					SAF.max (lower' tl v) (SAF.affine (AF.scale k rest))

	let lower s v =
		let result = lower' s v in
		if !debug_supinf_steps then
			begin
				printf "lower: "; SAF.print result; printf"<="; AF.print_var v; eflush stdout;
			end;
		result
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
   if compare b fieldUnit < 0 then
		let result=AF.scale (inv (sub fieldUnit b)) c in
		(result, [assertT (mk_ge_rat_term (AF.term_of info result) (VI.restore info x)) thenAT addHiddenLabelT "suppa case 0"])
		(* assertT <<'x <= result>> thenAT
			'x<='y <-->
			(1-'b)*'x <= (1-'b)*'y <-->
			'x <= 'b*'x + (1-'b)*'y <-->(normalize) 'x <= 'f *)
	else
      if (compare b fieldUnit = 0) && (AF.isNumber c) then
			let cmp=compare (AF.coef c AF.constvar) fieldZero in
			if cmp<0 then
				(AF.minusInfinity, [assertT (mk_ge_rat_term (AF.term_of info f) (VI.restore info x)) thenAT addHiddenLabelT "suppa case 100"])
			else
				if cmp=0 then
					(f, [assertT (mk_ge_rat_term (AF.term_of info f) (VI.restore info x)) thenAT addHiddenLabelT "suppa case 1010"])
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

let supp' info (x:AF.vars) (s:SAF.saf) =
	let aux f = let (result,actions)=suppa info x f in (SAF.affine result, actions) in
	let aux2 (f1,a1) (f2,a2) = SAF.min f1 f2, a1 @ a2 in
	List.fold_left aux2 (SAF.affine AF.plusInfinity, []) (List.map aux (SAF.decompose s))
	(* assertT << 'x <= min('a;'b) >> thenAT
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
   if compare b fieldUnit < 0 then
		let result=AF.scale (inv (sub fieldUnit b)) c in
		(result, [assertT (mk_ge_rat_term (VI.restore info x) (AF.term_of info result)) thenAT addHiddenLabelT "inffa case 0"])
		(* assertT <<'x >= result>> thenAT
			'x>='y <-->
			(1-'b)*'x >= (1-'b)*'y <-->
			'x >= 'b*'x + (1-'b)*'y <-->(normalize) 'x >= 'f *)
	else
      if (compare b fieldUnit = 0) && (AF.isNumber c) then
			let cmp=compare (AF.coef c AF.constvar) fieldZero in
			if cmp>0 then
				(AF.plusInfinity, [assertT (mk_ge_rat_term (VI.restore info x) (AF.term_of info f)) thenAT addHiddenLabelT "inffa case 100"])
			else
				if cmp=0 then
					(f,[assertT (mk_ge_rat_term (VI.restore info x) (AF.term_of info f)) thenAT addHiddenLabelT "inffa case 1010"])
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

let inff' info (x:AF.vars) (s:SAF.saf) =
	let aux f = let (result,actions)=inffa info x f in (SAF.affine result, actions) in
	let aux2 (f1,a1) (f2,a2) = SAF.max f1 f2, a1 @ a2 in
	List.fold_left aux2 (SAF.affine AF.minusInfinity, []) (List.map aux (SAF.decompose s))
	(* assertT << 'x >= max('a;'b) >> thenAT
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
						let r0=SACS.upper c v in
						let r0_term=SAF.term_of info r0 in
						let v_term=VI.restore info v in
						let a0=[assertT (mk_ge_rat_term r0_term v_term) thenAT addHiddenLabelT "supa 1001"] in
						let r1,a1=sup info c r0 (CS.add h v) in
						let a11=[assertT (mk_ge_rat_term (SAF.term_of info r1) v_term) thenAT geTransitive r0_term] in
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
			let a01=[assertT (mk_ge_rat_term (SAF.term_of info f') (AF.term_of info f)) thenAT addHiddenLabelT "supa 11"] in
			if SAF.occurs v b' then
				let r1,a1=sup info c f' h in
				(r1,a1@(a01@a0))
			else
				let r1,a1=sup info c scaled_v h in
				(SAF.add r1 b',a1@(a01@a0))

and sup' info (c:SACS.sacs) (s:SAF.saf) (h:CS.t) =
	let aux f = supa info c f h in
	let aux2 (f1,a1) (f2,a2) = SAF.min f1 f2, a1 @ a2 in
   List.fold_left aux2 (SAF.affine AF.plusInfinity, []) (List.map aux (SAF.decompose s))

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
									let r0=SACS.lower c v in
									let r0_term=SAF.term_of info r0 in
									let v_term=VI.restore info v in
									let a0=[assertT (mk_ge_rat_term v_term r0_term) thenAT addHiddenLabelT "infa 1001"] in
									let r1,a1=inf info c r0 (CS.add h v) in
									let a11=[assertT (mk_ge_rat_term v_term (SAF.term_of info r1)) thenAT geTransitive r0_term] in
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
					let a01=[assertT (mk_ge_rat_term (AF.term_of info f) (SAF.term_of info f')) thenAT addHiddenLabelT "infa 11"] in
					if SAF.occurs v b' then
						begin
							if !debug_supinf_trace then
								(printf "case 110"; eflush stdout);
							let r1,a1=inf info c f' h in
							r1, a1@(a01@a0)
						end
					else
						begin
							if !debug_supinf_trace then
								(printf "case 111"; eflush stdout);
							let r1,a1=inf info c scaled_v h in
							(SAF.add r1 b', a1@(a01@a0))
						end
				end
		end

and inf' info (c:SACS.sacs) (s:SAF.saf) (h:CS.t) =
	let aux f = infa info c f h in
	let aux2 (f1,a1) (f2,a2) = SAF.max f1 f2, a1 @ a2 in
   List.fold_left aux2 (SAF.affine AF.minusInfinity, []) (List.map aux (SAF.decompose s))

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

let rec runListT = function
	[] -> idT
 | [tac] -> tac
 | hd::tl -> hd thenMT (runListT tl)

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
		runListT (List.rev (a1@a2)) thenMT
		(assertT (mk_ge_rat_term (SAF.term_of info sup') (SAF.term_of info inf')) thenAT (addHiddenLabelT "final" thenT geTransitive (VI.restore info 1)))
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
sequent { <H>; ge_rat{'a; rat{0;1}}; ge_rat{'b; rat{0;1}}; ge_rat{rat{-1;1}; add_rat{'a; 'b}} >- "assert"{bfalse} }
