extends Itt_equal
extends Itt_rfun
extends Itt_logic
extends Itt_bool
extends Itt_int_ext

open Printf
open Lm_debug
open Opname
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
			Number (a1,a2), Number (b1,b2) -> Number(mult_num a1 b2, mult_num a2 b1)
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

	val print : af -> unit
	val print_var : vars -> unit
end

module MakeAF(BField : BoundFieldSig)
	: AF_Sig with type bfield=BField.bfield and type vars=VarType.t =
struct
	module Monom=MakeMonom(BField)
	module Table=Lm_splay_table.MakeTable(Monom)

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

	val print : saf -> unit
end

module MakeSAF(BField : BoundFieldSig)(AF : AF_Sig  with type bfield=BField.bfield)
	: SAF_Sig with type bfield=BField.bfield and type vars=AF.vars and type af=AF.af =
struct
	open BField
	open AF

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
				else if cmp=0 then Affine(mk_number(fieldZero))
				else Min (List.map (scale k) l)
		 | Max l ->
				let cmp=compare k fieldZero in
				if cmp<0 then Min (List.map (scale k) l)
				else if cmp=0 then Affine(mk_number(fieldZero))
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

open RationalBoundField

let suppa' (x:AF.vars) (f:AF.af) =
	if !debug_supinf_trace then
		(printf"suppa: ";	AF.print_var x; AF.print f; eflush stdout);
	let b = AF.coef f x in
	let c = AF.remove f x in
   if compare b fieldUnit < 0 then
		AF.scale (inv (sub fieldUnit b)) c
	else
      if (compare b fieldUnit = 0) && (AF.isNumber c) then
			let cmp=compare (AF.coef c AF.constvar) fieldZero in
			if cmp<0 then
				AF.minusInfinity
			else
				if cmp=0 then
					f
				else
					AF.plusInfinity
		else
			AF.plusInfinity

let suppa x f =
	let result=suppa' x f in
	if !debug_supinf_steps then
		begin
			printf"suppa<: "; AF.print_var x; printf"<="; AF.print f; eflush stdout;
			printf"suppa>: "; AF.print_var x; printf"<="; AF.print result; eflush stdout;
		end;
	result

let supp' (x:AF.vars) (s:SAF.saf) =
	List.fold_left SAF.min (SAF.affine AF.plusInfinity) (List.map (fun f -> SAF.affine (suppa x f)) (SAF.decompose s))

let supp x s =
	let result=supp' x s in
	if !debug_supinf_steps then
		begin
			printf"supp<: "; AF.print_var x; printf"<="; SAF.print s; eflush stdout;
			printf"supp>: "; AF.print_var x; printf"<="; SAF.print result; eflush stdout;
		end;
	result

let inffa' (x:AF.vars) (f:AF.af) =
	if !debug_supinf_trace then
		(printf"inffa: ";	AF.print_var x; printf" "; AF.print f; eflush stdout);
	let b = AF.coef f x in
	let c = AF.remove f x in
   if compare b fieldUnit < 0 then
		AF.scale (inv (sub fieldUnit b)) c
	else
      if (compare b fieldUnit = 0) && (AF.isNumber c) then
			let cmp=compare (AF.coef c AF.constvar) fieldZero in
			if cmp>0 then
				AF.plusInfinity
			else
				if cmp=0 then
					f
				else
					AF.minusInfinity
		else
			AF.minusInfinity

let inffa x f =
	let result=inffa' x f in
	if !debug_supinf_steps then
		begin
			printf"inffa<: "; AF.print f; printf"<="; AF.print_var x; eflush stdout;
			printf"inffa>: "; AF.print result; printf"<="; AF.print_var x; eflush stdout;
		end;
	result

let inff' (x:AF.vars) (s:SAF.saf) =
	List.fold_left SAF.max (SAF.affine AF.minusInfinity) (List.map (fun f -> SAF.affine (inffa x f)) (SAF.decompose s))

let inff x s =
	let result=inff' x s in
	if !debug_supinf_steps then
		begin
			printf"inff<: "; SAF.print s; printf"<="; AF.print_var x; eflush stdout;
			printf"inff>: "; SAF.print result; printf"<="; AF.print_var x; eflush stdout;
		end;
	result

let rec supa (c:SACS.sacs) (f:AF.af) (h:CS.t) =
	if !debug_supinf_trace then
		begin
			printf"supa:\n";	SACS.print c; eflush stdout;
			AF.print f; eflush stdout;
			CS.print h; eflush stdout
		end;
	let (r,v,b) = AF.split f in
	if v==AF.constvar then SAF.affine (AF.mk_number r)
	else
		let af_v=AF.mk_var v in
		let saf_v = SAF.affine af_v in
		if (AF.isNumber b) && (compare (AF.coef b AF.constvar) fieldZero =0) then
			if compare r fieldUnit = 0 then
				if CS.mem h v then saf_v
				else supp v (sup c (SACS.upper c v) (CS.add h v))
			else
				if compare r fieldZero < 0 then
					SAF.scale r (inf c saf_v h)
				else
					SAF.scale r (sup c saf_v h)
		else
         let b' = sup c (SAF.affine b) (CS.add h v) in
			if SAF.occurs v b' then
				sup c (SAF.add (SAF.affine (AF.scale r af_v)) b') h
			else
				SAF.add (sup c (SAF.affine (AF.scale r af_v)) h) b'

and sup' (c:SACS.sacs) (s:SAF.saf) (h:CS.t) =
   List.fold_left SAF.min (SAF.affine AF.plusInfinity) (List.map (fun f -> supa c f h) (SAF.decompose s))

and sup (c:SACS.sacs) (s:SAF.saf) (h:CS.t) =
	let result=sup' c s h in
	if !debug_supinf_steps then
		begin
			printf"sup: "; SAF.print s; printf"<="; SAF.print result; eflush stdout;
		end;
	result

and infa (c:SACS.sacs) (f:AF.af) (h:CS.t) =
	if !debug_supinf_trace then
		begin
			printf"infa:\n";
			SACS.print c; eflush stdout;
			AF.print f; eflush stdout;
			CS.print h; eflush stdout
		end;
   let (r,v,b) = AF.split f in
	if v==AF.constvar then
		begin
			if !debug_supinf_trace then
				(printf "case 0"; eflush stdout);
			SAF.affine (AF.mk_number r)
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
									saf_v
								end
							else
								begin
									if !debug_supinf_trace then
										(printf "case 1001"; eflush stdout);
									inff v (inf c (SACS.lower c v) (CS.add h v))
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
									SAF.scale r (sup c saf_v h)
								end
							else
								begin
									if !debug_supinf_trace then
										(printf "case 1011"; eflush stdout);
									SAF.scale r (inf c saf_v h)
								end
						end
				end
			else
				begin
					if !debug_supinf_trace then
						(printf "case 11"; eflush stdout);
					let b' = inf c (SAF.affine b) (CS.add h v) in
					if SAF.occurs v b' then
						begin
							if !debug_supinf_trace then
								(printf "case 110"; eflush stdout);
							inf c (SAF.add (SAF.affine (AF.scale r af_v)) b') h
						end
					else
						begin
							if !debug_supinf_trace then
								(printf "case 111"; eflush stdout);
							SAF.add (inf c (SAF.affine (AF.scale r af_v)) h) b'
						end
				end
		end

and inf' (c:SACS.sacs) (s:SAF.saf) (h:CS.t) =
   List.fold_left SAF.max (SAF.affine AF.minusInfinity) (List.map (fun f -> infa c f h) (SAF.decompose s))

and inf (c:SACS.sacs) (s:SAF.saf) (h:CS.t) =
	let result=inf' c s h in
	if !debug_supinf_steps then
		begin
			printf"inf: "; SAF.print result; printf"<="; SAF.print s; eflush stdout;
		end;
	result

let collect gl =
   let sh = (explode_sequent gl).sequent_hyps in
   let aux' h = match h with HypBinding (_,t) | Hypothesis t -> t
    | Context (_,_,_) -> xnil_term in
   let shl = List.map aux' (SeqHyp.to_list sh) in
	List.filter is_ge_term shl

module Var =
struct
	type t = term
	let equal = alpha_equal
	let hash = Hashtbl.hash
end

module Var2Index =
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
end

let monom2af var2index t =
	if is_mul_term t then
		let t1,t2=dest_mul t in
		if is_number_term t1 then
			let k=dest_number t1 in
			let i=Var2Index.lookup var2index t2 in
			let f=AF.mk_var i in
			AF.scale (Number (k, num1)) f
		else
			let i=Var2Index.lookup var2index t in
			AF.mk_var i
	else
		if is_number_term t then
			AF.mk_number (Number(dest_number t, num1))
		else
			let i=Var2Index.lookup var2index t in
			AF.mk_var i

let rec linear2af var2index t =
	if is_add_term t then
		let t1,t2=dest_add t in
		let f1=linear2af var2index t1 in
		let f2=linear2af var2index t2 in
		AF.add f1 f2
	else
		monom2af var2index t

let ge2af var2index t =
	let left,right=dest_ge t in
	let f1=linear2af var2index left in
	let f2=linear2af var2index right in
	let neg_f2=AF.scale (neg fieldUnit) f2 in
	AF.add f1 neg_f2

let make_sacs var2index p =
   let g = Sequent.goal p in
   let l = collect g in
	let afs=List.map (ge2af var2index) l in
	List.fold_left SACS.addConstr SACS.empty afs

let testT = funT (fun p ->
	let var2index = Var2Index.create 13 in
	let constrs=make_sacs var2index p in
	printf "Vars:\n";
	Var2Index.print var2index;
	printf "SACS:\n"; SACS.print constrs;
	eflush stdout;
	begin
		let saf'=SAF.affine (AF.mk_var 1) in
		let sup'=sup constrs saf' CS.empty in
		let inf'=inf constrs saf' CS.empty in
		printf "start=";SAF.print saf'; eflush stdout;
		printf"sup=";SAF.print sup'; eflush stdout;
		printf"inf=";SAF.print inf'; eflush stdout;
		SAF.print inf'; printf "<="; SAF.print saf'; printf "<="; SAF.print sup'; eflush stdout;
	end;
	idT
)

interactive test 'H 'a 'b 'c :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H> >- 'c in int } -->
sequent { <H>; x: ('a >= ('b +@ 1));
                     t: ('c >= ('b +@ 3));
                     u: ('b >= ('a +@ 0))
                >- "assert"{bfalse} }

interactive test2 'H 'a 'b 'c :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H> >- 'c in int } -->
sequent { <H>; 'a >= 0; 'b >= 0; -1 >= 'a +@ 'b >- "assert"{bfalse} }

