extends Itt_equal
extends Itt_rfun
extends Itt_logic
extends Itt_bool
extends Itt_int_ext
extends Itt_int_arith
(*extends Itt_rat
extends Itt_rat2
*)
open Lm_debug
open Lm_printf

open Supinf

open Simple_print
open Basic_tactics

open Itt_equal
open Itt_struct
open Itt_bool

open Itt_int_base
open Itt_int_ext
open Itt_int_arith
(*open Itt_supinf*)

let _ = show_loading "Loading Itt_omega%t"

let debug_omega =
   create_debug (**)
      { debug_name = "omega";
        debug_description = "Itt_omega debug messages";
        debug_value = false
      }

let debug_arith_dtactic =
   create_debug (**)
      { debug_name = "arith_dtactic";
        debug_description = "Itt_int_arith.arithT: display operations of conversion to >=";
        debug_value = false
      }

let debug_rewrite =
   create_debug (**)
      { debug_name = "rewrite";
        debug_description = "Itt_omega debug messages";
        debug_value = false
      }

let debug_refine =
   create_debug (**)
      { debug_name = "refine";
        debug_description = "Itt_omega debug messages";
        debug_value = false
      }

module type RingSig =
sig
   type ring

   val ringUnit : ring
   val ringZero : ring
	val abs : ring -> ring
   val mul : ring -> ring -> ring
	val div : ring -> ring -> ring
	val rem : ring -> ring -> ring
   val add : ring -> ring -> ring
   val neg : ring -> ring
   val sub : ring -> ring -> ring
   val compare : ring -> ring -> int
	val isNegative : ring -> bool
	val gcd : ring -> ring -> ring
	val list_gcd : ring list -> ring

   val term_of : ring -> term
   val mul_term : term -> term -> term
   val add_term : term -> term -> term
   val neg_term : term -> term
   val sub_term : term -> term -> term
   val ge_term : term -> term -> term

   val print : out_channel -> ring -> unit
end

module VarType =
struct
   type t=int
   let compare a b = a-b

   let print out v =
      if v>0 then fprintf out "v%i" v
      else if v=0 then fprintf out "1"
      else raise (Invalid_argument "Variable index should be non-negative")
end

module Var2Index(Ring : RingSig) =
struct
	module Var =
	struct
		type t = term
		let equal = alpha_equal
		let hash = Hashtbl.hash
	end

   module Table=Hashtbl.Make(Var)

   type t=int ref * int Table.t

   let create n = (ref 0, Table.create n)

	let length (r,_) = !r

   let lookup (info:t) v =
      let count, table = info in
      if Table.mem table v then
         Table.find table v
      else
         let index=(!count)+1 in
         begin
            Table.add table v index;
            count:=index;
            index
         end

   let print out info =
      let count,table=info in
      let aux k d = fprintf out "%a ->v%i%t" print_term k d eflush in
      (*printf "count=%i%t" !count eflush;*)
      Table.iter aux table

   let invert ((count,table) : t) =
      let ar=Array.make !count (Ring.term_of Ring.ringZero) in
      let aux key data = (ar.(data-1)<-key) in
      Table.iter aux table;
      ar

   let restore inverted index =
      if index=0 then
         Ring.term_of (Ring.ringUnit)
      else
         inverted.(index-1)
end

module MakeMonom(Ring : RingSig) =
struct
   type elt = VarType.t
   type data = Ring.ring

   let compare = VarType.compare

   let print out (v:elt) (kl: data list) =
      match kl with
         [k] -> Ring.print out k; (*printf"*";*) VarType.print out v
       | _ -> raise (Invalid_argument "More than one coefficient is associated with one variable")

   let append l1 l2 =
      match l1,l2 with
         [],[] -> [Ring.ringZero]
       | [],[a] -> [a]
       | [a],[] -> [a]
       | [a],[b] -> [Ring.add a b]
       | _,_ -> raise (Invalid_argument "Addition non-trivial lists are not supported")

end

module type AF_Sig =
sig
   type ring
   type vars=int
   type af

   val constvar : vars

	val dim : af -> int
   val mk_number: int -> ring -> af
   val mk_var: int -> vars -> af
	val grow: int -> af -> af
   val scale: ring -> af -> af
	val div: af -> ring -> af
   val add: af -> af -> af
	val sub: af -> af -> af
   val add_scaled: af -> ring -> af -> af
	val sub_scaled: af -> ring -> af -> af
	val sub_number : af -> ring -> af

   val coef: af -> vars -> ring
   val get: af -> vars -> ring
   val remove: af -> vars -> af
   val split: af -> (ring * vars * af)
	val any_var : af -> vars
   val isNumber: af -> bool
	val gcd: af -> ring

	val value_of : af -> ring
   val term_of : (term array) -> af -> term

   val print : out_channel -> af -> unit
   val print_var : out_channel -> vars -> unit
end

module MakeAF(Ring : RingSig)
   : AF_Sig with
	type ring=Ring.ring and
	type vars=VarType.t =
struct
   module Monom=MakeMonom(Ring)
   module Table=Lm_splay_table.MakeTable(Monom)
   module VI=Var2Index(Ring)

   type ring=Ring.ring
   type vars=Monom.elt

   type af=Table.t

	let constvar = 0

   let print_var = VarType.print

   let print out f =
      let aux key data =
         fprintf out "+"; Monom.print out key [data]
      in
      fprintf out "("; Table.iter aux f; fprintf out ")%t" flush

   let mk_number _ k =
		Table.add Table.empty constvar k

   let mk_var _ v = Table.add Table.empty v Ring.ringUnit

	let grow _ f = f

	let dim f = pred (Table.length f)

   let scale_aux k v d =
      Ring.mul k d

   let scale k f =
      if Ring.compare k Ring.ringZero =0 then Table.empty
      else if Ring.compare k Ring.ringUnit =0 then f
      else Table.map (scale_aux k) f

   let coef f v =
      try Table.find f v
      with Not_found -> Ring.ringZero

	let get f v = coef f v

	let add_aux v k f =
		let k' = coef f v in
		Table.replace f v [Ring.add k' k]

	let add f1 f2 =
		Table.fold_map add_aux f1 f2

	let sub_aux v k f =
		let k' = coef f v in
		Table.replace f v [Ring.sub k' k]

	let sub f1 f2 =
		Table.fold_map sub_aux f1 f2
(*
		let neg_f2 = scale (Ring.neg Ring.ringUnit) f2 in
		add f1 neg_f2
*)

	let add_scaled_aux c v k f =
		let k' = coef f v in
		Table.replace f v [Ring.add k' (Ring.mul c k)]

	let add_scaled f1 c f2 =
		Table.fold_map (add_scaled_aux c) f1 f2

	let sub_scaled_aux c v k f =
		let k' = coef f v in
		Table.replace f v [Ring.sub k' (Ring.mul c k)]

	let sub_scaled f1 c f2 =
		Table.fold_map (sub_scaled_aux c) f1 f2

	let sub_number f k =
		let k' = Table.find f constvar in
		Table.replace f constvar [Ring.sub k' k]
(*		let k' = Table.find f constvar in
		let f' = Table.remove f constvar in
		Table.add f' constvar (Ring.sub k' k)
*)

	let gcd f =
		let r = ref Ring.ringZero in
		let aux v k =
			if v=constvar then
				()
			else
				r:=Ring.gcd !r k
		in
		Table.iter aux f;
		!r

	let div f k = Table.map (fun v c -> Ring.div c k) f

   let remove f vs = Table.remove f vs

   let rec split f =
		if Table.is_empty f then
			(Ring.ringZero, constvar, mk_number 0 Ring.ringZero)
		else
			let v, coefs, rest = Table.deletemax f in
			match coefs with
				[c] ->
					if v!=constvar && (Ring.compare c Ring.ringZero =0) then
						split rest
					else
						(c,v,rest)
			 | _ -> raise (Invalid_argument "More than one coefficient associated with a variable")

	let any_var f =
		let c,v,_ = split f in
		v

   let isNumber f =
      let test=ref true in
      let aux v c =
         if v<>constvar && Ring.compare c Ring.ringZero <>0 then
            test:=false
      in
      Table.iter aux f;
      !test

	let value_of f =
		if isNumber f then
			coef f constvar
		else
			begin
				eprintf "AF.value_of: applied to a non-constant form %a" print f;
				raise (Invalid_argument "AF.value_of: applied to a non-constant form")
			end

   let term_of_monom info k v =
      if v=constvar then
         Ring.term_of k
      else
         Ring.mul_term (Ring.term_of k) (VI.restore info v)

   let rec term_of_aux info = function
      [] -> Ring.term_of Ring.ringZero
    | [(v,k)] -> term_of_monom info k v
    | (v,k)::tl -> Ring.add_term (term_of_monom info k v) (term_of_aux info tl)

   let rec term_of info f =
      let l=Table.list_of f in
      let aux = function
         (k,[d]) -> (k,d)
       | (k,[]) -> raise (Invalid_argument "MakeAF.term_of - empty data list linked to a key in list_of")
       | (k,_) -> raise (Invalid_argument "MakeAF.term_of - more than one data item per key in list_of")
      in
      let aux2 (k,d) = if Ring.compare d Ring.ringZero = 0 then false else true in
      term_of_aux info (List.filter aux2 (List.map aux l))

end

module MakeArrayAF(Ring : RingSig)
   : AF_Sig with
	type ring=Ring.ring and
	type vars=VarType.t =
struct
   module Monom=MakeMonom(Ring)
   module VI=Var2Index(Ring)

   type ring=Ring.ring
   type vars=Monom.elt

   type af=ring array

	let constvar = 0

   let print_var = VarType.print

   let print out f =
      let aux key data =
         fprintf out "+"; Monom.print out key [data]
      in
      fprintf out "("; Array.iteri aux f; fprintf out ")%t" flush

	let dim f = pred (Array.length f)

   let mk_number n k =
		Array.init (succ n) (fun i -> if i=constvar then k else Ring.ringZero)

   let mk_var n v =
		Array.init (succ n) (fun i -> if i=v then Ring.ringUnit else Ring.ringZero)

	let grow n f =
		let old = Array.length f in
		if n > old then
			Array.init n (fun i -> if i<old then f.(i) else Ring.ringZero)
		else
			f

   let scale_aux k d =
      Ring.mul k d

   let scale k f =
		Array.map (scale_aux k) f

	let div f k =
		Array.map (fun x -> Ring.div x k) f

   let coef f v =
		f.(v)

	let get f i =
		if i>= Array.length f then
			Ring.ringZero
		else
			f.(i)

   let add f1 f2 =
		if Array.length f1 > Array.length f2 then
			Array.mapi (fun i k1 -> Ring.add k1 (get f2 i)) f1
		else
			Array.mapi (fun i k2 -> Ring.add k2 (get f1 i)) f2

   let add_scaled f1 c f2 =
		if Array.length f1 > Array.length f2 then
			Array.mapi (fun i k1 -> Ring.add k1 (Ring.mul c (get f2 i))) f1
		else
			Array.mapi (fun i k2 -> Ring.add (Ring.mul c k2) (get f1 i)) f2

	let sub f1 f2 =
		if Array.length f1 > Array.length f2 then
			Array.mapi (fun i k1 -> Ring.sub k1 (get f2 i)) f1
		else
			Array.mapi (fun i k2 -> Ring.sub (get f1 i) k2) f2

	let sub_scaled f1 c f2 =
		if Array.length f1 > Array.length f2 then
			Array.mapi (fun i k1 -> Ring.sub k1 (Ring.mul c (get f2 i))) f1
		else
			Array.mapi (fun i k2 -> Ring.sub (get f1 i) (Ring.mul c k2)) f2

	let sub_number f k =
		f.(constvar) <- Ring.sub f.(constvar) k;
		f

   let remove f v =
		f.(v) <- Ring.ringZero;
		f

	let rec gcd_aux f acc i =
		if i < Array.length f then
			gcd_aux f (Ring.gcd acc f.(i)) (succ i)
		else
			acc

	(*let gcd f = Array.fold_left Ring.gcd Ring.ringZero f*)
	let gcd f = gcd_aux f Ring.ringZero (succ constvar)

	exception Found of int

	let split f =
		let n = Array.length f in
		try
			for i=(pred n) downto 1 do
				if Ring.compare f.(i) Ring.ringZero <> 0 then
					raise (Found i)
			done;
			(f.(constvar), constvar, Array.make n Ring.ringZero)
		with
			Found i ->
				let f' = Array.init n (fun j -> if i=j then Ring.ringZero else f.(j)) in
				(f.(i), i, f')

	let any_var f =
		let n = Array.length f in
		try
			for i=(pred n) downto 1 do
				if Ring.compare f.(i) Ring.ringZero <> 0 then
					raise (Found i)
			done;
			constvar
		with
			Found i -> i

   let isNumber f =
      let test=ref true in
		for i=1 to Array.length f - 1 do
         if Ring.compare f.(i) Ring.ringZero <>0 then
            test:=false
		done;
      !test

	let value_of f =
		if isNumber f then
			coef f constvar
		else
			begin
				eprintf "AF.value_of: applied to a non-constant form %a" print f;
				raise (Invalid_argument "AF.value_of: applied to a non-constant form")
			end

   let term_of_monom info k v =
      if v=constvar then
         Ring.term_of k
      else
         Ring.mul_term (Ring.term_of k) (VI.restore info v)

	let rec term_of_aux info f n t i =
		if i >= n then
			t
		else
			let k = f.(i) in
			if Ring.compare k Ring.ringZero = 0 then
				term_of_aux info f n t (succ i)
			else
				let t' = Ring.add_term t (term_of_monom info k i) in
				term_of_aux info f n t' (succ i)

   let rec term_of info f =
		term_of_aux info f (Array.length f) (Ring.term_of f.(constvar)) 1

end

module MakeDebugAF(Ring : RingSig)
	(AF1: AF_Sig with type ring=Ring.ring) (* less trusted module *)
	(AF2: AF_Sig with type ring=Ring.ring) (* more trusted module *)
   : AF_Sig with
	type ring=Ring.ring and
	type vars=VarType.t =
struct
   module Monom=MakeMonom(Ring)
   module VI=Var2Index(Ring)

   type ring=Ring.ring
   type vars=Monom.elt

   type af=AF1.af * AF2.af

	let constvar = 0

   let print_var = VarType.print

   let print out (f1,f2) =
		fprintf out "AF1: ";
		AF1.print out f1;
		fprintf out " AF2: ";
		AF2.print out f2

	let dim (f1,f2) =
		let d1 = AF1.dim f1 in
		let d2 = AF2.dim f2 in
		max d1 d2

	let equal f1 f2 =
		let d = dim (f1,f2) in
		let r = ref true in
		for i=0 to d do
			let k1=AF1.get f1 i in
			let k2=AF2.get f2 i in
			if Ring.compare k1 k2 <> 0 then
				begin
					r := false;
					eprintf "MakeDebugAF.equal %i: %a %a@." i Ring.print k1 Ring.print k2
				end
		done;
		!r

   let mk_number n k =
		let f1 = AF1.mk_number n k in
		let f2 = AF2.mk_number n k in
		if equal f1 f2 then (f1,f2)
		else raise (Invalid_argument "MakeDebugAF.mk_number")

   let mk_var n v =
		let f1 = AF1.mk_var n v in
		let f2 = AF2.mk_var n v in
		if equal f1 f2 then (f1,f2)
		else raise (Invalid_argument "MakeDebugAF.mk_var")

	let grow n (f1,f2) =
		let f1 = AF1.grow n f1 in
		let f2 = AF2.grow n f2 in
		if equal f1 f2 then (f1,f2)
		else raise (Invalid_argument "MakeDebugAF.grow")

   let scale k (f1,f2) =
		let f1 = AF1.scale k f1 in
		let f2 = AF2.scale k f2 in
		if equal f1 f2 then (f1,f2)
		else raise (Invalid_argument "MakeDebugAF.scale")

	let div (f1,f2) k =
		let f1 = AF1.div f1 k in
		let f2 = AF2.div f2 k in
		if equal f1 f2 then (f1,f2)
		else raise (Invalid_argument "MakeDebugAF.div")

   let coef (f1,f2) v =
		let c1 = AF1.coef f1 v in
		let c2 = AF2.coef f2 v in
		if Ring.compare c1 c2 = 0 then c1
		else
			begin
				eprintf "MakeDebugAF.coef\n%a %i -> %a\n%a %i -> %a@."
					AF1.print f1 v Ring.print c1
					AF2.print f2 v Ring.print c2;
				raise (Invalid_argument "MakeDebugAF.coef")
			end

   let get (f1,f2) v =
		let c1 = AF1.get f1 v in
		let c2 = AF2.get f2 v in
		if Ring.compare c1 c2 = 0 then c1
		else
			begin
				eprintf "MakeDebugAF.get\n%a %i -> %a\n%a %i -> %a@."
					AF1.print f1 v Ring.print c1
					AF2.print f2 v Ring.print c2;
				raise (Invalid_argument "MakeDebugAF.get")
			end

   let add (f11,f12) (f21,f22) =
		let f1 = AF1.add f11 f21 in
		let f2 = AF2.add f12 f22 in
		if equal f1 f2 then (f1,f2)
		else
			begin
				eprintf "MakeDebugAF.add\n%a %a = %a\n%a %a = %a@."
				AF1.print f11 AF1.print f21 AF1.print f1
				AF2.print f12 AF2.print f22 AF2.print f2;
				raise (Invalid_argument "MakeDebugAF.add")
			end

   let add_scaled (f11,f12) c (f21,f22) =
		let f1 = AF1.add_scaled f11 c f21 in
		let f2 = AF2.add_scaled f12 c f22 in
		if equal f1 f2 then (f1,f2)
		else
			begin
				eprintf "MakeDebugAF.add_scaled\n%a %a = %a\n%a %a = %a@."
				AF1.print f11 AF1.print f21 AF1.print f1
				AF2.print f12 AF2.print f22 AF2.print f2;
				raise (Invalid_argument "MakeDebugAF.add_scaled")
			end

	let sub (f11,f12) (f21,f22) =
		let f1 = AF1.sub f11 f21 in
		let f2 = AF2.sub f12 f22 in
		if equal f1 f2 then (f1,f2)
		else
			begin
				eprintf "MakeDebugAF.sub\n%a %a = %a\n%a %a = %a@."
				AF1.print f11 AF1.print f21 AF1.print f1
				AF2.print f12 AF2.print f22 AF2.print f2;
				raise (Invalid_argument "MakeDebugAF.sub")
			end

	let sub_scaled (f11,f12) c (f21,f22) =
		let f1 = AF1.sub_scaled f11 c f21 in
		let f2 = AF2.sub_scaled f12 c f22 in
		if equal f1 f2 then (f1,f2)
		else
			begin
				eprintf "MakeDebugAF.sub_scaled\n%a %a = %a\n%a %a = %a@."
				AF1.print f11 AF1.print f21 AF1.print f1
				AF2.print f12 AF2.print f22 AF2.print f2;
				raise (Invalid_argument "MakeDebugAF.sub_scaled")
			end

	let sub_number (f1,f2) k =
		let f1 = AF1.sub_number f1 k in
		let f2 = AF2.sub_number f2 k in
		if equal f1 f2 then (f1,f2)
		else
		raise (Invalid_argument "MakeDebugAF.sub_number")

   let remove (f1,f2) v =
		let f1 = AF1.remove f1 v in
		let f2 = AF2.remove f2 v in
		if equal f1 f2 then (f1,f2)
		else raise (Invalid_argument "MakeDebugAF.remove")

	let gcd (f1,f2) =
		let r1 = AF1.gcd f1 in
		let r2 = AF2.gcd f2 in
		if Ring.compare r1 r2 = 0 then
			r1
		else
			begin
				eprintf "MakeDebugAF.gcd:\n%a -> %a\n%a -> %a@." AF1.print f1 Ring.print r1 AF2.print f2 Ring.print r2;
				raise (Invalid_argument "MakeDebugAF.gcd")
			end

	exception Found of int

	let split (f1,f2) =
		let c1, v, f1' = AF1.split f1 in
		let c2 = AF2.coef f2 v in
		let f2' = AF2.remove f2 v in
		if (equal f1' f2') && (Ring.compare c1 c2 = 0) then
			(c1,v,(f1',f2'))
		else
			begin
				eprintf "MakeDebugAF.split:\n%a -> %a %i %a\n%a -> %a %i %a@."
					AF1.print f1 Ring.print c1 v AF1.print f1'
					AF2.print f2 Ring.print c2 v AF2.print f2';
				raise (Invalid_argument "MakeDebugAF.split")
			end

	let any_var (f1,f2) =
		let v = AF1.any_var f1 in
		let c1 = AF1.coef f1 v in
		let c2 = AF2.coef f2 v in
		if Ring.compare c1 c2 = 0 then
			v
		else
			begin
				eprintf "MakeDebugAF.any_var:\n%a -> %a %i\n%a -> %a %i@."
					AF1.print f1 Ring.print c1 v
					AF2.print f2 Ring.print c2 v;
				raise (Invalid_argument "MakeDebugAF.any_var")
			end

   let isNumber (f1,f2) =
		let r1 = AF1.isNumber f1 in
		let r2 = AF2.isNumber f2 in
		if r1 = r2 then
			r1
		else
			begin
				eprintf "MakeDebugAF.isNumber:\n%a -> %b\n%a -> %b@." AF1.print f1 r1 AF2.print f2 r2;
				raise (Invalid_argument "MakeDebugAF.isNumber")
			end

	let value_of (f1,f2) =
		let r1 = AF1.value_of f1 in
		let r2 = AF2.value_of f2 in
		if Ring.compare r1 r2 = 0 then
			r1
		else
			begin
				eprintf "MakeDebugAF.value_of:\n%a -> %a\n%a->%a@." AF1.print f1 Ring.print r1 AF2.print f2 Ring.print r2;
				raise (Invalid_argument "MakeDebugAF.value_of")
			end

   let term_of info (f1,f2) =
		let _ = AF1.term_of info f1 in
		AF2.term_of info f2

end

module IntRing =
struct
   open Lm_num

   type ring = num

   let num0=num_of_int 0
   let num1=num_of_int 1
   let ringUnit = num1
   let ringZero = num0

   let print out a =
      fprintf out "(%s)" (string_of_num a)

	let isNegative n = (compare_num n num0 < 0)

	let isPositive n = (compare_num n num0 > 0)

	let abs = abs_num

   let mul a b = mult_num a b

   let add a b = add_num a b

   let sub a b = sub_num a b

   let neg a = sub num0 a

	let rem a b =
		let abs_b = abs_num b in
		let almost_mod = mod_num (abs_num a) abs_b in
		if compare_num a num0 >= 0 then
			almost_mod
		else
			if is_zero almost_mod then
				almost_mod
			else
				sub_num abs_b almost_mod

	let div a b =
		let a_rem_b = rem a b in
		let a' = sub a a_rem_b in
		let abs_div = div_num (abs_num a') (abs_num b) in
		if ((compare_num a num0) * (compare_num b num0)) >= 0 then
			abs_div
		else
			neg abs_div

	let sign_num a = num_of_int (compare_num a num0)

   let compare a b = compare_num a b

	let rec gcd_aux a b =
		if is_zero b then
			a
		else
			if eq_num b num1 then
				num1
			else
				let r = rem a b in
				gcd_aux b r

	let gcd a b =
		let a' = abs_num a in
		let b' = abs_num b in
		let c = compare_num a' b' in
		if c > 0 then
			gcd_aux a' b'
		else
			if c < 0 then
				gcd_aux b' a'
			else
				a'

	let rec list_gcd_aux c = function
		hd::tl ->
			list_gcd_aux (gcd c hd) tl
	 | [] -> c

	let list_gcd = function
		[i] -> abs_num i
	 | hd::tl -> list_gcd_aux hd tl
	 | [] -> raise (Invalid_argument "list_gcd was applied to empty list")

   let term_of a = mk_number_term a

   let add_term = mk_add_term
   let mul_term = mk_mul_term
   let neg_term = mk_minus_term
   let sub_term = mk_sub_term
   let ge_term = mk_ge_term
end

module Constraints
	(Ring: RingSig)
	(AF: AF_Sig with type ring = Ring.ring) =
struct
	module HashedAF =
	struct
		type t = Ring.ring array

		let equal = (=)

		let hash = Hashtbl.hash
	end

	module Hash = Hashtbl.Make(HashedAF)

	let create dim size = (dim, Hash.create size)

	let length (dim, table) = Hash.length table

	let get_key dim f =
		Array.init dim (fun i -> AF.coef f (succ i))

	let add_aux info key constr =
		let dim, table = info in
		let tree, f = constr in
		try
			let old_tree, old_f = Hash.find table key in
			let old_const = AF.coef old_f AF.constvar in
			if Ring.compare old_const (AF.coef f AF.constvar) > 0 then
				Hash.replace table key constr
			else
				()
		with
			Not_found ->
				Hash.add table key constr

	let add info constr =
		let dim, table = info in
		let tree, f = constr in
		let key = get_key dim f in
		add_aux info key constr

	let get (dim,table) key =
		Hash.find table key

	let iter f (dim,table) = Hash.iter f table

	let rec of_list_aux constrs = function
		hd::tl ->
			add constrs hd;
			of_list_aux constrs tl
	 | [] ->
			constrs

	let of_list dim l =
		let constrs = create dim (List.length l) in
		of_list_aux constrs l
(*
	let append constrs (d',table') =
		Hash.iter (fun k d -> add_aux constrs k d) table';
		constrs
*)

	let append_list constrs l =
		List.iter (fun (k,d) -> add_aux constrs k d) l

	let filter_aux predicate new_constrs k d =
		if predicate k d then
			add new_constrs d
		else
			()

	let filter predicate (dim,table) =
		let new_constrs = create dim (Hash.length table) in
		Hash.iter (filter_aux predicate new_constrs) table;
		new_constrs

	exception Found of HashedAF.t

	let find_aux predicate k d =
		if predicate k d then
			raise (Found k)
		else
			()

	let find predicate (dim,table) =
		try
			Hash.iter (find_aux predicate) table;
			raise Not_found
		with
			Found k -> k

	let fold f (dim,table) init_val =
		Hash.fold f table init_val

end

module R = IntRing
(*
module AF=MakeDebugAF(R)(MakeArrayAF(R))(MakeAF(R))
*)
module AF=MakeAF(R)
(*
module AF=MakeArrayAF(R)
*)
module VI=Var2Index(R)
module C=Constraints(IntRing)(AF)
open IntRing

module Var =
struct
	type t = term
	let equal = alpha_equal
	let hash = Hashtbl.hash
end

(*
let ge_normC = (addrC [Subterm 1] normalizeC) thenC (addrC [Subterm 2] normalizeC)

let relNorm_aux t =
	match explode_term t with
		<<'a = 'b in 'T>> ->
			(addrC [Subterm 2] normalizeC) thenC (addrC [Subterm 3] normalizeC)
	 | _ ->
			(addrC [Subterm 1] normalizeC) thenC (addrC [Subterm 2] normalizeC)

let relNormC = termC relNorm_aux
*)
let relNormC = allSubC normalizeC
let ge_normC = relNormC

let monom2af var2index t =
	match explode_term t with
		<<'t1 *@ 't2>> ->
         if is_number_term t1 then
            let i=VI.lookup var2index t2 in
				let n = VI.length var2index in
            let f=AF.mk_var n i in
					AF.scale (dest_number t1) f
         else
            let i=VI.lookup var2index t in
				let n = VI.length var2index in
					AF.mk_var n i
	 | <<number[i:n]>> ->
			let n = VI.length var2index in
         AF.mk_number n (dest_number t)
	 | _ ->
			let i=VI.lookup var2index t in
				let n = VI.length var2index in
				AF.mk_var n i

let rec linear2af var2index t =
	match explode_term t with
		<<'t1 +@ 't2>> ->
			let f1=linear2af var2index t1 in
			let f2=linear2af var2index t2 in
				AF.add f1 f2
	 | _ ->
			monom2af var2index t

let ge2af var2index (i,t) =
	let left,right=dest_ge t in
	let f1=linear2af var2index left in
	let f2=linear2af var2index right in
	let f=AF.sub f1 f2 in
	(i, f)

let apply_rewrite p conv t =
	let es={sequent_args= <<sequent_arg>>; sequent_hyps=(SeqHyp.of_list []); sequent_concl=t} in
	let s=mk_sequent_term es in
	let s'=Top_conversionals.apply_rewrite p (addrC concl_addr conv) s in
	TermMan.concl s'

let is_neg_number f =
	if AF.isNumber f then
		isNegative (AF.coef f AF.constvar)
	else
		false

(*********************************************************************
 * OMEGA
 *********************************************************************)

interactive_rw ge_mulMonoPosit_rw 'c :
   (0 < 'c) -->
   ('a in int) -->
   ('b in int) -->
   ('c in int) -->
   ('a >= 'b) <--> (('c *@ 'a) >= ('c *@ 'b))

interactive_rw ge_mulMonoPosit2_rw 'c :
   (0 < 'c) -->
   ('a in int) -->
   ('c in int) -->
   ('a >= 0) <--> (('c *@ 'a) >= 0)

let scaleC n = ge_mulMonoPosit2_rw n

interactive ge_scaleAndWeaken 'c 'd :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   [wf] sequent { <H> >- 'd in int } -->
   [aux] sequent { <H> >- 'd >= 0 } -->
   [aux] sequent { <H> >- 'd < 'c } -->
	sequent { <H> >- (('c *@ 'a) +@ 'd) >= ('c *@ 'b) } -->
   sequent { <H> >- 'a >= 'b }

interactive ge_scaleAndWeaken2 number[k:n] number[c:n] :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [aux] sequent { <H> >- number[c:n] >= 0 } -->
   [aux] sequent { <H> >- number[c:n] < number[k:n] } -->
	sequent { <H> >- ((number[k:n] *@ 'a) +@ number[c:n]) >= (number[k:n] *@ 'b) } -->
   sequent { <H> >- 'a >= 'b }

interactive ge_scaleAndWeaken3 number[k:n] number[c:n] :
   [wf] sequent { <H> >- 'a in int } -->
   [aux] sequent { <H> >- number[c:n] >= 0 } -->
   [aux] sequent { <H> >- number[c:n] < number[k:n] } -->
	sequent { <H> >- ((number[k:n] *@ 'a) +@ number[c:n]) >= 0 } -->
   sequent { <H> >- 'a >= 0 }

let scaleAndWeakenT k c = ge_scaleAndWeaken3 k c

interactive var_elim 'v :
	[wf] sequent { <H> >- 'a in int } -->
	[wf] sequent { <H> >- 'b in int } -->
	[wf] sequent { <H> >- 'v in int } -->
	[aux] sequent { <H> >- 0 < number[i:n] } -->
	[aux] sequent { <H> >- 0 < number[j:n] } -->
	sequent { <H> >- number[i:n] *@ 'v -@ 'a >= 0 } -->
	sequent { <H> >- 'b -@ number[j:n] *@ 'v >= 0 } -->
	sequent { <H> >- number[i:n] *@ 'b >= number[j:n] *@ 'a }

interactive_rw factor_out 'cleft 'tleft 'cright 'tright :
	('cleft in int) -->
	('tleft in int) -->
	('cright in int) -->
	('tright in int) -->
	('right in int) -->
	('left = 'right +@ ('cleft *@ 'tleft) -@ ('cright *@ 'tright) in int) -->
	('left >= 'right) <-->
	('cleft *@ 'tleft >= 'cright *@ 'tright)

interactive_rw factor_out2 number[l:n] 'tleft number[r:n] 'tright :
	('tleft in int) -->
	('tright in int) -->
	('left = (number[l:n] *@ 'tleft) -@ (number[r:n] *@ 'tright) in int) -->
	('left >= 0) <-->
	(number[l:n] *@ 'tleft >= number[r:n] *@ 'tright)

interactive var_elim2 'v number[l:n] 'tleft number[r:n] 'tright :
	[wf] sequent { <H> >- 'tleft in int } -->
	[wf] sequent { <H> >- 'tright in int } -->
	[wf] sequent { <H> >- 'v in int } -->
	[aux] sequent { <H> >- 0 < number[l:n] } -->
	[aux] sequent { <H> >- 0 < number[r:n] } -->
	sequent { <H> >- number[l:n] *@ 'v -@ 'tright >= 0 } -->
	sequent { <H> >- 'tleft -@ number[r:n] *@ 'v >= 0 } -->
	[aux] sequent { <H> >- 'left = (number[l:n] *@ 'tleft) -@ (number[r:n] *@ 'tright) in int } -->
	sequent { <H> >- 'left >= 0 }

let rec rev_flatten = function
   h :: t ->
      List.rev_append h (rev_flatten t)
 | [] ->
      []

let all_pairs l1 l2 =
	let pairs_lists = List.rev_map (fun x -> List.rev_map (fun y -> (y,x)) l1) l2 in
	rev_flatten pairs_lists

type omegaTree =
	Solve of (AF.vars * ring * omegaTree * AF.af * ring * omegaTree * AF.af)
 | Mul of (omegaTree * ring)
 | MulAndWeaken of (omegaTree * ring * ring)
 | Hyp of (int * int * int)

let norm constr =
	let tree, f = constr in
	let gcd = AF.gcd f in
	if compare gcd ringUnit <= 0 then
		constr
	else
		let c = rem (AF.coef f AF.constvar) gcd in
		let f' = AF.div f gcd in
		if compare c num0 = 0 then
			(Mul (tree, gcd), f')
		else
			(MulAndWeaken (tree, gcd, c), f')

let omega_aux v ((c1,t1,l),(c2,t2,u)) =
	let s = (Solve (v,c1,t1,l,c2,t2,u),	AF.sub_scaled (AF.scale c1 u) c2 l) in
	norm s

let rec compute_metric pool key (tree,f) =
	Array.iteri (fun v m -> pool.(v) <- add m (abs (AF.coef f (succ v)))) pool

let rec min_index_aux pool result current =
	if current = Array.length pool then
		result
	else
		let current_val = pool.(current) in
		if (compare pool.(result) current_val > 0) && (isPositive current_val) then
			min_index_aux pool current (succ current)
		else
			min_index_aux pool result (succ current)

let rec min_index pool current =
	if current = Array.length pool then
		0
	else
		if compare pool.(current) ringZero > 0 then
			min_index_aux pool current (succ current)
		else
			min_index pool (succ current)

let pick_var pool constrs =
	Array.fill pool 0 (Array.length pool) ringZero;
	C.iter (compute_metric pool) constrs;
	let result = min_index pool 0 in
	if compare pool.(result) ringZero > 0 then
		succ result
	else
		raise (RefineError ("omegaT", StringError "failed to find a contradiction - no variables left"))

(*
let pick_var_aux key (tree,f) =
	let v = AF.any_var f in
	v<>AF.constvar

let pick_var pool constrs =
	try
		let k = C.find pick_var_aux constrs in
		let tree, f = C.get constrs k in
		AF.any_var f
	with
		Not_found ->
			raise (RefineError ("omegaT", StringError "failed to find a contradiction - no variables left"))
*)

let rec get_bounds_aux v key constr (l,u,rest) =
	let tree, f = constr in
	let c = AF.coef f v in
	if isPositive c then
		let f' = AF.remove f v in
		(((c, tree, (AF.scale (neg ringUnit) f'))::l), u, rest)
	else
		if isNegative c then
			let f' = AF.remove f v in
			(l, ((neg c, tree, f')::u), rest)
		else
			(l, u, ((key, constr)::rest))

let get_bounds v constrs = C.fold (get_bounds_aux v) constrs ([],[],[])

(*
let print_constrs constrs =
	C.iter (fun k (tree,f) -> eprintf "%a@." AF.print f) constrs
*)

let print_constrs constrs =
	eprintf "%i constraints@." (C.length constrs)

let var_bounds (old_upper, old_lower) f v =
	let c = AF.coef f (succ v) in
	if compare c num0 < 0 then
		(true, old_lower)
	else
		if compare c num0 > 0 then
			(old_upper, true)
		else
			(old_upper, old_lower)

let xor a b =
	if a then
		not b
	else
		b

let rec collect_unbound_vars pool acc i =
	if i=(Array.length pool) then
		acc
	else
		let upper,lower = pool.(i) in
		let i' = succ i in
		if xor upper lower then
			collect_unbound_vars pool (i'::acc) i'
		else
			collect_unbound_vars pool acc i'

let rec no_unbound_vars f = function
	hd::tl ->
		let c = AF.coef f hd in
		if compare c num0 <> 0 then
			begin
				if !debug_omega then
					eprintf "Unbound v%i in %a@." hd AF.print f;
				false
			end
		else
			no_unbound_vars f tl
 | [] ->	true

let remove_unbound_vars_aux pool constrs =
	Array.fill pool 0 (Array.length pool) (false,false);
	C.iter (fun key (tree,f) -> Array.iteri (fun v bounds -> pool.(v) <- var_bounds bounds f v) pool) constrs;
	let unbound_vars = collect_unbound_vars pool [] 0 in
	C.filter (fun k (tree,f) -> no_unbound_vars f unbound_vars) constrs

let rec remove_unbound_vars pool constrs =
	let new_constrs = remove_unbound_vars_aux pool constrs in
	(*
	if C.length new_constrs < C.length constrs then
		remove_unbound_vars pool new_constrs
	else
	*)
		new_constrs

let rec omega pool pool2 constrs =
	if !debug_omega then
		print_constrs constrs;
	let constrs = remove_unbound_vars pool constrs in
	let v = pick_var pool2 constrs in
	if !debug_omega then
		eprintf "picked %a@." AF.print_var v;
	let l, u, rest = get_bounds v constrs in
	let pairs = all_pairs l u in
	if !debug_omega then
		eprintf "generated %i pairs@." (List.length pairs);
	let new_constrs = List.rev_map (omega_aux v) pairs in
	if !debug_omega then
		eprintf "new constraints generated@.";
	try
		List.find (fun (tree, f) -> is_neg_number f) new_constrs
	with Not_found ->
		if !debug_omega then
			eprintf "no contradiction found, building new table@.";
		let new_constrs = C.of_list (Array.length pool) new_constrs in
		C.append_list new_constrs rest;
		if !debug_omega then
			eprintf "calling omega@.";
		omega pool pool2 new_constrs

interactive_rw ge_to_ge0 :
	('a in int) -->
	('b in int) -->
	('a >= 'b) <--> ('a -@ 'b >= 0)

let ge_to_ge0C t =
	if is_ge_term t then
		ge_to_ge0
	else
		idC

let normalize2C =	(termC ge_to_ge0C) thenC relNormC

let totaltime = ref 0.
let starttime = ref 0.

let startT = argfunT (fun i p ->
	starttime := Unix.time ();
	if !debug_omega then
		begin
			eprintf "start %i@." i;
			let i' = mk_number_term (Lm_num.num_of_int i) in
			let t = mk_equal_term <<int>> i' i' in
			assertT t
		end
	else
		idT
)

let endT = argfunT (fun i p ->
	totaltime := Unix.time() -. !starttime;
	(*eprintf "endT: total time spent is %f@." !totaltime;*)
	if !debug_omega then
		begin
			eprintf "end %i@." i;
			let i' = mk_number_term (Lm_num.num_of_int i) in
			let t = mk_equal_term <<int>> i' i' in
			assertT t
		end
	else
		idT
)

let rec tree_stats h m mw s = function
	Hyp _ -> ((succ h), m, mw, s)
 | Mul (tree, gcd) -> tree_stats h (succ m) mw s tree
 | MulAndWeaken (tree, gcd, c) -> tree_stats h m (succ mw) s tree
 | Solve (v,c1,t1,l,c2,t2,u) ->
		let h1,m1,mw1,s1 = tree_stats h m mw (succ s) t1 in
		tree_stats h1 m1 mw1 s1 t2

let rec source2hyp info hyp_pos src = funT (fun p ->
match src with
 | Hyp (i, pos, len) ->
		if !debug_omega then
			eprintf "Hyp %i %i %i hyp_pos.(i)=%i@." i pos len hyp_pos.(i);
		if len = 0 then
			(*endT i thenMT*) rw normalize2C i
		else
			(*endT i thenMT*) rw normalize2C (hyp_pos.(i) + pos)
 | Mul (tree, gcd) ->
		rw (scaleC (mk_number_term gcd)) 0 thenMT
		source2hyp info hyp_pos tree
 | MulAndWeaken (tree, gcd, c) ->
		scaleAndWeakenT (mk_number_term gcd) (mk_number_term c) thenMT
		source2hyp info hyp_pos tree
 | Solve (v,c1,t1,l,c2,t2,u) ->
		let cleft = term_of c1 in
		let tleft = AF.term_of info u in
		let cright = term_of c2 in
		let tright = AF.term_of info l in
		tryT (var_elim2 (VI.restore info v) cleft tleft cright tright thenMLT
			[source2hyp info hyp_pos t1; source2hyp info hyp_pos t2])
)

let omegaAuxT info hyp_pos tree =
	source2hyp info hyp_pos tree thenMT rw ge_normC (-1)

let rec eval_hyp_pos_aux hyp_length hyp_pos count = function
	hyp::tail ->
		let count' = count + hyp_length.(hyp) in
		hyp_pos.(hyp) <- count';
		if !debug_omega then
			eprintf "hyp_pos.(%i)=%i@." hyp count';
		eval_hyp_pos_aux hyp_length hyp_pos count' tail
 | [] -> ()

let eval_hyp_pos n hyp_length used_hyps =
	let hyp_pos = Array.create (Array.length hyp_length) 0 in
	eval_hyp_pos_aux hyp_length hyp_pos n used_hyps;
	hyp_pos

let omegaCoreT info hyp_num hyp_length used_hyps tree f = funT (fun p ->
	let hyp_pos = eval_hyp_pos hyp_num hyp_length used_hyps in
	let h,m,mw,s = tree_stats 0 0 0 0 tree in
	if !debug_omega then
		eprintf "Solved (%i hyps, %i muls, %i mul&weaken, %i eliminations), reconstructing the proof@." h m mw s;
	match tree with
	 | Hyp i ->
			omegaAuxT info hyp_pos tree
	 | Mul _ | MulAndWeaken _ ->
			let tm = AF.term_of info f in
			assertT (mk_ge_term tm (term_of num0))
			thenLT [omegaAuxT info hyp_pos tree; rw ge_normC (-1)]
	 | Solve (v,c1,t1,l,c2,t2,u) ->
			let c1t = term_of c1 in
			let c2t = term_of c2 in
			assertT
				(mk_ge_term
					(mk_sub_term (mk_mul_term c1t (AF.term_of info u)) (mk_mul_term c2t (AF.term_of info l)))
					(mk_number_term num0))
			thenLT [omegaAuxT info hyp_pos tree; rw ge_normC (-1)]
)

let rec all_hyps_aux hyps l i =
   if i = 0 then l else
   let j = pred i in
      match SeqHyp.get hyps j with
         Hypothesis (_, t) ->
            all_hyps_aux hyps ((j+1,t)::l) j
       | Context _ ->
            all_hyps_aux hyps l j

let all_hyps arg =
   let hyps = (Sequent.explode_sequent arg).sequent_hyps in
	let len = Term.SeqHyp.length hyps in
      all_hyps_aux hyps [] len

type ('a, 'b) flexTree = Leaf of 'a | Node of ('b * (('a, 'b) flexTree)) list

let rec append i tac len pos l = function
	t::tail ->
		append i tac len (succ pos) ((i,t,pos,len,tac)::l) tail
 | [] -> l

let make_option tree i tac t =
	let terms = dest_xlist t in
	let len=List.length terms in
	let pos= -len in
	let option = append i tac len pos [] terms in
	(option, tree)

let options tree i tac t =
	Node (List.map (make_option tree i tac) t)

let rec hyp2ge p tree = function
	(i,t)::tail ->
		if !debug_arith_dtactic then
			eprintf "Itt_int_arith.hyp2ge: looking for %ith hyp %s%t" i (SimplePrint.short_string_of_term t) eflush;
		if is_member_term t then
			hyp2ge p tree tail
		else if is_ge_term t then
			let tree' = Node [([(i,t,i,0,idT)], tree)] in
			hyp2ge p tree' tail
		else
			(try
				if !debug_arith_dtactic then
					eprintf "Itt_int_arith.hyp2ge: searching ge_elim resource%t" eflush;
				let terms, tac = Sequent.get_resource_arg p get_ge_elim_resource (Sequent.get_pos_hyp_num p i) p in
				let tree' = options tree i (tac i) terms in
				hyp2ge p tree' tail
			with Not_found ->
				if !debug_arith_dtactic then
					eprintf "Itt_int_arith.hyp2ge: looking for %ith hyp %s - not found%t" i (SimplePrint.short_string_of_term t) eflush;
				hyp2ge p tree tail
			)
 | [] -> tree

let rec push2leaves f acc tree =
	let aux (data, subtree) =
		let data', acc' = f data acc in
		data', push2leaves f acc' subtree
	in
	match tree with
		Node edges ->
			Node (List.map aux edges)
	 | Leaf _ ->
			Leaf acc

let rec map_leaves f = function
	Node edges ->
		Node (List.map (fun (data,tree) -> data, map_leaves f tree) edges)
 | Leaf data ->
		Leaf (f data)

let rec smart_map_leaves f used_hyps = function
	Node (first::rest) ->
		let data, subtree = first in
		let i,_,_,_,_ = List.hd data in
		let subtree' = smart_map_leaves f used_hyps subtree in
		if used_hyps.(i) then
			Node ((data, subtree')::(List.map (fun (data,tree) -> data, smart_map_leaves f used_hyps tree) rest))
		else
			subtree'
 | Leaf data ->
		Leaf (f data)
 | Node [] ->
		raise (Invalid_argument "smart_map_leaves: empty set of edges")

let rec leaves2list = function
	Node edges ->
		let lists = List.map (fun (data,tree) -> leaves2list tree) edges in
		List.flatten lists
 | Leaf data ->
		[data]

let allhyps2ge p tree =
	hyp2ge p tree (all_hyps p)

let all2ge p =
	let tree = allhyps2ge p (Leaf ()) in
	let tree' = push2leaves (fun data acc -> data, List.append data acc) [] tree in
	tree'

let rec count_used_hyps used_hyps hyp_length = function
	Hyp (i,pos,len) ->
		used_hyps.(i) <- true;
		hyp_length.(i) <- len;
 | Mul (tree, gcd) ->
		count_used_hyps used_hyps hyp_length tree
 | MulAndWeaken (tree, gcd, c) ->
		count_used_hyps used_hyps hyp_length tree
 | Solve (v,c1,t1,l,c2,t2,u) ->
		count_used_hyps used_hyps hyp_length t1;
		count_used_hyps used_hyps hyp_length t2

let omegaSim dim pool pool2 used_hyps hyp_length constrs =
	if List.length constrs = 1 then
		begin
			let coord,f = List.hd constrs in
			let i, pos, len = coord in
			used_hyps.(i) <- true;
			hyp_length.(i) <- len;
			(Hyp coord, f)
		end
	else
		begin
			let n = succ dim in
			let constrs = List.rev_map (fun (i,f) -> norm (Hyp i, AF.grow n f)) constrs in
			let constrs = C.of_list dim constrs in
			let tree, f = omega pool pool2 constrs in
			count_used_hyps used_hyps hyp_length tree;
			(tree, f)
		end

let rec foldi_aux f ar acc current =
	if current = Array.length ar then
		acc
	else
		foldi_aux f ar (f current ar.(current) acc) (succ current)

let foldi f ar acc = foldi_aux f ar acc 0

let rec sim_make_sacs_aux p var2index l = function
	[] -> l
 | (i,t,pos,len,tac)::tl ->
		(match explode_term t with
		 | <<ge{'left; 'right}>> when not (alpha_equal left right) ->
				let t'=apply_rewrite p ge_normC t in
				sim_make_sacs_aux p var2index ((ge2af var2index ((i,pos,len),t'))::l) tl
		 | _ ->
				sim_make_sacs_aux p var2index l tl
		)

let sim_make_sacs p var2index constrs =
	let afs = sim_make_sacs_aux p var2index [] (*REV*)(*List.rev*) (constrs)(*REV*) in
	try
 		let item = List.find (fun (i,f) -> is_neg_number f) afs in
 		[item]
	with Not_found ->
		afs

let ge_elimT = argfunT (fun i p ->
	try
		let _,tac=Sequent.get_resource_arg p get_ge_elim_resource (Sequent.get_pos_hyp_num p i) p in
		tac i
	with Not_found ->
		idT
)

let rec prune_tree used_hyps = function
	Node edges ->
		let terms, subtree = List.hd edges in
		let i, term, pos, len, tac = List.hd terms in
		if used_hyps.(i) then
			let edges' = List.map (fun (data,subtree) -> (data, prune_tree used_hyps subtree)) edges in
			Node edges'
		else
			prune_tree used_hyps subtree
 | Leaf data -> Leaf data

let isEmptyOrMainLabel l =
   (l="") or (List.mem l main_labels)

let count_main_goals goall =
	let count = ref 0 in
	let aux g =
		if isEmptyOrMainLabel (Sequent.label g) then
			count := succ (!count)
	in
	List.iter aux goall;
	!count

let prefix_thenMLT =
   let rec combine tacl goall =
     match tacl, goall with
        [], [] -> []
      | t::ts, g :: gs when isEmptyOrMainLabel (Sequent.label g) ->
          t :: (combine ts gs)
      | _, g :: gs  ->
          idT :: (combine tacl gs)
      | _ ->
			raise (RefineError ("thenMLT", StringError "mismatch between number of main goals and number of"))
	in
	let combine1 tacl goall =
		if !debug_omega then
			eprintf "thenMLT: %itacs, %i goals, %i main@." (List.length tacl) (List.length goall) (count_main_goals goall);
		combine tacl goall
   in
     fun (tac:tactic) (tacl:tactic list) -> tac thenFLT (combine1 tacl)

let rec applyTreeT prefixT mainT used_hyps = function
	Node (first::rest) ->
		let data, subtree = first in
		let i,_,_,_,_ = List.hd data in
		let used_hyps' = i::used_hyps in
		prefix_thenMLT
			(prefixT i)
			((applyTreeT prefixT mainT used_hyps' subtree)::(List.map (fun (data,tree) -> applyTreeT prefixT mainT used_hyps' tree) rest))
 | Leaf data ->
		mainT (List.rev used_hyps) data
 | Node [] ->
		raise (Invalid_argument "applyTreeT: empty set of edges")

let total = ref 0.

let omegaPrepT = funT (fun p ->
	if !debug_omega then
		eprintf "omegaPrepT started@.";
	let start = Unix.time () in
	let options = all2ge p in
   let var2index = VI.create 13 in
 	let option_constrs = map_leaves (sim_make_sacs p var2index) options in
 	let hyp_num = succ (Sequent.hyp_count p) in
	let used_hyps = Array.make hyp_num false in
	let hyp_length = Array.make hyp_num 0 in
	let n0 = VI.length var2index in
	let pool = Array.make n0 (false,false) in
	let pool2 = Array.make n0 ringZero in
	let pruned_solutions = smart_map_leaves (omegaSim n0 pool pool2 used_hyps hyp_length) used_hyps option_constrs in
	let used_hyps = foldi (fun i v acc -> if v then i::acc else acc) used_hyps [] in
	if !debug_omega then
		begin
			eprintf "used hyps ";
			List.iter (eprintf "%i ") used_hyps;
			eprintf "@.";
		end;
	let info = VI.invert var2index in
	total := !total +. (Unix.time() -. start);
	(*eprintf "Total time spent in omegaPrepT is %f@." !total;*)
	let aux used_hyps (tree, f) =
		omegaCoreT info hyp_num hyp_length used_hyps tree f
	in
	onMHypsT used_hyps (rw relNormC) thenMT
	applyTreeT ge_elimT aux [] pruned_solutions
)

let omegaT =
	startT 2 thenMT arithRelInConcl2HypT thenMT
	omegaPrepT thenMT endT 2 thenT rw relNormC 0

let getTimeT = funT (fun p ->
	eprintf "spent %f seconds in omegaPrepT@." !total;
	total := 0.;
	failT
)