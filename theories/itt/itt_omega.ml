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

module type RingSig =
sig
   type ring

   val ringUnit : ring
   val ringZero : ring
   val mul : ring -> ring -> ring
   val add : ring -> ring -> ring
   val neg : ring -> ring
   val sub : ring -> ring -> ring
   val compare : ring -> ring -> int
	val isNegative : ring -> bool

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

   val mk_number: ring -> af
   val mk_var: vars -> af
   val scale: ring -> af -> af
   val add: af -> af -> af
	val sub: af -> af -> af

   val coef: af -> vars -> ring
   val remove: af -> vars -> af
   val split: af -> (ring * vars * af)
   val isNumber: af -> bool

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

   let mk_number k =
		Table.add Table.empty constvar k

   let mk_var v = Table.add Table.empty v Ring.ringUnit

   let scale_aux k v d =
      Ring.mul k d

   let scale k f =
      if Ring.compare k Ring.ringZero =0 then Table.empty
      else if Ring.compare k Ring.ringUnit =0 then f
      else Table.map (scale_aux k) f

   let coef f v =
      try Table.find f v
      with Not_found -> Ring.ringZero

   let add f1 f2 =
		Table.union f1 f2

	let sub f1 f2 =
		let neg_f2 = scale (Ring.neg Ring.ringUnit) f2 in
		add f1 neg_f2

   let remove f vs = Table.remove f vs

   let rec split f =
		if Table.is_empty f then
			(Ring.ringZero, constvar, mk_number Ring.ringZero)
		else
			let v, coefs, rest = Table.deletemax f in
			match coefs with
				[c] ->
					if v!=constvar && (Ring.compare c Ring.ringZero =0) then
						split rest
					else
						(c,v,rest)
			 | _ -> raise (Invalid_argument "More than one coefficient associated with a variable")

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

module IntRing =
struct
   open Lm_num

   type ring = num

   let num0=num_of_int 0
   let num1=num_of_int 1
   let ringUnit = num1
   let ringZero = num0

	let isNegative n = (compare_num n num0 < 0)

	let isPositive n = (compare_num n num0 > 0)

   let mul a b = mult_num a b

   let add a b = add_num a b

   let sub a b = sub_num a b

   let neg a = sub num0 a

	let sign_num a = num_of_int (compare_num a num0)

   let compare a b = compare_num a b

   let print out a =
      fprintf out "(%s)" (string_of_num a)

   let term_of a = mk_number_term a

   let add_term = mk_add_term
   let mul_term = mk_mul_term
   let neg_term = mk_minus_term
   let sub_term = mk_sub_term
   let ge_term = mk_ge_term
end

module R = IntRing
module AF=MakeAF(R)
module VI=Var2Index(R)
open IntRing

module Var =
struct
	type t = term
	let equal = alpha_equal
	let hash = Hashtbl.hash
end

let ge_normC = (addrC [0] normalizeC) thenC (addrC [1] normalizeC)

let monom2af var2index t =
	match explode_term t with
		<<'t1 *@ 't2>> ->
         if is_number_term t1 then
            let i=VI.lookup var2index t2 in
            let f=AF.mk_var i in
					AF.scale (dest_number t1) f
         else
            let i=VI.lookup var2index t in
					AF.mk_var i
	 | <<number[i:n]>> ->
         AF.mk_number (dest_number t)
	 | _ ->
			let i=VI.lookup var2index t in
				AF.mk_var i

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
	let es={sequent_args= <<sequent_arg>>; sequent_hyps=(SeqHyp.of_list []); sequent_goals=(SeqGoal.of_list [t])} in
	let s=mk_sequent_term es in
	let s'=Top_conversionals.apply_rewrite p (higherC conv) s in
	SeqGoal.get (TermMan.explode_sequent s').sequent_goals 0

let rec make_sacs_aux p i l = function
	[] -> l
 | hd::tl ->
		let i' = succ i in
		match hd with
			Hypothesis (_, t) ->
				(match explode_term t with
				 | <<ge{'left; 'right}>> when not (alpha_equal left right) ->
						let t'=apply_rewrite p ge_normC t in
						make_sacs_aux p i' ((i,t')::l) tl
				 | _ ->
						make_sacs_aux p i' l tl
				)
		 | Context _ -> make_sacs_aux p i' l tl

type contraints = Constraints of (int * AF.af) list | Contradiction of (int * AF.af)

let is_neg_number f =
	if AF.isNumber f then
		isNegative (AF.coef f AF.constvar)
	else
		false

let make_sacs var2index p =
   let hyps = Term.SeqHyp.to_list (Sequent.explode_sequent p).sequent_hyps in
	let ihyps = make_sacs_aux p 1 [] hyps in
	let afs=List.map (ge2af var2index) ihyps in
	try
 		let item = List.find (fun (i,f) -> is_neg_number f) afs in
 		Contradiction item
	with Not_found ->
		Constraints afs

(*********************************************************************
 * OMEGA
 *********************************************************************)

interactive var_elim 'v :
	[wf] sequent { <H> >- 'a in int } -->
	[wf] sequent { <H> >- 'b in int } -->
	[wf] sequent { <H> >- 'v in int } -->
	sequent { <H> >- number[i:n] *@ 'v -@ 'a >= 0 } -->
	sequent { <H> >- 'b -@ number[j:n] *@ 'v >= 0 } -->
	sequent { <H> >- number[i:n] *@ 'b >= number[j:n] *@ 'a }

interactive dark_var_elim 'v :
	[wf] sequent { <H> >- 'a in int } -->
	[wf] sequent { <H> >- 'b in int } -->
	[wf] sequent { <H> >- 'v in int } -->
	sequent { <H> >- number[i:n] *@ 'v -@ 'a >= 0 } -->
	sequent { <H> >- 'b -@ number[j:n] *@ 'v >= 0 } -->
	sequent { <H> >- number[i:n] *@ 'b >= number[j:n] *@ 'a +@ (number[i:n] -@ 1) *@ (number[j:n] -@ 1) }

interactive_rw factor_out 'cleft 'tleft 'cright 'tright :
	('cleft in int) -->
	('tleft in int) -->
	('cright in int) -->
	('tright in int) -->
	('left +@ ('cright *@ 'tright) = 'right +@ ('cleft *@ 'tleft) in int) -->
	('left >= 'right) <-->
	('cleft *@ 'tleft >= 'cright *@ 'tright)

interactive_rw factor_out2 number[l:n] 'tleft number[r:n] 'tright :
	('tleft in int) -->
	('tright in int) -->
	('left +@ (number[r:n] *@ 'tright) = (number[l:n] *@ 'tleft) in int) -->
	('left >= 0) <-->
	(number[l:n] *@ 'tleft >= number[r:n] *@ 'tright)

interactive_rw dark_factor_out2 number[l:n] 'tleft number[r:n] 'tright :
	('tleft in int) -->
	('tright in int) -->
	('left +@ (number[r:n] *@ 'tright) = (number[l:n] *@ 'tleft) in int) -->
	('left >= (number[l:n] -@ 1) *@ (number[r:n] -@ 1)) <-->
	(number[l:n] *@ 'tleft >= number[r:n] *@ 'tright +@ (number[l:n] -@ 1) *@ (number[r:n] -@ 1))

let rec rev_flatten = function
   h :: t ->
      List.rev_append h (rev_flatten t)
 | [] ->
      []

let all_pairs l1 l2 =
	let pairs_lists = List.rev_map (fun x -> List.rev_map (fun y -> (y,x)) l1) l2 in
	rev_flatten pairs_lists

type omegaTree =
	Solve of AF.vars * ring * omegaTree * AF.af * ring * omegaTree * AF.af
 | SolveDark of AF.vars * ring * omegaTree * AF.af * ring * omegaTree * AF.af
 | Hyp of int

let omega_aux v ((c1,t1,l),(c2,t2,u)) =
	(Solve (v,c1,t1,l,c2,t2,u),
	AF.sub (AF.scale c1 u) (AF.scale c2 l))

let dark_omega_aux v ((c1,t1,l),(c2,t2,u)) =
	(SolveDark (v,c1,t1,l,c2,t2,u),
	AF.sub (AF.sub (AF.scale c1 u) (AF.scale c2 l))
			(AF.mk_number (mul (sub c1 ringUnit) (sub c2 ringUnit))))

let identical_to_real_shadow ((c1,t1,l),(c2,t2,u)) =
	(compare c1 ringUnit = 0) || (compare c2 ringUnit = 0)

let rec pick_var info = function
	[] ->
		if !debug_omega then
			eprintf "pick_var: No variables left@.";
		raise Not_found
		(*raise (RefineError ("omegaT", StringError "failed to find a contradiction - no variables left"))*)
 | (tree,f)::tl ->
		let c,v,rest = AF.split f in
		if v=AF.constvar then
			pick_var info tl
		else
			v

let rec get_bounds v l u = function
	[] -> (l,u)
 | (tree, f) as original :: tl ->
		let c = AF.coef f v in
		if isPositive c then
			let f' = AF.remove f v in
			get_bounds v ((c, tree, (AF.scale (neg ringUnit) f'))::l) u tl
		else
			if isNegative c then
				let f' = AF.remove f v in
				get_bounds v l ((neg c, tree, f')::u) tl
			else
				get_bounds v l u tl

(*
let rec print_constrs info = function
	[] ->
		eprintf "@."
 | (tree, f)::tl ->
		eprintf "%a@." AF.print f;
		print_constrs info tl
*)

let print_constrs info l =
	eprintf "%i constraints@." (List.length l)

let rec omega info constrs =
	if !debug_omega then
		print_constrs info constrs;
	let v = pick_var info constrs in
	if !debug_omega then
		eprintf "picked %a@." AF.print_var v;
	let l, u = get_bounds v [] [] constrs in
	let pairs = all_pairs l u in
	if !debug_omega then
		eprintf "generated %i pairs@." (List.length pairs);
	let new_constrs = List.rev_map (omega_aux v) pairs in
	try
		List.find (fun (tree, f) -> is_neg_number f) new_constrs
	with Not_found ->
		(try omega info new_constrs
			with Not_found ->
				dark_omega info v pairs
		)

and dark_omega info v pairs =
	if List.for_all identical_to_real_shadow pairs then
		raise Not_found
	else
		if !debug_omega then
			eprintf "dark shadow for %a@." AF.print_var v;
		let new_constrs = List.rev_map (dark_omega_aux v) pairs in
		try
			List.find (fun (tree, f) -> is_neg_number f) new_constrs
		with Not_found ->
			omega info new_constrs

interactive_rw ge_to_ge0 :
	('a in int) -->
	('b in int) -->
	('a >= 'b) <--> ('a -@ 'b >= 0)

let ge_to_ge0C t =
	if is_ge_term t then
		ge_to_ge0
	else
		idC

let normalize2C = (termC ge_to_ge0C) thenC normalizeC

let rec source2hyp info = function
 | Hyp i ->
		rw normalize2C i
 | Solve (v,c1,t1,l,c2,t2,u) ->
		let cleft = term_of c1 in
		let tleft = AF.term_of info u in
		let cright = term_of c2 in
		let tright = AF.term_of info l in
		rw (factor_out2 cleft tleft cright tright) 0 thenMT
		tryT (var_elim (VI.restore info v) thenMLT
			[source2hyp info t1; source2hyp info t2])
 | SolveDark (v,c1,t1,l,c2,t2,u) ->
		let cleft = term_of c1 in
		let tleft = AF.term_of info u in
		let cright = term_of c2 in
		let tright = AF.term_of info l in
		rw (dark_factor_out2 cleft tleft cright tright) 0 thenMT
		tryT (dark_var_elim (VI.restore info v) thenMLT
			[source2hyp info t1; source2hyp info t2])

let omegaAuxT info tree = funT (fun p ->
	source2hyp info tree thenMT rw ge_normC (-1)
)

let omegaCoreT = funT (fun p ->
   let var2index = VI.create 13 in
   let s = make_sacs var2index p in
   let info=VI.invert var2index in
   match s with
   	Constraints constrs ->
			let tree, f = omega info (List.map (fun (i,f) -> (Hyp i, f)) constrs) in
			if !debug_omega then
				eprintf "Solved, reconstructing the proof@.";
			(match tree with
			 | Hyp i ->
					omegaAuxT info tree
			 | Solve (v,c1,t1,l,c2,t2,u) ->
					let c1t = term_of c1 in
					let c2t = term_of c2 in
					assertT
						(mk_ge_term
							(mk_sub_term (mk_mul_term c1t (AF.term_of info u)) (mk_mul_term c2t (AF.term_of info l)))
							(mk_number_term num0))
					thenLT [omegaAuxT info tree; rw ge_normC (-1)]
			 | SolveDark (v,c1,t1,l,c2,t2,u) ->
					let c1t = term_of c1 in
					let c2t = term_of c2 in
					let num1_term = mk_number_term num1 in
					assertT
						(mk_ge_term
							(mk_sub_term (mk_mul_term c1t (AF.term_of info u)) (mk_mul_term c2t (AF.term_of info l)))
							(mk_mul_term (mk_sub_term c1t num1_term) (mk_sub_term c2t num1_term)))
					thenLT [omegaAuxT info tree; rw ge_normC (-1)]
			)
	 | Contradiction (i,f) ->
	 		omegaAuxT info (Hyp i)
)

let omegaT = preT thenMT omegaCoreT thenT rw normalizeC 0
