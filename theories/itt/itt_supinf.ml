extends Itt_equal
extends Itt_rfun
extends Itt_logic
extends Itt_bool
extends Itt_int_ext
extends Itt_rat
extends Itt_rat2

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
open Itt_rat

let _ = show_loading "Loading Itt_supinf%t"

let debug_supinf_trace =
   create_debug (**)
      { debug_name = "supinf_trace";
        debug_description = "Print out (low-level) trace of supinf execution";
        debug_value = false
      }

let debug_supinf_steps =
   create_debug (**)
      { debug_name = "supinf_steps";
        debug_description = "Itt_supinf.supinfT: print out (high-level) steps to be proved";
        debug_value = false
      }

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

   let print out r =
      match r with
(*			Number (a,b) -> fprintf out "rat(%s,%s)" (string_of_num a) (string_of_num b)*)
         Number (a,b) ->
            if eq_num a num0 then fprintf out "0*"
            else if eq_num b num1 then fprintf out "(%s)" (string_of_num a)
            else fprintf out "(%s/%s)" (string_of_num a) (string_of_num b)
       | MinusInfinity -> fprintf out "(-oo)"
       | PlusInfinity -> fprintf out "(+oo)"

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

	let print out info =
		let count,table=info in
		let aux k d = fprintf out "%a ->v%i%t" print_term k d eflush in
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

   let print out (v:elt) (kl: data list) =
      match kl with
         [k] -> BField.print out k; (*printf"*";*) VarType.print out v
       | _ -> raise (Invalid_argument "More than one coefficient is associated with one variable")

   let append l1 l2 =
      match l1,l2 with
         [],[] -> [BField.fieldZero]
       | [],[a] -> [a]
       | [a],[] -> [a]
       | [a],[b] -> [BField.add a b]
       | _,_ -> raise (Invalid_argument "Addition non-trivial lists are not supported")

end

module type SACS_Sig =
sig
   type vars
   type af
   type saf
   type step
	type source
   type sacs

   val empty: sacs
   val addConstr: sacs -> af -> sacs

   val upper: (term array) -> sacs -> vars -> (saf * step list)
   val lower: (term array) -> sacs -> vars -> (saf * step list)

   val print: out_channel -> sacs -> unit
end

module MakeSACS(BField : BoundFieldSig)
(Source: SourceSig with type bfield=BField.bfield and type vars=VarType.t)
(AF : AF_Sig  with type bfield=BField.bfield and type vars=VarType.t and type source=Source.source)
(SAF : SAF_Sig  with type bfield=BField.bfield and type vars=VarType.t and type source=Source.source and type af=AF.af)
: SACS_Sig with
 	type vars=VarType.t and
  	type source=Source.source and
 	type af=AF.af and
  	type saf=SAF.saf and
   type step = tactic SAF.step =
struct
   type vars   = VarType.t
   type af     = AF.af
   type saf    = SAF.saf
   type step   = tactic SAF.step
	type source = Source.source
   type sacs   = af list

   let empty = []
   let addConstr s f = f::s

   let print out s =
      List.iter (fun x -> begin fprintf out "%a>=0\n" AF.print x end) s

   let rec upper' info s v =
      match s with
         [] -> SAF.affine AF.plusInfinity, []
       | f::tl ->
				let v_coef = AF.coef f v in
            if BField.compare v_coef BField.fieldZero >=0 then
               upper' info tl v
            else
               let k=BField.neg (BField.inv v_coef) in
               let rest=AF.remove f v in
					let u0=AF.scale k rest in
					let u1=AF.extract2rightSource v u0 in
               let r0,a0=upper' info tl v in
               let r1=SAF.min r0 (SAF.affine u1) in
					let saf_v=SAF.affine (AF.mk_var v) in
                  if SAF.isAffine r1 then
                     r1,(SAF.Assert ("upper 0",r1,saf_v, idT))::a0
                  else
                     r1,(SAF.Assert ("upper 1",r1,saf_v, idT))::a0
(*						r1,(SAF.Assert ("upper 1",r1,saf_v, ge_minLeftIntro))::a0*)

   let upper info s v =
      let result,actions = upper' info s v in
         if !debug_supinf_steps then
            eprintf "upper: %a <= %a@." AF.print_var v SAF.print result;
         result,actions

   let rec lower' info s v =
      match s with
         [] -> SAF.affine AF.minusInfinity,[]
       | f::tl ->
				let v_coef = AF.coef f v in
            if BField.compare v_coef BField.fieldZero <=0 then
               lower' info tl v
            else
               let k=BField.neg (BField.inv v_coef) in
               let rest=AF.remove f v in
					let u0=AF.scale k rest in
					let u1=AF.extract2leftSource v u0 in
               let r0,a0=lower' info tl v in
               let r1=SAF.max r0 (SAF.affine u1) in
					let saf_v=SAF.affine (AF.mk_var v) in
                  if SAF.isAffine r1 then
                     r1,(SAF.Assert ("lower 0",saf_v, r1, idT))::a0
                  else
                     r1,(SAF.Assert ("lower 1",saf_v, r1, idT))::a0
(*						r1,(SAF.Assert ("lower 1",saf_v, r1, ge_maxRightIntro))::a0*)

   let lower info s v =
      let result,actions = lower' info s v in
         if !debug_supinf_steps then
            eprintf "lower: %a <= %a@." SAF.print result AF.print_var v;
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

module S=MakeSource(RationalBoundField)
module AF=MakeAF(RationalBoundField)(S)
module SAF=MakeSAF(RationalBoundField)(S)(AF)
module SACS=MakeSACS(RationalBoundField)(S)(AF)(SAF)
module CS=Lm_set.LmMakeDebug(VarType)
module VI=Var2Index(RationalBoundField)

open RationalBoundField
open S

let suppa' info (x:AF.vars) (f:AF.af) =
   if !debug_supinf_trace then
      eprintf "suppa: %a <= %a@." AF.print_var x AF.print f;
   let b = AF.coef f x in
   let c = AF.remove f x in
	let af_x=AF.mk_var x in
   let saf_x=SAF.affine af_x in
      if compare b fieldUnit < 0 then
         let result0=AF.scale (inv (sub fieldUnit b)) c in
			let result=AF.extract2rightSource x result0 in
            (result, [SAF.Assert("suppa case 0",SAF.affine result, saf_x, idT)])
		(* SAF.AssertT <<'x <= result>> thenAT
			'x<='y <-->
			(1-'b)*'x <= (1-'b)*'y <-->
			'x <= 'b*'x + (1-'b)*'y <-->(normalize) 'x <= 'f *)
      else
      if (compare b fieldUnit = 0) && (AF.isNumber c) then
         let cmp=compare (AF.coef c AF.constvar) fieldZero in
            if cmp<0 then
               (AF.contrSource f AF.minusInfinity, [SAF.Assert ("suppa case 100",SAF.affine f, saf_x, idT)])
            else
            if cmp=0 then
               (af_x, [SAF.Assert("suppa case 1010",SAF.affine f, saf_x, idT)])
            else
               (AF.plusInfinity, [])
      else
         (AF.plusInfinity, [])

let suppa info x f =
   let (result,actions)=suppa' info x f in
      if !debug_supinf_steps then
         begin
            eprintf "suppa<: %a <= %a@." AF.print_var x AF.print f;
            eprintf "suppa>: %a <= %a@." AF.print_var x AF.print result
         end;
      (result,actions)

let rec supp' info (x:AF.vars) (saf:SAF.saf) =
	let src,s=saf in
   match s with
      SAF.Affine f ->
         let r,a=suppa info x (AF.setSource src f) in
            SAF.affine r, a
    | SAF.Min (a,b) ->
         let f1,a1=supp' info x (SAF.setSource (Sleft src) a) in
         let f2,a2=supp' info x (SAF.setSource (Sright src) b) in
			(match SAF.getSource f1, SAF.getSource f2 with
				Scontradiction s, _ ->
					f1,a1
			 | _, Scontradiction s ->
					f2,a2
			 | _, _ ->
				let result=SAF.min f1 f2 in
				let act=SAF.Assert ("supp",result,
										  (SAF.affine (AF.mk_var x)),
										  idT
(*										  (ge_minLeftIntro)*)
										 )
				in
				result, act::(a1@a2)
			)
			(*result, act::(a1@(a2@[SAF.Tactic (tryT (ge_minLeftElim (-1)))]))*)
    | SAF.Max _ -> raise (Invalid_argument "Itt_supinf.supp applied to max(...,...)")
	(* SAF.AssertT << 'x <= min('a;'b) >> thenAT
		'x <= min('a;'b) <-->
		'x <= 'a & 'x <= 'b *)

let supp info x s =
   let result,actions=supp' info x s in
      if !debug_supinf_steps then
         begin
            eprintf"supp<: %a <= %a@." AF.print_var x SAF.print s;
            eprintf"supp>: %a <= %a@." AF.print_var x SAF.print result
         end;
      result,actions

let inffa' info (x:AF.vars) (f:AF.af) =
   if !debug_supinf_trace then
      eprintf"inffa: %a >= %a@." AF.print_var x AF.print f;
   let b = AF.coef f x in
   let c = AF.remove f x in
	let af_x=AF.mk_var x in
   let saf_x=SAF.affine af_x in
      if compare b fieldUnit < 0 then
         let result0=AF.scale (inv (sub fieldUnit b)) c in
			let result=AF.extract2leftSource x result0 in
            (result, [SAF.Assert ("inffa case 0",saf_x,SAF.affine result, idT)])
		(* SAF.AssertT <<'x >= result>> thenAT
			'x>='y <-->
			(1-'b)*'x >= (1-'b)*'y <-->
			'x >= 'b*'x + (1-'b)*'y <-->(normalize) 'x >= 'f *)
      else
      if (compare b fieldUnit = 0) && (AF.isNumber c) then
         let cmp=compare (AF.coef c AF.constvar) fieldZero in
            if cmp>0 then
               (AF.contrSource f AF.plusInfinity, [SAF.Assert ("inffa case 100",saf_x, SAF.affine f, idT)])
            else
            if cmp=0 then
               (af_x, [SAF.Assert("inffa case 1010",saf_x, SAF.affine f, idT)])
            else
               (AF.minusInfinity,[])
      else
         (AF.minusInfinity,[])

let inffa info x f =
   let result,actions=inffa' info x f in
      if !debug_supinf_steps then
         begin
            eprintf"inffa<: %a <= %a@." AF.print f AF.print_var x;
            eprintf"inffa>: %a <= %a@." AF.print result AF.print_var x
         end;
      (result,actions)

let rec inff' info (x:AF.vars) (saf:SAF.saf) =
	let src,s=saf in
   match s with
      SAF.Affine f ->
         let r,a=inffa info x (AF.setSource src f) in
            SAF.affine r, a
    | SAF.Max (a,b) ->
         let f1,a1=inff' info x (SAF.setSource (Sleft src) a) in
         let f2,a2=inff' info x (SAF.setSource (Sright src) b) in
			(match SAF.getSource f1, SAF.getSource f2 with
				Scontradiction s, _ ->
					f1,a1
			 | _, Scontradiction s ->
					f2,a2
			 | _, _ ->
				let result=SAF.max f1 f2 in
				result, (SAF.Assert ("inff",SAF.affine (AF.mk_var x), result, idT))::(a1@a2)
			)
(*			result, (SAF.Assert (SAF.affine (AF.mk_var x), result, (addHiddenLabelT "inff" thenT ge_maxRightIntro)))::(a1@(a2@[SAF.Tactic (tryT (ge_maxRightElim (-1)))]))*)
    | SAF.Min _ -> raise (Invalid_argument "Itt_supinf.inff applied to min(...,...)")
	(* SAF.AssertT << 'x >= max('a;'b) >> thenAT
		'x >= max('a;'b) <-->
		'x >= 'a & 'x >= 'b *)

let inff info x s =
   let result,actions=inff' info x s in
      if !debug_supinf_steps then
         begin
            eprintf"inff<: %a <= %a@." SAF.print s AF.print_var x;
            eprintf"inff>: %a <= %a@." SAF.print result AF.print_var x
         end;
      (result,actions)

let rec supa info (c:SACS.sacs) (f:AF.af) (h:CS.t) =
   if !debug_supinf_trace then
      begin
         eprintf"supa:\n%a@.%a@.%a@."	(**)
            SACS.print c
            AF.print f
            CS.print h
      end;
   let (r,v,b) = AF.split f in
      if v=AF.constvar then
         begin
            if !debug_supinf_trace then
               (eprintf "supa case 0@.");
				(SAF.affine (AF.mk_number r), [])
			end
      else
         begin
            if !debug_supinf_trace then
               (eprintf "supa case 1 var:%i@." v);
				let af_v=AF.mk_var v in
					if (AF.isNumber b) && (compare (AF.coef b AF.constvar) fieldZero =0) then
                  begin
                     if !debug_supinf_trace then
                        (eprintf "supa case 10@.");
							if compare r fieldUnit = 0 then
                        begin
                           if !debug_supinf_trace then
                              (eprintf "supa case 100@.");
									if CS.mem h v then
                              begin
                                 if !debug_supinf_trace then
                                    (eprintf "supa case 1000@.");
											let af_v = AF.mk_var v in
											(SAF.affine af_v, [])
										end
									else
										begin
											if !debug_supinf_trace then
												(eprintf "supa case 1001@.");
											let r0,a0=SACS.upper info c v in
											let saf_v=SAF.affine af_v in
									(*let a0=[r0, saf_v, addHiddenLabelT "supa 1001 a0"] in*)
											let r1,a1=sup info c r0 (CS.add h v) in
											let r1'=SAF.transitiveLeftSource r1 r0 v in
											let a11=[SAF.Transitive("supa 1001 a11",r1',r0,saf_v)] in
											let r2,a2=supp info v r1' in
												(r2,a2@(a11@(a1@a0)))
										end
								end
							else
                        begin
                           if !debug_supinf_trace then
                              (eprintf "supa case 101@.");
									let saf_v=SAF.affine af_v in
									if compare r fieldZero < 0 then
                              begin
                                 if !debug_supinf_trace then
                                    (eprintf "supa case 1010@.");
											let r0,a0=inf info c saf_v h in
												SAF.scale r r0, a0
										end
									else
                              begin
                                 if !debug_supinf_trace then
                                    (eprintf "supa case 1011@.");
											let r0,a0=sup info c saf_v h in
												SAF.scale r r0, a0
										end
								end
						end
					else
                  begin
                     if !debug_supinf_trace then
                        (eprintf "supa case 11@.");
							let b',a0 = sup info c (SAF.affine b) (CS.add h v) in
							let scaled_av=AF.scale r af_v in
							let scaled_v=SAF.affine scaled_av in
							let f'=SAF.add scaled_v b' in
							let saf_f=SAF.affine f in
							(*let f''=SAF.addVarSource r v f' in*)
							let a01=SAF.Assert("supa 11",f', saf_f, idT) in
								if SAF.occurs v b' then
                           begin
                              if !debug_supinf_trace then
                                 (eprintf "supa case 110 var:%a@." SAF.print scaled_v);
										let r1,a1=sup info c f' h in
										let r1'=SAF.transitiveLeftSource r1 f' 0 in
										(r1',a1@(a01::a0))
									end
								else
                           begin
                              if !debug_supinf_trace then
                                 (eprintf "supa case 111 var:%a@." SAF.print scaled_v);
										let r1,a1=sup info c scaled_v h in
										let r2=SAF.add r1 b' in
										let b''=SAF.scale (neg fieldUnit) b' in
										let a2=SAF.Assert("supa case 1110",r2,f',ge_addMono (SAF.term_of info b'')) in
										let a3=SAF.Transitive("supa case 1111",r2,f',saf_f) in
											(r2, (a3::(a2::(a1@(a01::a0)))))
									end
						end
			end

and sup' info (c:SACS.sacs) (saf:SAF.saf) (h:CS.t) =
	let (src,s)=saf in
   match s with
      SAF.Affine f -> supa info c (AF.setSource src f) h
    | SAF.Min (a,b) ->
         let f1,a1=sup' info c (SAF.setSource (Sleft src) a) h in
         let f2,a2=sup' info c (SAF.setSource (Sright src) b) h in
         let result=SAF.min f1 f2 in
         let actions=
            if SAF.isAffine result then
               (SAF.Assert("sup 0",result, saf, ge_minLeftIntro))::(a1@a2)
            else
               (SAF.Assert("sup 1",result, saf, idT))::(a1@a2)
(*					(SAF.Assert("sup 1",result, s, (tryT min_ge_minIntro)))::(a1@a2)*)
         in
            result, actions
    | SAF.Max _ -> raise (Invalid_argument "Itt_supinf.sup applied to max(...,...)")

and sup info (c:SACS.sacs) (s:SAF.saf) (h:CS.t) =
   let result,actions=sup' info c s h in
      if !debug_supinf_steps then
         begin
            eprintf"sup: %a <= %a@." SAF.print s SAF.print result
         end;
      (result,actions)

and infa info (c:SACS.sacs) (f:AF.af) (h:CS.t) =
   if !debug_supinf_trace then
      begin
         eprintf"infa:\n%a@.%a@.%a@." (**)
            SACS.print c
            AF.print f
            CS.print h
      end;
   let (r,v,b) = AF.split f in
      if v=AF.constvar then
         begin
            if !debug_supinf_trace then
               (eprintf "infa case 0@.");
				(SAF.affine (AF.mk_number r), [])
         end
      else
         begin
            if !debug_supinf_trace then
               (eprintf "infa case 1 var:%i@." v);
            let af_v=AF.mk_var v in
            let saf_v = SAF.affine af_v in
               if (AF.isNumber b) && (compare (AF.coef b AF.constvar) fieldZero =0) then
                  begin
                     if !debug_supinf_trace then
                        (eprintf "infa case 10@.");
                     if compare r fieldUnit = 0 then
                        begin
                           if !debug_supinf_trace then
                              (eprintf "infa case 100@.");
                           if CS.mem h v then
                              begin
                                 if !debug_supinf_trace then
                                    (eprintf "infa case 1000@.");
											let af_v = AF.mk_var v in
											(SAF.affine af_v, [])
                              end
                           else
                              begin
                                 if !debug_supinf_trace then
                                    (eprintf "infa case 1001@.");
                                 let r0,a0=SACS.lower info c v in
									(*let a0=[saf_v, r0, addHiddenLabelT "infa 1001 a0"] in*)
                                 let r1,a1=inf info c r0 (CS.add h v) in
											let r1'=SAF.transitiveRightSource v r0 r1 in
                                 let a11=[SAF.Transitive("infa 1001 a11",saf_v,r0,r1')] in
                                 let r2,a2=inff info v r1' in
                                    (r2, a2@(a11@(a1@a0)))
                              end
                        end
                     else
                        begin
                           if !debug_supinf_trace then
                              (eprintf "infa case 101@.");
                           if compare r fieldZero < 0 then
                              begin
                                 if !debug_supinf_trace then
                                    (eprintf "infa case 1010@.");
                                 let r0,a0=sup info c saf_v h in
												SAF.scale r r0, a0
                              end
                           else
                              begin
                                 if !debug_supinf_trace then
                                    (eprintf "infa case 1011@.");
                                 let r0,a0=inf info c saf_v h in
												SAF.scale r r0, a0
                              end
                        end
                  end
               else
                  begin
                     if !debug_supinf_trace then
                        (eprintf "infa case 11@.");
                     let b',a0 = inf info c (SAF.affine b) (CS.add h v) in
                     let scaled_v=SAF.affine (AF.scale r af_v) in
                     let f'=SAF.add scaled_v b' in
                     let saf_f=SAF.affine f in
							(*let f''=SAF.addVarSource r v f' in*)
                     let a01=SAF.Assert("infa 11",saf_f, f', idT) in
                        if SAF.occurs v b' then
                           begin
                              if !debug_supinf_trace then
                                 (eprintf "infa case 110 var:%a@." SAF.print scaled_v);
                              let r1,a1=inf info c f' h in
										let r1'=SAF.transitiveRightSource 0 f' r1 in
                                 r1', a1@(a01::a0)
                           end
                        else
                           begin
                              if !debug_supinf_trace then
                                 (eprintf "infa case 111 var:%a@." SAF.print scaled_v);
                              let r1,a1=inf info c scaled_v h in
                              let r2=SAF.add r1 b' in
                              let b''=SAF.scale (neg fieldUnit) b' in
                              let a2=SAF.Assert("infa case 1110",f',r2,ge_addMono (SAF.term_of info b'')) in
                              let a3=SAF.Transitive("infa case 1111",saf_f,f',r2) in
                                 (r2, (a3::(a2::(a1@(a01::a0)))))
                           end
                  end
         end

and inf' info (c:SACS.sacs) (saf:SAF.saf) (h:CS.t) =
	let (src,s)=saf in
   match s with
      SAF.Affine f -> infa info c (AF.setSource src f) h
    | SAF.Max (a,b) ->
         let f1,a1=inf' info c (SAF.setSource (Sleft src) a) h in
         let f2,a2=inf' info c (SAF.setSource (Sright src) b) h in
         let result=SAF.max f1 f2 in
         let actions=
            if SAF.isAffine result then
               (SAF.Assert("inf 0",saf, result, ge_maxRightIntro))::(a1@a2)
            else
               (SAF.Assert("inf 1",saf, result, idT))::(a1@a2)
(*					(SAF.Assert("inf 1",s, result, (tryT max_ge_maxIntro)))::(a1@a2)*)
         in
            result, actions
    | SAF.Min _ -> raise (Invalid_argument "Itt_supinf.inf applied to min(...,...)")

and inf info (c:SACS.sacs) (s:SAF.saf) (h:CS.t) =
   let result,actions=inf' info c s h in
      if !debug_supinf_steps then
         begin
            eprintf"inf: %a <= %a@." SAF.print result SAF.print s
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

let ge2af var2index (i,t) =
	let left,right=dest_ge_rat t in
	let f1=linear2af var2index left in
	let f2=linear2af var2index right in
	let neg_f2=AF.scale (neg fieldUnit) f2 in
	AF.hypSource i (AF.add f1 neg_f2)

let rec make_sacs_aux i l = function
	[] -> l
 | hd::tl ->
		let i' = succ i in
		match hd with
			Hypothesis (_, t) ->
				if is_ge_rat_term t then
					make_sacs_aux i' ((i,t)::l) tl
				else
					make_sacs_aux i' l tl
		 | Context _ -> make_sacs_aux i' l tl

let make_sacs var2index p =
   let hyps = Term.SeqHyp.to_list (Sequent.explode_sequent p).sequent_hyps in
	let ihyps = make_sacs_aux 1 [] hyps in
	let afs=List.map (ge2af var2index) ihyps in
	List.fold_left SACS.addConstr SACS.empty afs

module TermPos=
struct
	type data = int
	let append l1 l2 = l1 @ l2
end

module TTable=Term_eq_table.MakeTermTable(TermPos)

let mem h t = TTable.mem !h t
let add h t d = h:=(TTable.add !h t d)
let empty _ = ref (TTable.empty)

(*
let assert_geT info history f1 f2 = funT (fun p ->
	let t=(mk_ge_rat_term (SAF.term_of info f1) (SAF.term_of info f2)) in
	if mem history t then
		idT
	else
		begin
			add history t ((Sequent.hyp_count p)+1);
			assertT t
		end
)
*)

let runAssertT info (history,wf) label f1 f2 tac =
   funT (fun p ->
         if tac==idT then
            let left=SAF.term_of info f1 in
            let right=SAF.term_of info f2 in
            let t=(mk_ge_rat_term left right) in
               if mem history t then
                  idT
               else
               if mem wf left then
                  if mem wf right then
                     begin
                        add history t ((Sequent.hyp_count p)+1);
                        assertT t thenAT (addHiddenLabelT label)
                     end
                  else
                     begin
                        add wf right ((Sequent.hyp_count p)+1);
                        add history t ((Sequent.hyp_count p)+2);
                        let rmem=mk_equal_term rationals_term right right in
                           assertT rmem thenMT (assertT t thenAT (addHiddenLabelT label))
                     end
               else
               if mem wf right then
                  begin
                     add wf left ((Sequent.hyp_count p)+1);
                     add history t ((Sequent.hyp_count p)+2);
                     let lmem=mk_equal_term rationals_term left left in
                        assertT lmem thenMT (assertT t thenAT (addHiddenLabelT label))
                  end
               else
                  begin
                     add wf left ((Sequent.hyp_count p)+1);
                     add wf right ((Sequent.hyp_count p)+2);
                     add history t ((Sequent.hyp_count p)+3);
                     let lmem=mk_equal_term rationals_term left left in
                     let rmem=mk_equal_term rationals_term right right in
                        assertT lmem thenMT assertT rmem thenMT (assertT t thenAT (addHiddenLabelT label))
                  end
(*		assert_geT info history f1 f2 thenAT (addHiddenLabelT label)*)
         else
            let left=SAF.term_of info f1 in
            let right=SAF.term_of info f2 in
            let t=(mk_ge_rat_term left right) in
               if mem history t then
                  idT
               else
               if mem wf left then
                  if mem wf right then
                     begin
                        add history t ((Sequent.hyp_count p)+1);
                        assertT t thenAT (addHiddenLabelT label thenT tac)
                     end
                  else
                     begin
                        add wf right ((Sequent.hyp_count p)+1);
                        add history t ((Sequent.hyp_count p)+2);
                        let rmem=mk_equal_term rationals_term right right in
                           assertT rmem thenMT (assertT t thenAT (addHiddenLabelT label thenT tac))
                     end
               else
               if mem wf right then
                  begin
                     add wf left ((Sequent.hyp_count p)+1);
                     add history t ((Sequent.hyp_count p)+2);
                     let lmem=mk_equal_term rationals_term left left in
                        assertT lmem thenMT (assertT t thenAT (addHiddenLabelT label thenT tac))
                  end
               else
                  begin
                     add wf left ((Sequent.hyp_count p)+1);
                     add wf right ((Sequent.hyp_count p)+2);
                     add history t ((Sequent.hyp_count p)+3);
                     let lmem=mk_equal_term rationals_term left left in
                     let rmem=mk_equal_term rationals_term right right in
                        assertT lmem thenMT assertT rmem thenMT (assertT t thenAT (addHiddenLabelT label thenT tac))
                  end
(*		assert_geT info history f1 f2 thenAT (addHiddenLabelT label thenT tac)*)
   )

let rec runAssertStepT info h label tac f1 f2 =
	let src1,f1'=f1 in
	let src2,f2'=f2 in
   match f1',f2' with
      SAF.Affine _, SAF.Affine _ -> runAssertT info h label f1 f2 tac
    |	SAF.Affine _, SAF.Max(s21,s22) -> runAssertStepListT info h label tac [(f1,s21);(f1,s22)]
    | SAF.Min(s11,s12), SAF.Affine _ -> runAssertStepListT info h label tac [(s11,f2);(s12,f2)]
    | SAF.Min(s11,s12),SAF.Max(s21,s22) ->
         runAssertStepListT info h label tac [(s11,s21);(s11,s22);(s12,s21);(s12,s22)]
    | SAF.Max(s11,s12),SAF.Max(s21,s22) -> runAssertStepListT info h label tac [(s11,s21);(s12,s22)]
    | SAF.Min(s11,s12),SAF.Min(s21,s22) -> runAssertStepListT info h label tac [(s11,s21);(s12,s22)]
    | _,_ -> idT(*runAssertT info label f1 f2 tac*)

and runAssertStepListT info h label tac = function
   [(f1,f2)] -> runAssertStepT info h label tac f1 f2
 | (f1,f2)::tl ->
      runAssertStepT info h label tac f1 f2 thenMT (runAssertStepListT info h label tac tl)
 | [] -> raise (Invalid_argument "runAssertStepListT applied to an empty list")

let runTransitiveT info h label f1 f2 f3 =
	try
		runAssertT info h label f1 f3 (geTransitive (SAF.term_of info f2))
	with RefineError(a,b) ->
		begin
			eprintf"RefineError caught in runTransitiveT";
			raise (RefineError(a,b))
		end

let rec runTransitiveStepT info h label f1 f2 f3 =
	let src1,f1'=f1 in
	let src2,f2'=f2 in
	let src2,f3'=f3 in
   match f1',f2',f3' with
      SAF.Affine _, SAF.Affine _, SAF.Affine _ -> runTransitiveT info h label f1 f2 f3
    |	_, SAF.Max(s21,s22), SAF.Max(s31,s32) -> runTransitiveStepListT info h label [(f1,s21,s31);(f1,s22,s32)]
    |	SAF.Min (s11,s12), SAF.Min(s21,s22), _ -> runTransitiveStepListT info h label [(s11,s21,f3);(s12,s22,f3)]
    |	_, SAF.Affine _, SAF.Max(s31,s32) -> runTransitiveStepListT info h label [(f1,f2,s31);(f1,f2,s32)]
    |	SAF.Min (s11,s12), SAF.Affine _, _ -> runTransitiveStepListT info h label [(s11,f2,f3);(s12,f2,f3)]
    | _,_,_ -> idT(*runTransitiveT info label f1 f2 f3*)

and runTransitiveStepListT info h label = function
   [(f1,f2,f3)] -> runTransitiveStepT info h label f1 f2 f3
 | (f1,f2,f3)::tl ->
      runTransitiveStepT info h label f1 f2 f3 thenMT (runTransitiveStepListT info h label tl)
 | [] -> raise (Invalid_argument "runTransitiveStepListT applied to an empty list")

let rec runListT info h = function
   [] -> idT
 | [SAF.Assert (label,f1,f2,tac)] ->
      begin
         if !debug_supinf_steps then
            (eprintf "%s %a >= %a@." label SAF.print f1 SAF.print f2);
         if SAF.isInfinite f1 || SAF.isInfinite f2 then
            idT
         else
            runAssertStepT info h label tac f1 f2
      end
 | [SAF.Transitive (label,f1,f2,f3)] ->
      begin
         if !debug_supinf_steps then
            (eprintf "%s %a >= %a >= %a@." (**)
                label
                SAF.print f1
                SAF.print f2
                SAF.print f3);
         if SAF.isInfinite f1 || SAF.isInfinite f2 || SAF.isInfinite f3 then
            idT
         else
            runTransitiveStepT info h label f1 f2 f3
      end
 | [SAF.Tactic(label,tac)] ->
      begin
         if !debug_supinf_steps then
            eprintf "%s%t" label eflush;
         addHiddenLabelT label thenT tac
      end
 | (SAF.Assert (label,f1,f2,tac))::tl ->
      begin
         if !debug_supinf_steps then
            (eprintf "%s %a >= %a@." label SAF.print f1 SAF.print f2);
         if SAF.isInfinite f1 || SAF.isInfinite f2 then
            runListT info h tl
         else
            runAssertStepT info h label tac f1 f2 thenMT (runListT info h tl)
      end
 | (SAF.Transitive (label,f1,f2,f3))::tl ->
      begin
         if !debug_supinf_steps then
            (eprintf "%s %a >= %a >= %a@." (**)
                label
                SAF.print f1
                SAF.print f2
                SAF.print f3);
         if SAF.isInfinite f1 || SAF.isInfinite f2 || SAF.isInfinite f3 then
            runListT info h tl
         else
            runTransitiveStepT info h label f1 f2 f3 thenMT (runListT info h tl)
      end
 | (SAF.Tactic(label,tac))::tl ->
      begin
         if !debug_supinf_steps then
            eprintf "%s%t" label eflush;
         addHiddenLabelT label thenT (tac thenMT (runListT info h tl))
      end

let resource intro += [
	<<ge_rat{rat{number[i:n];number[j:n]}; rat{number[k:n];number[l:n]}}>>, wrap_intro (rw reduceC 0);
	<<lt_rat{rat{number[i:n];number[j:n]}; rat{number[k:n];number[l:n]}}>>, wrap_intro (rw reduceC 0);
	<<gt_rat{rat{number[i:n];number[j:n]}; rat{number[k:n];number[l:n]}}>>, wrap_intro (rw reduceC 0);
	<<le_rat{rat{number[i:n];number[j:n]}; rat{number[k:n];number[l:n]}}>>, wrap_intro (rw reduceC 0);
]

interactive ge2leftMin 'H 'J :
	[wf] sequent { <H>; ge_rat{'a; 'c}; <J>; ge_rat{'b; 'c}; <K> >- 'a in rationals } -->
	[wf] sequent { <H>; ge_rat{'a; 'c}; <J>; ge_rat{'b; 'c}; <K> >- 'b in rationals } -->
	[wf] sequent { <H>; ge_rat{'a; 'c}; <J>; ge_rat{'b; 'c}; <K> >- 'c in rationals } -->
	sequent { <H>; ge_rat{'a; 'c}; <J>; ge_rat{'b; 'c}; <K>; ge_rat{min_rat{'a;'b}; 'c} >- 'C } -->
	sequent { <H>; ge_rat{'a; 'c}; <J>; ge_rat{'b; 'c}; <K> >- 'C }

let ge2leftMinT i j = funT (fun p ->
	let i=Sequent.get_pos_hyp_num p i in
	let j=Sequent.get_pos_hyp_num p j in
   begin
		if !debug_supinf_steps then
			let h1=Sequent.nth_hyp p i in
			let h2=Sequent.nth_hyp p j in
			eprintf "ge2leftMinT %i %i on %s %s@." i j
				(SimplePrint.short_string_of_term h1)
				(SimplePrint.short_string_of_term h2)
	end;
	ge2leftMin i (j-i)
)

interactive ge2rightMax 'H 'J :
	[wf] sequent { <H>; ge_rat{'a; 'b}; <J>; ge_rat{'a; 'c}; <K> >- 'a in rationals } -->
	[wf] sequent { <H>; ge_rat{'a; 'b}; <J>; ge_rat{'a; 'c}; <K> >- 'b in rationals } -->
	[wf] sequent { <H>; ge_rat{'a; 'b}; <J>; ge_rat{'a; 'c}; <K> >- 'c in rationals } -->
	sequent { <H>; ge_rat{'a; 'b}; <J>; ge_rat{'a; 'c}; <K>; ge_rat{'a; max_rat{'b;'c}} >- 'C } -->
	sequent { <H>; ge_rat{'a; 'b}; <J>; ge_rat{'a; 'c}; <K> >- 'C }

let ge2rightMaxT i j = funT (fun p ->
	let i=Sequent.get_pos_hyp_num p i in
	let j=Sequent.get_pos_hyp_num p j in
   begin
		if !debug_supinf_steps then
			let h1=Sequent.nth_hyp p i in
			let h2=Sequent.nth_hyp p j in
			eprintf "ge2rightMaxT %i %i on %s %s@." i j
				(SimplePrint.short_string_of_term h1)
				(SimplePrint.short_string_of_term h2)
	end;
	ge2rightMax i (j-i)
)

interactive ge2transitive 'H 'J :
	[wf] sequent { <H>; ge_rat{'a; 'b}; <J>; ge_rat{'b; 'c}; <K> >- 'a in rationals } -->
	[wf] sequent { <H>; ge_rat{'a; 'b}; <J>; ge_rat{'b; 'c}; <K> >- 'b in rationals } -->
	[wf] sequent { <H>; ge_rat{'a; 'b}; <J>; ge_rat{'b; 'c}; <K> >- 'c in rationals } -->
	sequent { <H>; ge_rat{'a; 'b}; <J>; ge_rat{'b; 'c}; <K>; ge_rat{'a; 'c} >- 'C } -->
	sequent { <H>; ge_rat{'a; 'b}; <J>; ge_rat{'b; 'c}; <K> >- 'C }

let ge2transitiveT i j = funT (fun p ->
	let i=Sequent.get_pos_hyp_num p i in
	let j=Sequent.get_pos_hyp_num p j in
   begin
		if !debug_supinf_steps then
			let h1=Sequent.nth_hyp p i in
			let h2=Sequent.nth_hyp p j in
			eprintf "ge2transitiveT %i %i on %s %s@." i j
				(SimplePrint.short_string_of_term h1)
				(SimplePrint.short_string_of_term h2)
	end;
	ge2transitive i (j-i)
)

let ge_normC = (addrC [0] normalizeC) thenC (addrC[1] normalizeC)

interactive_rw extract2left 't :
	('a in rationals) -->
	('b in rationals) -->
	('t in rationals) -->
	ge_rat{'a; 'b} <-->
	ge_rat{'t; add_rat{'t; sub_rat{'b; 'a}}}

let extract2leftC t = extract2left t thenC ge_normC

interactive_rw extract2right 't :
	('a in rationals) -->
	('b in rationals) -->
	('t in rationals) -->
	ge_rat{'a; 'b} <-->
	ge_rat{add_rat{'t; sub_rat{'a; 'b}}; 't}

let extract2rightC t = extract2right t thenC ge_normC

interactive_rw positive_multiply_ge 'c :
	('a in rationals) -->
	('b in rationals) -->
	(gt_rat{'c; rat{0;1}}) -->
	ge_rat{'a; 'b} <--> ge_rat{mul_rat{'c; 'a}; mul_rat{'c; 'b}}

interactive_rw negative_multiply_ge 'c :
	('a in rationals) -->
	('b in rationals) -->
	(lt_rat{'c; rat{0;1}}) -->
	ge_rat{'a; 'b} <--> ge_rat{mul_rat{'c; 'b}; mul_rat{'c; 'a}}

interactive_rw ge_addMono_rw 'c :
	('a in rationals) -->
	('b in rationals) -->
	('c in rationals) -->
	ge_rat{'a; 'b} <--> ge_rat{add_rat{'c; 'a}; add_rat{'c; 'b}}

interactive ge_addMono2 'H 'J :
	[wf] sequent { <H>; ge_rat{'a; 'b}; <J>; ge_rat{'c; 'd}; <K> >- 'a in rationals } -->
	[wf] sequent { <H>; ge_rat{'a; 'b}; <J>; ge_rat{'c; 'd}; <K> >- 'b in rationals } -->
	[wf] sequent { <H>; ge_rat{'a; 'b}; <J>; ge_rat{'c; 'd}; <K> >- 'c in rationals } -->
	[wf] sequent { <H>; ge_rat{'a; 'b}; <J>; ge_rat{'c; 'd}; <K> >- 'd in rationals } -->
	sequent { <H>; ge_rat{'a; 'b}; <J>; ge_rat{'c; 'd}; <K>; ge_rat{add_rat{'a; 'c}; add_rat{'b; 'd}} >- 'C } -->
	sequent { <H>; ge_rat{'a; 'b}; <J>; ge_rat{'c; 'd}; <K> >- 'C }

let ge_addMono2T i j = funT (fun p ->
	let i=Sequent.get_pos_hyp_num p i in
	let j=Sequent.get_pos_hyp_num p j in
   begin
		if !debug_supinf_steps then
			let h1=Sequent.nth_hyp p i in
			let h2=Sequent.nth_hyp p j in
			eprintf "ge_addMono2T %i %i on %s %s@." i j
				(SimplePrint.short_string_of_term h1)
				(SimplePrint.short_string_of_term h2)
	end;
	ge_addMono2 i (j-i)
)

open Tree

let treeMapHelper n2 tac2 (n1,tac1) = n1+n2, (tac1 thenMT tac2)

let treeProductHelper (n1,tac1) (n2,tac2) =
	n1+n2+1, (tac1 thenMT tac2 thenMT ge_addMono2T (-n2-1) (-1) thenMT rw ge_normC (-1))

let treeMergeHelper (n1,tac1) (n2,tac2) =
	n1+n2+1, (tac1 thenMT tac2 thenMT ge2transitiveT (-n2-1) (-1))

let rec source2hyp info = function
	Signore ->
		if !debug_supinf_trace then
         eprintf "Signore reached source2hyp@.";
		Ignore
 | Shypothesis i ->
		if !debug_supinf_trace then
			eprintf "hyp %i@." i;
		Leaf(1, (copyHypT i (-1)))
 | Smin(Signore,s2) ->
		let result = source2hyp info s2 in
		if !debug_supinf_trace then
			eprintf "minRight %s@." (string_of_tree result);
		Right result
 | Smin(s1,Signore) ->
		let result = source2hyp info s1 in
		if !debug_supinf_trace then
			eprintf "minLeft %s@." (string_of_tree result);
		Left result
 | Smin(s1,s2) ->
		let result1 = source2hyp info s1 in
		let result2 = source2hyp info s2 in
		if !debug_supinf_trace then
			eprintf "min %s %s@." (string_of_tree result1) (string_of_tree result2);
		Pair(result1, result2)
 | Smax(Signore,s2) ->
		let result = source2hyp info s2 in
		if !debug_supinf_trace then
			eprintf "maxRight %s@." (string_of_tree result);
		Right result
 | Smax(s1,Signore) ->
		let result = source2hyp info s1 in
		if !debug_supinf_trace then
			eprintf "maxLeft %s@." (string_of_tree result);
		Left result
 | Smax(s1,s2) ->
		let result1 = source2hyp info s1 in
		let result2 = source2hyp info s2 in
		if !debug_supinf_trace then
			eprintf "max %s %s@." (string_of_tree result1) (string_of_tree result2);
		Pair(result1, result2)
 | Sleft(s) ->
		let result = source2hyp info s in
		if !debug_supinf_trace then
			eprintf "left %s@." (string_of_tree result);
		leftBranch result
 | Sright(s) ->
		let result = source2hyp info s in
		if !debug_supinf_trace then
			eprintf "right %s@." (string_of_tree result);
		rightBranch result
 | Sextract2left(vi,s) ->
		let result = source2hyp info s in
		let v = VI.restore info vi in
		if !debug_supinf_trace then
			eprintf "extrLeft %i %s %s@." vi (SimplePrint.short_string_of_term v) (string_of_tree result);
		treeMap (treeMapHelper 0 (rw (extract2leftC v) (-1))) result
 | Sextract2right(vi,s) ->
		let result = source2hyp info s in
		let v = VI.restore info vi in
		if !debug_supinf_trace then
			eprintf "extrRight %i %s %s@." vi (SimplePrint.short_string_of_term v) (string_of_tree result);
		treeMap (treeMapHelper 0 (rw (extract2rightC v) (-1))) result
 | StrivialConst c ->
		let ctm = term_of c in
		let tm = mk_ge_rat_term ctm ctm in
		if !debug_supinf_trace then
			eprintf "trivConst %s@." (SimplePrint.short_string_of_term ctm);
		Leaf(1, (assertT tm thenAT geReflexive))
 | StrivialVar vi ->
		let v = VI.restore info vi in
		let tm = mk_ge_rat_term v v in
		if !debug_supinf_trace then
			eprintf "trivVar %i %s@." vi (SimplePrint.short_string_of_term v);
		Leaf(1, (assertT tm thenAT geReflexive))
 | Sscale(c,s) ->
		let result = source2hyp info s in
		let tm = term_of c in
		if !debug_supinf_trace then
			eprintf "scale %a %s@." RationalBoundField.print c (string_of_tree result);
		if compare c fieldZero >0 then
			treeMap (treeMapHelper 0 (rw ((positive_multiply_ge tm) thenC ge_normC) (-1))) result
		else
			treeMap (treeMapHelper 0 (rw ((negative_multiply_ge tm) thenC ge_normC) (-1))) result
 | SaddVar(c,vi,s) ->
		let result = source2hyp info s in
		let v = VI.restore info vi in
		let tm = mk_mul_rat_term (term_of c) v in
		if !debug_supinf_trace then
			eprintf "addV %i %s %s@." vi (SimplePrint.short_string_of_term v) (string_of_tree result);
		treeMap (treeMapHelper 0 (rw ((ge_addMono_rw tm) thenC ge_normC) (-1))) result
 | Ssum(s1,s2) ->
		(* this case computes a product of two trees
		 * it should be consistent with SAF.add
		 *)
		let result1 = source2hyp info s1 in
		let result2 = source2hyp info s2 in
		if !debug_supinf_trace then
			eprintf "sum %s %s@." (string_of_tree result1) (string_of_tree result2);
		treeProduct treeProductHelper result1 result2
 | StransitiveLeft(s1,s2,vi) ->
		let result1 = source2hyp info s1 in
		let result2 = source2hyp info s2 in
		let v = VI.restore info vi in
		if !debug_supinf_trace then
			eprintf "tranL %i %s >= %s >= %s@." vi (string_of_tree result1) (string_of_tree result2) (SimplePrint.short_string_of_term v);
		treeMergeLeft treeMergeHelper result1 result2
 | StransitiveRight(vi,s1,s2) ->
		let result1 = source2hyp info s1 in
		let result2 = source2hyp info s2 in
		let v = VI.restore info vi in
		if !debug_supinf_trace then
			eprintf "tranR %i %s >= %s >= %s@." vi (SimplePrint.short_string_of_term v) (string_of_tree result1) (string_of_tree result2);
		treeMergeRight treeMergeHelper result1 result2
 | Scontradiction s ->
		let result = source2hyp info s in
		if !debug_supinf_trace then
			eprintf "contrad %s@." (string_of_tree result);
		result

let rec proj2 = function
	[] -> []
 | (a,b)::tail -> b::(proj2 tail)

let source2hypT info s = funT (fun p ->
	if !debug_supinf_trace then
		eprintf "%a@." print s;
	let result = source2hyp info s in
	let taclist = proj2 (treeFlatten result) in
	seqOnMT taclist thenMT rw normalizeC (-1)
)

let testT =
   funT (fun p ->
         let var2index = VI.create 13 in
         let constrs=make_sacs var2index p in
         let info=VI.invert var2index in
            if !debug_supinf_steps then
               begin
                  eprintf "Vars:\n%a\nSACS:\n%a@." (**)
                     VI.print var2index
                     SACS.print constrs
               end;
            begin
               let saf'=SAF.affine (AF.mk_var 1) in
               let sup',a1=sup info constrs saf' CS.empty in
					if SAF.isMinusInfinity sup' then
						let actions=List.rev a1 in
							begin
								if !debug_supinf_steps then
									begin
										eprintf "start=%a@." SAF.print saf';
										eprintf"sup=%a@." SAF.print sup';
										eprintf "%a <= %a@." (**)
											SAF.print saf'
											SAF.print sup'
									end;
								runListT info (empty (),empty ()) actions
							end
					else
						let inf',a2=inf info constrs saf' CS.empty in
						let actions=List.rev (SAF.Transitive("final",sup',(SAF.affine (AF.mk_var 1)),inf')::(a1@a2)) in
							begin
								if !debug_supinf_steps then
									begin
										eprintf "start=%a@." SAF.print saf';
										eprintf"sup=%a@." SAF.print sup';
										eprintf"inf=%a@." SAF.print inf';
										eprintf "%a <= %a <= %a@." (**)
											SAF.print inf'
											SAF.print saf'
											SAF.print sup'
									end;
								runListT info (empty (),empty ()) actions
							end
            end
   )

let test2T =
   funT (fun p ->
         let var2index = VI.create 13 in
         let constrs=make_sacs var2index p in
         let info=VI.invert var2index in
            if !debug_supinf_steps then
               begin
                  eprintf "Vars:\n%a\nSACS:\n%a@." (**)
                     VI.print var2index
                     SACS.print constrs
               end;
            begin
               let saf'=SAF.affine (AF.mk_var 1) in
               let sup',a1=sup info constrs saf' CS.empty in
					if SAF.isMinusInfinity sup' then
						begin
							let src=SAF.getSource sup' in
							if !debug_supinf_steps then
								begin
									eprintf "start=%a@." SAF.print saf';
									eprintf"sup=%a@." SAF.print sup';
									eprintf "%a <= %a@." (**)
										SAF.print saf'
										SAF.print sup';
								end;
							source2hypT info src
						end
					else
						let inf',a2=inf info constrs saf' CS.empty in
						begin
							let src=SAF.getSource inf' in
							if !debug_supinf_steps then
								begin
									eprintf "start=%a@." SAF.print saf';
									eprintf"sup=%a@." SAF.print sup';
									eprintf"inf=%a@." SAF.print inf';
									eprintf "%a <= %a <= %a@." (**)
										SAF.print inf'
										SAF.print saf'
										SAF.print sup';
								end;
							if (SAF.isPlusInfinity inf') then
								source2hypT info src
							else
								let supsrc=SAF.getSource sup' in
								let sup_tm=SAF.term_of info sup' in
								let inf_tm=SAF.term_of info inf' in
								let tm=mk_ge_rat_term sup_tm inf_tm in
								source2hypT info supsrc thenMT
								source2hypT info src thenMT
								(assertT tm thenAT geTransitive (VI.restore info 1)) thenMT
								rw normalizeC (-1)
						end
            end
   )

let ge_int2ratT = argfunT (fun i p ->
	if is_ge_term (Sequent.nth_hyp p i) then
		rw (int2ratC thenC ge_normC) i
	else
		idT
)
(*
let term2term_number p t =
	let es={sequent_args=t; sequent_hyps=(SeqHyp.of_list []); sequent_goals=(SeqGoal.of_list [t])} in
	let s=mk_sequent_term es in
	let s'=Top_conversionals.apply_rewrite p normalizeC s in
	let t'=SeqGoal.get (TermMan.explode_sequent s').sequent_goals 0 in
	begin
		if !debug_int_arith then
			eprintf "t2t_n: %a -> %a%t" print_term t print_term t' eflush;
		if is_add_term t' then
			let a,b=dest_add t' in
			if is_number_term a then
				(b,dest_number a)
			else
				(t',num0)
		else
			if is_number_term t' then
				(mk_number_term num0, dest_number t')
			else
				(t',num0)
	end

let findContradRelT = funT ( fun p ->
	let l = all2ge p in
	let l' = List.map (four2inequality p) l in
)

type HypPosition = Unused | Original of int | Normed of int

let empty_hyps _ = (0, Array.create 13 Unused)
*)
let preT = funT (fun p ->
   arithRelInConcl2HypT thenMT
   ((tryOnAllMCumulativeHypsT negativeHyp2ConclT) thenMT
	all2geT thenMT
	tryOnAllMHypsT ge_int2ratT)
)

let coreT = test2T
let core2T = test2T
let supinfT = preT thenMT core2T

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
					ge_rat{add_rat{rat{-1;1}; mul_rat{rat{-1;1};'y}};neg_rat{'x}}
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

interactive inttest 'a 'b 'c :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H> >- 'c in int } -->
sequent { <H>; x: ('a >= ('b +@ 1));
                     t: ('c >= ('b +@ 3));
                     u: ('b >= ('a +@ 0))
                >- "assert"{bfalse} }

interactive inttest2 'a 'b 'c :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H> >- 'c in int } -->
sequent { <H>; x: (('b +@ 1) <= 'a);
                     t: ('c > ('b +@ 2));
                     u: ('b >= ('a +@ 0))
                >- "assert"{bfalse} }

interactive inttest3 'a 'b 'c :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H> >- 'c in int } -->
sequent { <H>; x: (('b +@ 1) <= 'a);
                     t: ('c > ('b +@ 2))
                >- ('b < ('a +@ 0))  }

interactive inttest4 'a 'b :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H>; x: ('a >= 'b);
                     t: ('a < 'b)
                >- "assert"{bfalse} }

interactive inttest5 'a 'b :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H>; x: ('a >= 'b +@ 0);
                     t: ('a < 'b)
                >- "assert"{bfalse} }

interactive inttest6 'b 'c :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H> >- 'c in int } -->
sequent { <H>; x: (('c *@ ('b +@ ('a *@ 'c)) +@ ('b *@ 'c)) >= 'b +@ 0);
                     t: (((((('c *@ 'b) *@ 1) +@ (2 *@ ('a *@ ('c *@ 'c)))) +@
 (('c *@ ((-1) *@ 'a)) *@ 'c)) +@ ('b *@ 'c)) < 'b)
                >- "assert"{bfalse} }

interactive inttest7 :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H>; 'a < 'b >- 'a <> 'b }

interactive inttest8 :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H>; 'a < 'b >- not{'a = 'b in int} }

interactive inttest9 :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H>; not{'a < 'b} >- 'a >= 'b }

interactive inttest10 :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H>; 'a <> 'b >- 'a <> 'b }

interactive inttestn :
	sequent {'v  in int;
				'v1 in int;
				'v2 in int;
				'v3 in int;
				'v4 in int;
				'v5 in int;
				'v6 in int;
				'v7 in int;
				'v8 in int;
				'v9 in int; "assert"{bfalse} >- "assert"{bfalse} }

interactive inttestn2 :
	sequent {v: int;
				v1: int;
				v2: int;
				v3: int;
				v4: int;
				v5: int;
				v6: int;
				v7: int;
				v8: int;
				v9: int; "assert"{bfalse} >- "assert"{bfalse} }
