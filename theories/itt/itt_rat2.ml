extends Itt_rat

open Term_order
open Basic_tactics
open Itt_int_base
open Itt_rat

module TO = TermOrder (Refiner.Refiner)
open TO

interactive_rw sum_same_products_rat1_rw :
   ('a in rationals) -->
   add_rat{mul_rat{rat{number[i:n]; number[j:n]}; 'a}; mul_rat{rat{number[k:n]; number[l:n]}; 'a}} <-->
   mul_rat{add_rat{rat{number[i:n]; number[j:n]}; rat{number[k:n]; number[l:n]}}; 'a}

let sum_same_products_rat1C = sum_same_products_rat1_rw thenC (addrC [0] reduce_add)

interactive_rw sum_same_products_rat2_rw :
   ('a in rationals) -->
   add_rat{mul_rat{rat{number[i:n]; number[j:n]}; 'a}; 'a} <--> mul_rat{add_rat{rat{number[i:n]; number[j:n]}; rat{1; 1}}; 'a}

let sum_same_products_rat2C = sum_same_products_rat2_rw thenC (addrC [0] reduce_add)

interactive_rw sum_same_products_rat3_rw :
   ('a in rationals) -->
   add_rat{'a; mul_rat{rat{number[i:n]; number[j:n]}; 'a}} <--> mul_rat{add_rat{rat{number[i:n]; number[j:n]}; rat{1; 1}}; 'a}

let sum_same_products_rat3C = sum_same_products_rat3_rw thenC (addrC [0] reduce_add)

interactive_rw sum_same_products_rat4_rw :
   ('a in rationals) -->
   add_rat{'a; 'a} <--> mul_rat{rat{2;1}; 'a}

let sum_same_products_rat4C = sum_same_products_rat4_rw

interactive_rw add_rat_BubblePrimitive_rw :
   ( 'a in rationals ) -->
   ( 'b in rationals ) -->
   ( 'c in rationals ) -->
   add_rat{'a; add_rat{'b; 'c}} <--> add_rat{'b; add_rat{'a; 'c}}

let add_rat_BubblePrimitiveC = add_rat_BubblePrimitive_rw

let is_rat_number_term t =
	let a,b=dest_rat t in
	(is_number_term a) && (is_number_term b)

let stripRatCoef t =
	if is_mul_rat_term t then
      let (c,t')=dest_mul_rat t in
      if (is_rat_number_term c) then
         t'
      else
         t
   else
      t

let add_rat_Swap1C t =
	match explode_term t with
		<<add_rat{'a; 'b}>> when (compare_terms (stripRatCoef b) (stripRatCoef a))=Less -> add_rat_CommutC
	 | _ -> failC

let add_rat_Swap2C t =
	match explode_term t with
		<<add_rat{'a; 'b}>> ->
			(match explode_term b with
				<<add_rat{'c; 'd}>> when (compare_terms (stripRatCoef c) (stripRatCoef a))=Less -> add_rat_BubblePrimitiveC
			 | _ -> failC
			)
	 | _ -> failC

interactive_rw mul_rat_BubblePrimitive_rw :
   ( 'a in rationals ) -->
   ( 'b in rationals ) -->
   ( 'c in rationals ) -->
   mul_rat{'a; mul_rat{'b; 'c}} <--> mul_rat{'b; mul_rat{'a; 'c}}

let mul_rat_BubblePrimitiveC = mul_rat_BubblePrimitive_rw

let mul_rat_Swap1C t =
	match explode_term t with
		<<mul_rat{'a; 'b}>> when (compare_terms b a)=Less -> mul_rat_CommutC
	 | _ -> failC

let mul_rat_Swap2C t =
	match explode_term t with
		<<mul_rat{'a; 'b}>> ->
			(match explode_term b with
				<<mul_rat{'c; 'd}>> when (compare_terms c a)=Less -> mul_rat_BubblePrimitiveC
			 | _ -> failC
			)
	 | _ -> failC

let resource arith_unfold +=[
   << add_rat{rat{'a;'b}; rat{'c;'d}} >>, (reduce_add_rat thenC reduceC);
   << mul_rat{rat{'a;'b}; rat{'c;'d}} >>, (reduce_mul_rat thenC reduceC);
   << neg_rat{rat{'a;'b}} >>, reduce_neg_rat;
	<< inv_rat{rat{'a;'b}} >>, reduce_inv_rat;

	<<rat_of_int{'a}>>, unfold_rat_of_int;
	<<add_rat{'a; rat{0; 1}}>>, add_rat_IdC;
	<<add_rat{rat{0; 1}; 'a}>>, add_rat_Id2C;
	<<mul_rat{'a; add_rat{'b; 'c}}>>, mul_rat_add_DistribC;
	<<mul_rat{add_rat{'a; 'b}; 'c}>>, mul_rat_add_Distrib3C;

	<<mul_rat{'a; 'b}>>, termC mul_rat_Swap1C;
	<<mul_rat{'a; mul_rat{'b; 'c}}>>, termC mul_rat_Swap2C;
	<<mul_rat{'a; rat{number[i:n]; number[k:n]}}>>, mul_rat_CommutC;
	<<mul_rat{rat{number[i:n]; number[k:n]}; mul_rat{rat{number[j:n]; number[l:n]}; 'c}}>>, (mul_rat_AssocC thenC (addrC [0] reduceC));

	<<add_rat{'a; 'b}>>, termC add_rat_Swap1C;
	<<add_rat{'a; add_rat{'b; 'c}}>>, termC add_rat_Swap2C;
	<<add_rat{'a; rat{number[i:n]; number[k:n]}}>>, add_rat_CommutC;
	<<add_rat{rat{number[i:n]; number[k:n]}; add_rat{rat{number[j:n]; number[l:n]}; 'c}}>>, (add_rat_AssocC thenC (addrC [0] reduceC));

	<<add_rat{add_rat{'a; 'b}; 'c}>>, add_rat_Assoc2C;
	<<mul_rat{mul_rat{'a; 'b}; 'c}>>, mul_rat_Assoc2C;

	<<add_rat{mul_rat{rat{number[i:n]; number[k:n]}; 'a}; mul_rat{rat{number[j:n]; number[l:n]}; 'a}}>>, sum_same_products_rat1C;
	<<add_rat{mul_rat{rat{number[i:n]; number[k:n]}; 'a}; 'a}>>, sum_same_products_rat2C;
	<<add_rat{'a; mul_rat{rat{number[j:n]; number[l:n]}; 'a}}>>, sum_same_products_rat3C;
	<<add_rat{'a; 'a}>>, sum_same_products_rat4C;

	<<add_rat{mul_rat{rat{number[i:n]; number[k:n]}; 'a}; add_rat{mul_rat{rat{number[j:n]; number[l:n]}; 'a}; 'b}}>>, (add_rat_AssocC thenC (addrC [0] sum_same_products_rat1C));
	<<add_rat{mul_rat{rat{number[i:n]; number[k:n]}; 'a}; add_rat{'a; 'b}}>>, (add_rat_AssocC thenC (addrC [0] sum_same_products_rat2C));
	<<add_rat{'a; add_rat{mul_rat{rat{number[i:n]; number[k:n]}; 'a}; 'b}}>>, (add_rat_AssocC thenC (addrC [0] sum_same_products_rat3C));
	<<add_rat{'a; add_rat{'a; 'b}}>>, (add_rat_AssocC thenC (addrC [0] sum_same_products_rat4C));
]

interactive test1 :
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   [wf] sequent { <H> >- 'c in rationals } -->
   sequent { <H> >- mul_rat{'b; add_rat{'c; add_rat{'a; mul_rat{'a; rat_of_int{1}}}}} in rationals }
