doc <:doc<
   @begin[doc]
   @module[Itt_relation_str]

   The @tt[Itt_relation_str] module defines algebraic structures such as
   ordered sets, @misspelled{PERs}, types with decidable equality and so on.
   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.

   Copyright (C) 1998 Jason Hickey, Cornell University

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

   Author: Alexei Kopylov
   @email{apk6@cs.cornell.edu}
   @end[license]
>>

doc <:doc<
   @begin[doc]
   @parents
   @end[doc]
>>
extends Itt_equal
extends Itt_int_ext
extends Itt_decidable
extends Itt_record
extends Itt_algebra_df
extends Itt_logic
extends Itt_bisect
extends Itt_comment
doc <:doc< @docoff >>

open Basic_tactics

open Itt_struct

let dByDefT  unfold n = rw unfold n thenT dT n
let dByRecDefT term unfold n = dByDefT unfold n thenT rwhAll (makeFoldC term unfold)

let soft_elim term unfold = term, (dByDefT unfold)
let soft_into term unfold = term, (dByDefT unfold 0)
let softrec_elim term unfold = term, (dByRecDefT term unfold)
let softrec_into term unfold = term, (dByRecDefT term unfold 0)

let reduceByDefC unfold =   unfold thenC reduceTopC
let reduceByRecDefC term unfold = reduceByDefC unfold thenC higherC (makeFoldC term unfold)

let soft_reduce term unfold  = term, (reduceByDefC unfold)
let softrec_reduce term unfold  = term, (reduceByRecDefC term unfold)

doc <:doc<
   @begin[doc]
   @modsection{Order}
   @modsubsection{Definition}
   Order is a type  <<label["car":t]>> with an irreflexive transitive complete
  relation:
     $$<<label["<":t]>>  : <<label["car":t]-> label["car":t] -> bool>>$$
   @end[doc]
>>

define preorder : preorder[i:l] <-->
    { car : univ[i:l];
      "<=" : ^car -> ^car -> bool ;
      all x:^car. "assert"{'x ^<= 'x};
      all x:^car.all y:^car.all z:^car. ("assert"{'x ^<= 'y} &  "assert"{'y ^<= 'z} =>  "assert"{'x ^<= 'z});
      all x:^car.all y:^car. ("assert"{'x ^<= 'y} or  "assert"{'y ^<= 'x})
    }


(*
define irreflexiveOrder1 :  IrreflexiveOrder[i:l] <--> { self : orderSig[i:l] | all x:^car. not{"assert"{'x ^< 'x}}}

define transitiveOrder1 :  TransitiveOrder[i:l] <--> { self : orderSig[i:l] | all x:^car.all y:^car.all z:^car. ("assert"{'x ^< 'y} &  "assert"{'y ^< 'z} =>  "assert"{'x ^< 'z})}

define partialOrder1 : PartialOrder[i:l] <--> bisect{ IrreflexiveOrder[i:l]; TransitiveOrder[i:l]}

dform iorder_df : except_mode[src] :: IrreflexiveOrder[i:l] = `"IrreflexiveOrder" sub{slot[i:l]}
dform torder_df : except_mode[src] :: TransitiveOrder[i:l] = `"TransitiveOrder" sub{slot[i:l]}
dform porder_df : except_mode[src] :: PartialOrder[i:l] = `"PartialOrder" sub{slot[i:l]}

define order1 : order[i:l] <-->  { self : PartialOrder[i:l] | all x:^car.all y:^car. ("assert"{'x ^< 'y} or  "assert"{'y ^< 'x} or 'x='y in ^car) }
*)

doc <:doc< @docoff >>

define le: le{'self; 'a;'b} <--> "assert"{'b ^<= 'a}

define eq: eq{'self; 'a;'b} <--> le{'self; 'a;'b} and le{'self; 'b; 'a}

define less: less{'self; 'a;'b} <--> le{'self; 'a; 'b} and not{eq{'self;'a;'b}}



let resource reduce += <<less{rcrd[x:t]{'f;'r};'a;'b}>> , (less thenC addrC [Subterm 1; Subterm 1; Subterm 1] reduceTopC)

dform less_df : parens :: except_mode[src] :: less{'self; 'a;'b}
 = 'a  bf[" <"]sub{'self} `" " 'b

doc <:doc<
   @begin[doc]
   @modsection{Decidable Equality}
   @modsubsection{Definition}
   @tt[DecEquality] is a type (@tt[car]) with an equality solver:
  $$<<label["=":t]>> : <<label[car:t]-> label[car:t] -> bool>>$$
   @end[doc]
>>

define decEquality : DecEquality[i:l] <-->
    { car : univ[i:l];
      "=" : ^car -> ^car -> bool;
       all x:^car. all y:^car. iff{"assert"{'x ^= 'y}; 'x='y in ^car}
    }

doc <:doc< @docoff >>

dform preorder_df : except_mode[src] :: preorder[i:l] = `"preOrder" sub{slot[i:l]}

dform deq_df : except_mode[src] ::  DecEquality[i:l] = `"DecEquality" sub{slot[i:l]}

let fold_less = makeFoldC <<less{'self; 'a;'b}>> less
(*
let irreflexiveOrder = irreflexiveOrder1 thenC higherC fold_less

let transitiveOrder = transitiveOrder1 thenC higherC fold_less
*)
let order = preorder thenC higherC fold_less

let resource elim += soft_elim <<preorder[i:l]>> order

doc "doc"{rules}

interactive le_wf  {| intro[intro_typeinf <<'ord>>] |} preorder[i:l] :
   [wf] sequent { <H> >- 'ord in preorder[i:l] }  -->
   [wf] sequent { <H> >- 'x in 'ord^car }  -->
   [wf] sequent { <H> >- 'y in 'ord^car }  -->
   sequent { <H> >- 'x <=['ord] 'y in bool}

interactive less_prop_wf  {| intro[intro_typeinf <<'ord>>] |} preorder[i:l] :
   [wf] sequent { <H> >- 'ord in preorder[i:l] }  -->
   [wf] sequent { <H> >- 'x in 'ord^car }  -->
   [wf] sequent { <H> >- 'y in 'ord^car }  -->
   sequent { <H> >- "type"{less{'ord;'x; 'y}} }

interactive car_wf  {| intro[intro_typeinf <<'ord>>] |} preorder[i:l] :
   [wf] sequent { <H> >- 'ord in preorder[i:l] }  -->
   sequent { <H> >- "type"{'ord^car} }

interactive car_univ  {| intro[intro_typeinf <<'ord>>] |} preorder[i:l] :
   [wf] sequent { <H> >- 'ord in preorder[i:l] }  -->
   sequent { <H> >- 'ord^car in univ[i:l] }

interactive eq_prop_wf  {| intro[intro_typeinf <<'ord>>] |} preorder[i:l] :
   [wf] sequent { <H> >- 'ord in preorder[i:l] }  -->
   [wf] sequent { <H> >- 'x in 'ord^car }  -->
   [wf] sequent { <H> >- 'y in 'ord^car }  -->
   sequent { <H> >- "type"{eq{'ord;'x; 'y}} }

interactive eq_refl  {| intro[intro_typeinf <<'ord>>] |} preorder[i:l] :
   [wf] sequent { <H> >- 'ord in preorder[i:l] }  -->
   [wf] sequent { <H> >- 'x in 'ord^car }  -->
   sequent { <H> >- eq{'ord;'x; 'x} }

define compare: compare{'self; 'a;'b; 'less_case; 'equal_case; 'greater_case} <--> if 'a ^<= 'b then  if 'b ^<= 'a then 'equal_case else 'less_case else  'greater_case

interactive_rw compare_less:
   less{'ord;'x;'y} -->
   compare{'ord; 'x;'y; 'less_case; 'equal_case; 'greater_case} <--> 'less_case

interactive_rw compare_equal:
   eq{'ord; 'x; 'y} -->
   compare{'ord; 'x;'y; 'less_case; 'equal_case; 'greater_case} <--> 'equal_case

interactive_rw compare_greater:
   less{'ord;'y;'x} -->
   compare{'ord; 'x;'y; 'less_case; 'equal_case; 'greater_case} <--> 'greater_case

interactive three_cases  ('x = 'y in 'ord^car) preorder[i:l]:
   [wf] sequent { <H> >- 'ord in preorder[i:l] }  -->
   [wf] sequent { <H> >- 'x in 'ord^car }  -->
   [wf] sequent { <H> >- 'y in 'ord^car }  -->
   [less] sequent { <H>; u:  less{'ord;'x;'y} >- 'T }  -->
   [equal] sequent { <H>; u:  eq{'ord; 'x; 'y} >- 'T }  -->
   [greater] sequent { <H>; u:  less{'ord;'y;'x} >- 'T }  -->
   sequent { <H> >- 'T}

doc docoff

let decideOrder3T compare_term order_term =
      three_cases compare_term order_term thenLT
         [idT; idT; idT;
          rwhAll (compare_less thenTC nthHypT (-1));
          rwhAll (compare_equal thenTC nthHypT (-1));
          rwhAll (compare_greater thenTC nthHypT (-1))]


doc <:doc< @doc{ } >>


interactive compare_wf {| intro [intro_typeinf <<'ord>>] |} preorder[i:l] :
   [wf] sequent { <H> >- 'ord in preorder[i:l] }  -->
   [wf] sequent { <H> >- 'x in 'ord^car }  -->
   [wf] sequent { <H> >- 'y in 'ord^car }  -->
   sequent { <H>; u:  less{'ord;'x;'y} >- 'less_case in 'T }  -->
   sequent { <H>; u:  less{'ord;'y;'x} >- 'greater_case in 'T } -->
   sequent { <H>; u: eq{'ord;'x;'y} >- 'equal_case in 'T } -->
   sequent { <H> >-  compare{'ord; 'x;'y; 'less_case; 'equal_case; 'greater_case} in 'T}

dform compare_df : except_mode[src] :: compare{'O; 'a;'b; 'less_case; 'equal_case; 'greater_case} =
   szone pushm[0] pushm[3] `"Compare in " slot{'O} `": " hspace
       'a `"<" 'b `" -> " slot{'less_case} hspace
       'a `"=" 'b `" -> " slot{'equal_case}  hspace
       'a `">" 'b `" -> " slot{'greater_case} popm popm ezone


interactive trans_less_less preorder[i:l] :
   [wf] sequent { <H> >- 'ord in preorder[i:l] }  -->
   [wf] sequent { <H> >- 'x in 'ord^car }  -->
   [wf] sequent { <H> >- 'y in 'ord^car }  -->
   [wf] sequent { <H> >- 'z in 'ord^car }  -->
   sequent { <H>; less{'ord;'x;'z}   >- 'C } -->
   sequent { <H>; less{'ord;'x;'y}; less{'ord;'y;'z}  >- 'C}

interactive trans_less_eq preorder[i:l] :
   [wf] sequent { <H>  >- 'ord in preorder[i:l] }  -->
   [wf] sequent { <H> >- 'x in 'ord^car }  -->
   [wf] sequent { <H> >- 'y in 'ord^car }  -->
   [wf] sequent { <H> >- 'z in 'ord^car }  -->
   sequent { <H>; less{'ord;'x;'z}   >- 'C } -->
   sequent { <H>; less{'ord;'x;'y}; eq{'ord;'y;'z} >- 'C}

interactive trans_eq_less preorder[i:l] :
   [wf] sequent { <H> >- 'ord in preorder[i:l] }  -->
   [wf] sequent { <H> >- 'x in 'ord^car }  -->
   [wf] sequent { <H> >- 'y in 'ord^car }  -->
   [wf] sequent { <H> >- 'z in 'ord^car }  -->
   sequent { <H>; less{'ord;'x;'z}   >- 'C } -->
   sequent { <H>; eq{'ord;'x;'y}; less{'ord;'y;'z} >- 'C}

interactive trans_less_less0 preorder[i:l] :
   [wf] sequent { <H> >- 'ord in preorder[i:l] }  -->
   [wf] sequent { <H> >- 'x in 'ord^car }  -->
   [wf] sequent { <H> >- 'y in 'ord^car }  -->
   [wf] sequent { <H> >- 'z in 'ord^car }  -->
   sequent { <H> >- less{'ord;'y;'z}  } -->
   sequent { <H>; less{'ord;'x;'y} >- less{'ord;'x;'z} }

interactive trans_less_less1 preorder[i:l] :
   [wf] sequent { <H> >- 'ord in preorder[i:l] }  -->
   [wf] sequent { <H> >- 'x in 'ord^car }  -->
   [wf] sequent { <H> >- 'y in 'ord^car }  -->
   [wf] sequent { <H> >- 'z in 'ord^car }  -->
   sequent { <H> >- less{'ord;'x;'y}  } -->
   sequent { <H>; less{'ord;'y;'z} >- less{'ord;'x;'z} }

interactive sym_eq_eq preorder[i:l] :
   [wf] sequent { <H> >- 'ord in preorder[i:l] }  -->
   [wf] sequent { <H> >- 'x in 'ord^car }  -->
   [wf] sequent { <H> >- 'y in 'ord^car }  -->
   sequent { <H>; eq{'ord;'x;'y} >- eq{'ord;'y;'x} }


(* BUG: shoild be implemented using resource(s) *)
let some_transT level = firstT [trans_less_less level; trans_less_eq level; trans_eq_less level]

let some_transT0 level = firstT [trans_less_less0 level; trans_less_less1 level; sym_eq_eq level]

declare order[i:l]


let hypTransT n m =
   funT (fun p ->
            let term1 = Sequent.nth_hyp p n in
            let ord = match explode_term term1 with
                  <<less{'ord;'x;'y}>> | <<eq{'ord;'x;'y}>> -> ord |
                  _ -> raise (RefineError ("hypTransT", StringTermError("transitivity does not know about ",term1))) in
            let level = infer_type p ord in
               if n=0 || m=0 then
                  let k = n+m in copyHypT k (-1) thenT some_transT0 level
               else
                  copyHypT n (-1) thenT copyHypT m (-1) thenT some_transT level
        )


interactive irref_less_eq {| elim[elim_typeinf <<'ord>> ] |} preorder[i:l] 'H :
   [wf] sequent { <H> >- 'ord in preorder[i:l] }  -->
   sequent { <H>; less{'ord;'x;'x}; <J> >- 'C }

(*
doc <:doc< @begin[doc]
  Corollary: The equality is decidable in ordered sets
  @end[doc]
>>

interactive dec_equalaty  order[i:l] :
   sequent { <H> >- 'ord in order[i:l] }  -->
   sequent { <H> >- 'x in 'ord^car }  -->
   sequent { <H> >- 'y in 'ord^car }  -->
   sequent { <H> >-  decidable{'x='y in 'ord^car} }
*)


doc <:doc< @begin[doc]
@modsection{Product}
  @end[doc]
>>

define type_porduct_ord: type_product_ord{'T;'Ord} <-->
   {car='T * 'Ord^car;
    "<=" = lambda {a.lambda {b. snd{'a} <=['Ord] snd{'b}}}
   }

let resource reduce +=
   <<field[f:t]{ type_product_ord{'T;'Ord} }>>, (addrC [Subterm 1] type_porduct_ord thenC reduceTopC)

interactive_rw compare_type_porduct_ord_reduce {| reduce |}:
   compare{type_product_ord{'T;'Ord} ; ('a,'x);('b,'y); 'less_case; 'equal_case; 'greater_case} <-->
   compare{'Ord ; 'x;'y; 'less_case; 'equal_case; 'greater_case}

interactive type_porduct_ord_preorder {| intro[] |}:
   sequent { <H> >- 'T in univ[i:l] } -->
   sequent { <H> >- 'Ord in preorder[i:l] } -->
   sequent { <H> >-  type_product_ord{'T;'Ord} in preorder[i:l] }


dform  type_porduct_ord_df: type_product_ord{'T;'Ord} = ('T * 'Ord)

doc <:doc< @begin[doc]
@modsection{Example: integers}
  @end[doc]
>>

define int_order: int_order <--> {car= int; "<"= lambda{a.lambda{b.lt_bool{'a;'b}}};"<="= lambda{a.lambda{b.le_bool{'a;'b}}}}



let resource reduce +=
   <<compare{int_order ; number[n:n];number[m:n]; 'less_case; 'equal_case; 'greater_case}>>, (addrC [Subterm 1] int_order thenC compare)


doc docoff


let preorder_opname = opname_of_term <<preorder[i:l]>>
let dest_preorder = dest_univ_term preorder_opname
let mk_preorder_term = mk_univ_term preorder_opname
let type_product_ord_opname = opname_of_term <<type_product_ord{'T;'Ord}>>
let dest_type_product_ord = dest_dep0_dep0_term type_product_ord_opname

(*
let infer_preorder inf consts decls eqs opt_eqs defs t =
   let a, b = dest_type_product_ord t in
   let eqs', opt_eqs', defs', a' = inf consts decls eqs opt_eqs defs a in
   let eqs'', opt_eqs'', defs'', b' = inf consts decls eqs' opt_eqs' defs' b in
   let le1 = Itt_equal.dest_univ a' in
   let le2 = dest_preorder b' in
      eqs'', opt_eqs'', defs'', mk_preorder_term (max_level_exp le1 le2 0)
*)

let infer_preorder inf consts decls eqs opt_eqs defs t =
   let a, b = dest_type_product_ord t in
      inf consts decls eqs opt_eqs defs b


let resource typeinf +=  <<type_product_ord{'T;'Ord}>>,  infer_preorder
