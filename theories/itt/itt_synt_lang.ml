doc <:doc<
   @begin[doc]
   @module[Itt_synt_lang]

   The @tt[Itt_synt_lang]  module defines a type of syntactic terms that are built with a fixed list of operators.

   If $ops$ is a list of operators, then <<Lang{'ops}>> is a subtype of type <<BTerm>> that contains all terms built with operators from the list $ops$.
   @end[doc]
>>

doc <:doc< @doc{@parents} >>

extends Itt_synt_bterm
extends Itt_functions
extends Itt_nat
extends Itt_nequal
extends Itt_bisect
extends Itt_list
extends Itt_srec
extends Itt_pairwise
extends Itt_pairwise2
doc docoff

open Basic_tactics


doc <:doc<
   @begin[doc]
     We define the type <<Lang{'ops}>> as the recursive type.

   @end[doc]
>>


define unfold_dom: dom{'ops;'T} <--> Var + (i:Index{'ops} * depth : nat * { bts: list{BTerm isect 'T} | compatible_shapes{inject{nth{'ops;'i};'depth};'bts} })


define unfold_mk: mk{'ops} <--> lambda{d. decide{'d; v. 'v; p.spread{'p; i,q. spread{'q; depth,bts. make_bterm{nth{'ops;'i}; 'depth; 'bts }} }}}

define unfold_lang: Lang{'ops} <-->  srec{X. Img{mk{'ops}; dom{'ops;'X}; BTerm}}
doc docoff

let fold_lang = makeFoldC << Lang{'ops} >> unfold_lang

doc <:doc<
   @begin[doc]
   @end[doc]
>>
interactive dom_wf  {| intro[] |}:
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- 'T Type } -->
   sequent { <H> >- dom{'ops;'T} Type }

interactive dom_intro  {| intro[] |}:
   sequent { <H> >- 'x in Var + (i:Index{'ops} * depth : nat * { bts: list{BTerm isect 'T} | compatible_shapes{inject{nth{'ops;'i};'depth};'bts} }) } -->
   sequent { <H> >- 'x in dom{'ops;'T} }

interactive dom_elim  {| elim[] |} 'H :
   sequent { <H>; x: Var + (i:Index{'ops} * depth : nat * { bts: list{BTerm isect 'T} | compatible_shapes{inject{nth{'ops;'i};'depth};'bts} }); <J['x]> >- 'C['x] } -->
   sequent { <H>; x: dom{'ops;'T}; <J['x]> >- 'C['x] }

interactive mk_wf  {| intro[] |}:
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- 'T Type } -->
   sequent { <H> >- mk{'ops} in dom{'ops;'T} -> BTerm }

interactive dom_monotone  {| intro[] |}:
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- 'S subtype 'T } -->
   sequent { <H> >- dom{'ops;'S} subtype dom{'ops;'T} }

define dest: dest{'ops} <-->
   lambda{t.
      dest_bterm{'t;
        var. inl{'var};
        op,subterms.
           inr{(find{'ops; 'op; x,y.Itt_synt_operator!is_same_op{'x;'y}}, (op_bdepth{'op} ,'subterms))
              } }}

(*interactive dest_wf  {| intro[] |}:
   sequent { <H> >- 'ops in diff_list{Operator} } -->
   sequent { <H> >- 'T Type } -->
   sequent { <H> >- dest{'ops} in BTerm -> dom{'ops;'T} }
*)
interactive find_diff_ops {| intro[] |} :
   sequent { <H> >- 'ops in diff_list{Operator} } -->
   sequent { <H> >- 'i in Index{'ops} } -->
   sequent { <H> >- 'depth in nat } -->
   sequent { <H> >- find{'ops; inject{nth{'ops; 'i}; 'depth}; x,y.Itt_synt_operator!is_same_op{'x;'y}} = 'i in Index{'ops} }

interactive mk_dest_inverse {| intro[] |} :
   sequent { <H> >- 'ops in diff_list{Operator} } -->
   sequent { <H> >- 'T subtype BTerm } -->
   sequent { <H> >- inverse{dest{'ops}; mk{'ops}; dom{'ops;'T}} }

interactive mk_reverse {| intro[] |} :
   sequent { <H> >- 'ops in diff_list{Operator} } -->
   sequent { <H> >- 'T subtype BTerm } -->
   sequent { <H> >- dest{'ops} in RReverse{mk{'ops}; dom{'ops;'T}; BTerm} }

interactive mk_reverse2 {| intro[] |} :
   sequent { <H> >- 'ops in diff_list{Operator} } -->
   sequent { <H> >- 'T subtype BTerm } -->
   sequent { <H> >- RReverse{mk{'ops}; dom{'ops;'T}; BTerm} }

interactive lang_wf  {| intro[] |} :
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- Lang{'ops} Type }

interactive lang_subtype  {| intro[] |} :
   sequent { <H> >- 'ops in diff_list{Operator} } -->
   sequent { <H> >- Lang{'ops} subtype BTerm }

interactive lang_induction  {| elim[] |} 'H:
   [wf] sequent { <H> >- 'ops in diff_list{Operator} } -->
   [base] sequent { <H>; <J>; v:Var >- 'P[ 'v ] } -->
   [step] sequent { <H>; <J>; i:Index{'ops}; bts: list{Lang{'ops}};
                       depth:nat; compatible_shapes{inject{nth{'ops;'i};'depth};'bts};
                       all_list{'bts;t.'P['t]} >- 'P[ make_bterm{nth{'ops;'i}; 'depth; 'bts} ] } -->
   sequent { <H>; x: Lang{'ops}; <J> >- 'P['x] }

interactive lang_intro  {| intro[] |} :
   sequent { <H> >- 'op in Operator } -->
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- 'depth in nat } -->
   sequent { <H> >- 'bts in list{BTerm isect Lang{'ops}} } -->
   sequent { <H> >- mem{'op;'ops;Operator}  } -->
   sequent { <H> >- all_list{'bts;t.'t in Lang{'ops}} } -->
   sequent { <H> >- compatible_shapes{inject{'op;'depth};'bts}  } -->
   sequent { <H> >- make_bterm{'op; 'depth; 'bts} in Lang{'ops} }

interactive lang_intro_var  {| intro[AutoMustComplete] |} :
   sequent { <H> >- 'v in Var } -->
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- 'v in Lang{'ops} }
