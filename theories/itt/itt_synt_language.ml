extends Itt_synt_bterm
extends Itt_functions
extends Itt_nat
extends Itt_nequal
extends Itt_bisect
extends Itt_list
extends Itt_srec
extends Itt_pairwise
extends Itt_pairwise2

open Basic_tactics


define unfold_dom: dom{'ops;'T} <--> Var + (i:Index{'ops} * depth : nat * { bts: list{BTerm isect 'T} | compatible_shapes{inject{nth{'ops;'i};'depth};'bts} })


define unfold_mk: mk{'ops} <--> lambda{d. decide{'d; v. 'v; p.spread{'p; i,bts. make_bterm{nth{'ops;'i}; 'bts } }}}

define unfould_language: Language{'ops} <-->  srec{X. Img{mk{'ops}; dom{'ops;'X}; BTerm}}


interactive dom_wf  {| intro[] |}:
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- 'T Type } -->
   sequent { <H> >- dom{'ops;'T} Type }

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
           inr{(find{'ops; 'op; x,y.is_same_op{'x;'y}}
               ,'subterms
               )} }}


interactive mk_reverse {| intro[] |} :
   sequent { <H> >- 'ops in diff_list{Operator} } -->
   sequent { <H> >- 'T subtype BTerm } -->
   sequent { <H> >- dest{'ops} in RReverse{mk{'ops}; dom{'ops;'T}; BTerm} }


interactive language_induction  {| elim[] |} 'H:
   [wf] sequent { <H> >- 'ops in diff_list{Operator} } -->
   [base] sequent { <H>; <J>; v:Var >- 'P[ 'v ] } -->
   [step] sequent { <H>; <J>; i:Index{'ops}; bts: list{Language{'ops}};
                       depth:nat; compatible_shapes{inject{nth{'ops;'i};'depth};'bts};
                       all_list{'bts;t.'P['t]} >- 'P[ make_bterm{nth{'ops;'i}; 'depth; 'bts} ] } -->
   sequent { <H>; x: Language{'ops}; <J> >- 'P['x] }

interactive language_intro  {| intro[] |} :
   sequent { <H> >- mem{'op;'ops;Operator}  } -->
   sequent { <H> >- all_list{'bts;t.'t in Language{'ops}} } -->
   sequent { <H> >- compatible_shapes{inject{'op;'depth};'bts}  } -->
   sequent { <H> >- make_bterm{'op; 'depth; 'bts} in Language{'ops} }

interactive language_intro_var  {| intro[AutoMustComplete] |} :
   sequent { <H> >- 'v in Var } -->
   sequent { <H> >- 'v in Language{'ops} }
