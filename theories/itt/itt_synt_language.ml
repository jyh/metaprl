extends Itt_synt_bterm
extends Itt_functions
extends Itt_nat
extends Itt_bisect
extends Itt_list
extends Itt_srec
extends Itt_pairwise
extends Itt_pairwise2

open Basic_tactics


define unfold_dom: dom{'ops;'T} <--> Var + (i:Index{'ops} * { bts: list{BTerm isect 'T} | compatible_shapes{nth{'ops;'i};'bts} })


define unfold_mk: mk{'ops} <--> lambda{d. decide{'d; v. 'v; p.spread{'p; i,bts. make_bterm{nth{'ops;'i}; 'bts } }}}

define unfould_language: language{'ops} <-->  srec{X. Img{mk{'ops}; dom{'ops;'X}; BTerm}}


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
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- 'T subtype BTerm } -->
   sequent { <H> >- dest{'ops} in RReverse{mk{'ops}; dom{'ops;'T}; BTerm} }


