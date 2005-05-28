doc <:doc< @doc{@parents} >>
extends Itt_hoas_destterm
extends Itt_image
extends Itt_tunion

doc docoff

open Basic_tactics
open Itt_struct

define unfold_compatible_shapes: compatible_shapes{'bdepth; 'op; 'btl} <-->
      length{shape{'op}} = length{'btl} in int &
      all i:Index{'btl}. bdepth{nth{'btl;'i}} =  'bdepth +@ nth{shape{'op};'i} in int

dform compatible_shapes_df: compatible_shapes{'bdepth;'op;'btl} = `"compatible_shapes(" slot{'bdepth} `";" slot{'op} `";" slot{'btl} `")"



define (*private*) unfold_dom: dom{'BT} <--> nat*nat + depth:nat * op:Operator * {subterms:list{'BT} | compatible_shapes{'depth;'op;'subterms} }


define (*private*) unfold_mk: mk{'x} <--> decide{'x;
                                                  v.spread{'v;left,right. var{'left;'right}};
                                                  t.spread{'t;d,op,st. mk_bterm{'d;'op;'st}}}

define (*private*) unfold_dest: dest{'bt} <--> if is_var{'bt}
                                               then inl {(left{'bt},right{'bt})}
                                               else (bdepth{'bt},(get_op{'bt},subterms{'bt}))


define (*private*) unfold_Iter: Iter{'X} <--> Img{dom{'X};x.mk{'x}}

define (*private*) unfold_BT: BT{'n} <--> ind{'n; void; X.Iter{'X}}

interactive_rw bt_reduce_base {| reduce |}: BT{0} <--> void

interactive_rw bt_reduce_step {| reduce |}: 'n in nat --> BT{'n+@1} <--> Iter{BT{'n}}


(*private *) define unfold_BTerm: BTerm <--> Union n:nat. BT{'n}


interactive  bt_elim_squash  {| elim [] |} 'H :
   [wf] sequent { <H>; <J> >- 'n in nat } -->
   [base] sequent { <H>; <J>; l: nat; r:nat >- squash{'P[var{'l;'r}]} } -->
   [step] sequent { <H>; <J>; depth: nat; op:Operator; subterms:list{BT{'n}};
               compatible_shapes{'depth;'op;'subterms} >- squash{'P[mk_bterm{'depth;'op;'subterms}]} } -->
   sequent { <H>; t: BT{'n+@1}; <J> >- squash{'P['t]} }

interactive  bt_wf_and_bdepth_wf  {| intro[] |}:
   sequent{ <H> >- 'n in nat } -->
   sequent{ <H> >- BT{'n} Type & all t: BT{'n}. bdepth{'t} in nat }

interactive  bt_wf {| intro[] |}:
   sequent{ <H> >- 'n in nat } -->
   sequent{ <H> >- BT{'n} Type }

interactive  bterm_wf {| intro[] |}:
   sequent{ <H> >- BTerm Type }

interactive  bdepth_wf  {| intro[] |}:
   sequent{ <H> >- 't in BTerm } -->
   sequent{ <H> >- bdepth{'t} in nat }

interactive compatible_shapes_wf {| intro[] |}:
   sequent{ <H> >- 'bdepth in nat } -->
   sequent{ <H> >- 'op in Operator } -->
   sequent{ <H> >- 'btl in list{BTerm} } -->
   sequent{ <H> >- compatible_shapes{'bdepth; 'op; 'btl} Type }

interactive  bt_subtype_bterm  {| intro[] |} :
   sequent{ <H> >- 'n in nat} -->
   sequent{ <H> >- BT{'n} subtype BTerm }

interactive  bt_monotone  {| intro[] |} :
   sequent{ <H> >- 'n in nat} -->
   sequent{ <H> >- BT{'n} subtype BT{'n+@1} }


interactive var_wf {| intro[] |}:
   sequent{ <H> >- 'l in nat } -->
   sequent{ <H> >- 'r in nat } -->
   sequent{ <H> >- var{'l;'r} in BTerm }

interactive mk_bterm_bt_wf {| intro[] |}:
   sequent{ <H> >- 'n in nat } -->
   sequent{ <H> >- 'depth in nat } -->
   sequent{ <H> >- 'op in Operator } -->
   sequent{ <H> >- 'subterms in list{BT{'n}} } -->
   sequent{ <H> >- compatible_shapes{'depth;'op;'subterms} } -->
   sequent{ <H> >- mk_bterm{'depth;'op;'subterms} in BT{'n+@1} }

interactive mk_bterm_wf {| intro[] |}:
   sequent{ <H> >- 'depth in nat } -->
   sequent{ <H> >- 'op in Operator } -->
   sequent{ <H> >- 'subterms in list{BTerm} } -->
   sequent{ <H> >- compatible_shapes{'depth;'op;'subterms} } -->
   sequent{ <H> >- mk_bterm{'depth;'op;'subterms} in BTerm }

interactive  bterm_elim_squash {| elim [] |} 'H :
   sequent { <H>; <J>; l: nat; r:nat >- squash{'P[var{'l;'r}]} } -->
   sequent { <H>; <J>; depth: nat; op:Operator; subterms:list{BTerm};
               compatible_shapes{'depth;'op;'subterms} >- squash{'P[mk_bterm{'depth;'op;'subterms}]} } -->
   sequent { <H>; t: BTerm; <J> >- squash{'P['t]} }

interactive  bt_elim  {| elim [] |} 'H :
   sequent { <H>; <J>; l: nat; r:nat >- 'P[var{'l;'r}] } -->
   sequent { <H>; <J>; depth: nat; op:Operator; subterms:list{BT{'n}};
               compatible_shapes{'depth;'op;'subterms} >- 'P[mk_bterm{'depth;'op;'subterms}] } -->
   sequent { <H>; t: BT{'n+@1}; <J> >- 'P['t] }

interactive bterm_elim  {| elim [] |} 'H :
   sequent { <H>; <J>; l: nat; r:nat >- 'P[var{'l;'r}] } -->
   sequent { <H>; <J>; depth: nat; op:Operator; subterms:list{BTerm};
               compatible_shapes{'depth;'op;'subterms} >- 'P[mk_bterm{'depth;'op;'subterms}] } -->
   sequent { <H>; t: BTerm; <J> >- 'P['t] }

(*
define (*private*) unfold_dom: dom{'BT} <--> nat*nat + op:Operator * depth:nat * all_list{shape{'op};x.'BT ('depth-'x)}



define (*private*) unfold_f: f{'x} <--> decide{x.
                                                  v.spread{'v;left,right. var{left;'right}};
                                                  t.speaad{'t;op,n,p. mk_bterm{'n;list_from_prod{length{'op};'p}}}}



define unfold_BTerm: BTerm{'n} <--> prec{BT;n . Image{dom{'BT};x.f{'x}}; 'n }

*)
