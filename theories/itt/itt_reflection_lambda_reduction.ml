(* This theory define beta-reduction for the simple lambda-calculus *)
extends Itt_reflection_new
extends Itt_synt_subst
extends Itt_reflection_example_lambda

open Basic_tactics

define unfold_subst2: subst{'f;'b} <--> subst{'f;last_var{'f};'b}

interactive subst_wf {| intro [] |} :
   sequent { <H> >- 'f in BTerm_plus{1} } -->
   sequent { <H> >- 'b in BTerm } -->
   sequent { <H> >- bdepth{'f} >= bdepth{'b} } -->
   sequent { <H> >- subst{'f;'b} in BTerm }

interactive subst_LambdaTerm {| intro [] |} :
   sequent { <H> >- 'f in LambdaTerm } -->
   sequent { <H> >- 'b in LambdaTerm } -->
   sequent { <H> >- bdepth{'f} >= bdepth{'b} } -->
   sequent { <H> >- bdepth{'f} >= 1 } -->
   sequent { <H> >- subst{'f;'b} in LambdaTerm }


define unfold_beta_redex: beta_redex{'redex;'contractum} <-->
   exst f:LambdaTerm. exst b:LambdaTerm.
    ( bdepth{'f} >= bdepth{'b} & bdepth{'f} >= 1 &
      ('redex = mk_apply{ mk_lambda{'f}; 'b} in LambdaTerm &
       'contractum = subst{'f;'b} in LambdaTerm))

interactive beta_redex_wf {| intro[] |}:
   sequent{ <H> >- 't in LambdaTerm } -->
   sequent{ <H> >- 's in LambdaTerm } -->
   sequent{ <H> >- beta_redex{'t;'s} Type }

interactive beta_redex_bterm:
   sequent{ <H> >- bterm{| <K>; x:term >- 'f['x] |} in LambdaTerm } -->
   sequent{ <H> >- bterm{| <K> >- 'b |} in LambdaTerm } -->
   sequent { <H> >- if_quoted_op{ bterm{| <K>; x:term >- 'f['x] |}; "true" } } -->
   sequent { <H> >- if_quoted_op{ bterm{| <K> >- 'b |}; "true" } } -->
   sequent{ <H> >- beta_redex{bterm{| <K> >- apply[@]{lambda[@]{x.'f['x]}; 'b} |}; bterm{| <K> >- 'f['b] |} } }

define unfold_reduce1: reduce1{'t;'s} <-->
   exst f:LambdaTerm. exst redex:LambdaTerm. exst contractum:LambdaTerm.
    ( bdepth{'f} >= bdepth{'redex} & bdepth{'f} >= bdepth{'contractum} & bdepth{'f} >= 1 =>
      ('t = subst{'f;'redex} in LambdaTerm &
       's = subst{'f;'contractum} in LambdaTerm &
       beta_redex{'redex;'contractum}))

interactive beta_reduce1_wf {| intro[] |}:
   sequent{ <H> >- 't in LambdaTerm } -->
   sequent{ <H> >- 's in LambdaTerm } -->
   sequent{ <H> >- reduce1{'t;'s} Type }


