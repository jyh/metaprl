extends Itt_synt_lang
extends Itt_reflection_new
extends Itt_reflection_example_lambda
extends Itt_reflection_lambda_reduction

open Basic_tactics

declare fun_term
iform fun_term: fun_term <--> bterm{| >- "fun"[@]{term[@];term[@]} |}
dform fun_df: fun_term = `"\"fun\""

define unfold_mk_fun: mk_fun{'t;'s} <--> let depth=max{bdepth{'t};bdepth{'s}} in  make_bterm{fun_term; 'depth; make_depth{'t;'depth}::make_depth{'s;'depth}::nil}

declare iform TypeTerm
iform typeTerm: TypeTerm <--> Lang{fun_term::nil}
dform type_df: TypeTerm = `"Term" sub{rightarrow}

interactive type_term_induction  {| elim[] |} 'H:
   sequent { <H>; <J>; v:Var >- 'P[ 'v ] } -->
   sequent { <H>; <J>; t: TypeTerm; s:TypeTerm; bdepth{'t} = bdepth{'s} in nat;
                            'P['t]; 'P['s]   >- 'P[ mk_fun{'t;'s} ] } -->
   sequent { <H>; x: TypeTerm; <J> >- 'P['x] }

interactive mk_fun_wf  {| intro[] |} :
   sequent { <H> >- 't in TypeTerm } -->
   sequent { <H> >- 's in TypeTerm } -->
   sequent { <H> >- mk_fun{'t;'s} in TypeTerm }


(* define unfold_is_type: is_type{'t;'Tv; 'T} <-->
*) declare is_type{'t;'Tv; 'T}

interactive_rw is_type_rw {| reduce |}: is_type{'t;'Tv; 'T} <-->
   dest_lambda_term{'t;
              v. 'T = nth{'Tv; right{'v}} in TypeTerm;
              f. exst A:TypeTerm. exst B:TypeTerm. (is_type{'f;'A::'Tv;'B} & 'T=mk_fun{'A;'B} in TypeTerm);
              f,a. exst A:TypeTerm. (is_type{'f;'Tv;mk_fun{'A;'T}} &  is_type{'a;'Tv;'A})}



interactive is_type_wf {| intro[] |}:
   sequent { <H> >- 't in LambdaTerm } -->
   sequent { <H> >- 'Tv in list{TypeTerm} } -->
   sequent { <H> >- 'T in TypeTerm } -->
   sequent { <H> >-  is_type{'t;'Tv;'T} Type }


interactive subject_reduction {| intro[] |} 't:
   sequent { <H> >- 't in LambdaTerm } -->
   sequent { <H> >- 'Tv in list{TypeTerm} } -->
   sequent { <H> >- 'T in TypeTerm } -->
   sequent { <H> >-  is_type{'t;'Tv;'T} } -->
   sequent { <H> >-  reduce1{'t;'s} } -->
   sequent { <H> >-  is_type{'s;'Tv;'T} }



interactive example:
sequent{ <H> >- is_type{bterm{| a:term >- apply[@]{lambda[@]{x.'x};'a} |}; bterm{|A:term >- 'A |}::nil; bterm{|A:term >- 'A |} } }



