doc <:doc<
   @begin[doc]
   @module[Itt_synt_subst]

   The @tt[Itt_synt_subst] module defines substitution on bterms.
   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.

   Copyright (C) 2005 MetaPRL Group

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

   Authors: Alexei Kopylov @email{kopylov@cs.caltech.edu}
            Aleksey Nogin @email{nogin@cs.caltech.edu}
            Xin Yu @email{xiny@cs.caltech.edu}
   @end[license]
>>

doc <:doc< @doc{@parents} >>
extends Itt_theory
extends Itt_nat
extends Itt_fun2
extends Itt_nequal
extends Itt_synt_var
extends Itt_synt_operator
extends Itt_synt_bterm
doc docoff

open Basic_tactics

doc <:doc<
   @begin[doc]
   @modsection{Auxiliary Operations for Defining Substitution}
   @modsubsection{Make a new variable}

   << new_var{'bt} >> creates a new variable:
   $$ new@_var(<<Gamma>>.t) = <<Gamma>>,x.x$$
   @end[doc]
>>
define unfold_new_var: new_var{'bt} <--> var{bdepth{'bt};0}

interactive_rw new_var_reduce1 {| reduce |} :
      new_var{make_bterm{'op;'subterms}} <--> var{op_bdepth{'op};0}

interactive_rw new_var_reduce2 {| reduce |} :
      'l in nat -->
      'r in nat -->
       new_var{var{'l;'r}} <--> var{'l +@ 'r +@ 1; 0}

interactive_rw new_var_var_reduce :
      ('u in Var) -->
      new_var{'u} <--> var{left{'u}+@right{'u}+@1; 0}

interactive_rw new_var_bdepth {| reduce |} :
   ('bt in BTerm)  -->
   depth{new_var{'bt}} <--> bdepth{'bt} +@ 1

interactive new_var_wf {| intro [] |} :
   sequent { <H> >- 'bt in BTerm } -->
   sequent { <H> >- new_var{'bt} in Var }

doc <:doc<
   @begin[doc]
   @modsubsection{Last variable}

   << last_var{'bt} >> is the last variable of the term $bt$:
   $$ new@_var(<<Gamma>>,x.t) = <<Gamma>>,x.x$$
   @end[doc]
>>
define unfold_last_var: last_var{'bt} <--> var{bdepth{'bt}-@1;0}

interactive_rw last_var_reduce1 {| reduce |} :
      last_var{make_bterm{'op;'subterms}} <--> var{op_bdepth{'op}-@1;0}

interactive_rw last_var_reduce2 {| reduce |} :
      'l in nat -->
      'r in nat -->
       last_var{var{'l;'r}} <--> var{'l +@ 'r ; 0}

interactive_rw last_var_var_reduce :
      ('u in Var) -->
      last_var{'u} <--> var{left{'u}+@right{'u}; 0}

interactive_rw last_var_bdepth {| reduce |} :
   ('bt in BTerm)  -->
   depth{last_var{'bt}} <--> bdepth{'bt}

interactive last_var_wf {| intro [] |} :
   sequent { <H> >- 'bt in BTerm } -->
   sequent { <H> >- last_var{'bt} in Var }

interactive last_var_wf2 {| intro [] |} :
   sequent { <H> >- 'bt in BTerm } -->
   sequent { <H> >- last_var{'bt}  in Vars_of{'bt} }


doc <:doc<
   @begin[doc]
   @modsubsection{Add a binding variable}

   $$ add@_var(<<Gamma>>, <<Delta>>.s; <<Gamma>>,x,<<Delta>>_1.x) = <<Gamma>>,x,<<Delta>>.s$$
   @end[doc]
>>
define unfold_add_var:
   add_var{'bt;'v} <-->
      fix{add.lambda{bt.
         dest_bterm{'bt;
                    u. if left{'v} <=@ left{'u}
                        then var{left{'u}+@1;right{'u}}
                        else var{left{'u};right{'u}+@1};
                    op,subterms. make_bterm{bind{'op}; map{x.'add 'x; 'subterms}} }
         }} 'bt
doc docoff

let fold_add_var = makeFoldC << add_var{'bt;'v} >> unfold_add_var

doc <:doc< @begin[doc]
@end[doc] >>
interactive_rw add_var_reduce1 {| reduce |} :
      add_var{make_bterm{'op;'subterms}; 'v} <--> make_bterm{bind{'op}; map{x.add_var{'x;'v}; 'subterms}}

interactive_rw add_var_reduce2 {| reduce |} :
      'l in nat -->
      'r in nat -->
      add_var{var{'l;'r}; 'v} <--> if left{'v} <=@ 'l
                                      then var{'l+@1;'r}
                                      else var{'l;'r+@1}

interactive_rw add_var_var_reduce :
      ('u in Var) -->
      add_var{'u; 'v} <--> if left{'v} <=@ left{'u}
                                  then var{left{'u}+@1;right{'u}}
                                  else var{left{'u};right{'u}+@1}

interactive_rw add_var_bdepth {| reduce |} :
   ('bt in BTerm)  -->
   ('v in Var)  -->
   bdepth{add_var{'bt;'v}} <--> bdepth{'bt} +@ 1

interactive add_var_wf {| intro [] |} :
   sequent { <H> >- 'bt in BTerm } -->
   sequent { <H> >- 'v in Var } -->
   sequent { <H> >- add_var{'bt;'v} in BTerm }

interactive add_var_wf2 {| intro [] |} :
   sequent { <H> >- 'bt in Var } -->
   sequent { <H> >- 'v in Var } -->
   sequent { <H> >- add_var{'bt;'v} in Var }

doc <:doc<
   @begin[doc]

   Another version of @tt[add_var]:
   $$ add@_var(<<Gamma>>.s) = <<Gamma>>,x.s$$
   @end[doc]
>>
define unfold_add_new_var:
   add_var{'bt} <--> add_var{'bt; new_var{'bt}}

interactive_rw add_new_var_reduce1 {| reduce |} :
   add_var{make_bterm{'op;'subterms}} <--> make_bterm{bind{'op}; map{x.add_var{'x; var{op_bdepth{'op}; 0}}; 'subterms}}

interactive_rw add_new_var_reduce2 {| reduce |} :
      ('l in nat) -->
      ('r in nat) -->
      add_var{var{'l;'r}} <--> var{'l;'r+@1}

interactive_rw add_new_var_var_reduce :
      ('u in Var) -->
      add_var{'u} <--> var{left{'u};right{'u}+@1}

interactive_rw add_new_var_bdepth {| reduce |} :
   ('bt in BTerm)  -->
   bdepth{add_var{'bt}} <--> bdepth{'bt} +@ 1

interactive add_new_var_wf {| intro [] |} :
   sequent { <H> >- 'bt in BTerm } -->
   sequent { <H> >- add_var{'bt} in BTerm }

doc <:doc<
   @begin[doc]
   @modsubsection{Add zero or more binding variables}

   <<make_depth{'s;'n}>> adds some variables to the term $s$ to make its binding depth to be equal to $n$.
   It is defined only if <<'n >= bdepth{'s}>>.
   @end[doc]
>>

define unfold_make_depth: make_depth{'s;'n} <--> ind{'n -@ bdepth{'s};'s; k,s.add_var{'s}}

interactive_rw make_depth_bdepth {| reduce |} :
   ('s in BTerm)  -->
   ('n in nat)  -->
   ('n >= bdepth{'s})  -->
   bdepth{make_depth{'s;'n}} <--> 'n

interactive make_depth_wf {| intro [] |} :
   sequent { <H> >- 's in BTerm } -->
   sequent { <H> >- 'n in nat } -->
   sequent { <H> >- 'n >= bdepth{'s} } -->
   sequent { <H> >- make_depth{'s;'n} in BTerm }



doc <:doc<
   @begin[doc]
   <<add_vars_upto{'s;'t}>> adds variables to the term $s$  to match its binding depth to the term $t$:
   $$ add@_vars@_upto(<<Gamma>>.s; <<Gamma>>,<<Delta>>.t) = <<Gamma>>,<<Delta>>.s$$
   It is undefined when <<bdepth{'t} < bdepth{'s}>>.
   @end[doc]
>>


define unfold_add_vars_upto:
   add_vars_upto{'s;'t} <--> make_depth{'s;bdepth{'t}}
doc docoff

let fold_add_vars_upto = makeFoldC << add_vars_upto{'s;'t} >> unfold_add_vars_upto
doc docon

interactive_rw add_vars_upto_bdepth {| reduce |} :
   ('t in BTerm)  -->
   ('s in BTerm)  -->
   (bdepth{'t} >= bdepth{'s})  -->
   bdepth{add_vars_upto{'s;'t}} <--> bdepth{'t}

interactive add_vars_upto_wf {| intro [] |} :
   sequent { <H> >- 't in BTerm } -->
   sequent { <H> >- 's in BTerm } -->
   sequent { <H> >- bdepth{'t} >= bdepth{'s} } -->
   sequent { <H> >- add_vars_upto{'s;'t} in BTerm }

doc <:doc<
   @begin[doc]
   @modsection{Substitution}

   << subst{'t;'v;'s} >> substitutes << 's >> for the variable << 'v >> of bterm << 't >>:
   $$ subst(<<Gamma>>,x,<<Delta>>_1,<<Delta>>_2.t[x]; <<Gamma>>,x,<<Delta>>_3.x; <<Gamma>>,x,<<Delta>>_1.s[x]) = <<Gamma>>,x,<<Delta>>_1, <<Delta>>_2.t[s[x]] $$
   @end[doc]
>>
define unfold_subst:
   subst{'t;'v;'s} <-->
      fix{subst.lambda{t.
         dest_bterm{'t;
                    u. if is_eq{'v;'u} then add_vars_upto{'s;'u} else 'u;
                    op,subterms. make_bterm{'op;map{x.'subst 'x; 'subterms}} }
         }} 't
doc docoff

let fold_subst = makeFoldC << subst{'t;'v;'s} >> unfold_subst

doc <:doc< @begin[doc]
@end[doc] >>
interactive_rw subst_reduce1 {| reduce |} :
      subst{make_bterm{'op;'subterms}; 'v; 's} <--> make_bterm{'op; map{x.subst{'x;'v;'s}; 'subterms}}

interactive_rw subst_var_reduce :
      ('u in Var) -->
      subst{'u; 'v; 's} <--> if is_eq{'v;'u} then add_vars_upto{'s;'u} else 'u

interactive_rw subst_var_eq_reduce {| reduce |} :
      ('v in Var) -->
      subst{'v; 'v; 's} <-->  add_vars_upto{'s;'v}

interactive_rw subst_reduce2 {| reduce |} :
      subst{var{'l;'r}; 'v; 's} <-->  if is_eq{'v;var{'l;'r}} then add_vars_upto{'s;var{'l;'r}} else var{'l;'r}

interactive_rw subst_bdepth {| reduce |} :
   ('t in BTerm)  -->
   ('v in Vars_of{'t})  -->
   ('s in BTerm)  -->
   (bdepth{'t} >= bdepth{'s})  -->
   bdepth{subst{'t;'v;'s}} <--> bdepth{'t}

interactive subst_wf {| intro [] |} :
   sequent { <H> >- 't in BTerm } -->
   sequent { <H> >- 'v in Vars_of{'t} } -->
   sequent { <H> >- 's in BTerm } -->
   sequent { <H> >- bdepth{'t} >= bdepth{'s} } -->
   sequent { <H> >- subst{'t;'v;'s} in BTerm }

doc <:doc< @begin[doc]
   << not_free{'v;'t} >> decides whether << 'v >> is not free in << 't >>.
@end[doc] >>
define unfold_not_free: not_free{'v;'t} <-->
      fix{not_free.lambda{t.
          dest_bterm{'t;
                    u. "assert"{bnot{is_eq{'v;'u}}};
                    op,subterms.
                       all_list{ 'subterms; t.'not_free 't} }
         }} 't
doc docoff

let fold_not_free = makeFoldC << not_free{'v;'t} >> unfold_not_free

doc <:doc< @begin[doc]
@end[doc] >>
interactive_rw not_free_reduce1 {| reduce |} :
      not_free{'v; make_bterm{'op;'subterms}} <-->
      all_list{'subterms; t.not_free{'v;'t}}

interactive_rw not_free_reduce2 {| reduce |} :
      not_free{'v; var{'l;'r}} <--> "assert"{bnot{is_eq{'v; var{'l;'r}}}}

interactive_rw not_free_var_reduce :
      ('u in Var) -->
      not_free{'v; 'u} <-->  "assert"{bnot{is_eq{'v;'u}}}

interactive not_free_wf {| intro[] |}:
   sequent { <H> >- 'v in Var } -->
   sequent { <H> >- 't in BTerm } -->
   sequent { <H> >- not_free{'v;'t} Type  }

doc "doc"{rules}

interactive subst_not_free :
   sequent { <H> >- 't in BTerm } -->
   sequent { <H> >- 'v in Vars_of{'t} } -->
   sequent { <H> >- 's in BTerm } -->
   sequent { <H> >- bdepth{'t} >= bdepth{'s} } -->
   sequent { <H> >- not_free{'v;'t} } -->
   sequent { <H> >- subst{'t;'v;'s} ~ 't }

interactive eq_add_var1 {| intro[] |}:
   sequent { <H> >- 'v in Var } -->
   sequent { <H> >- 'u in Var } -->
   sequent { <H> >- left{'v} < left{'u} } -->
   sequent { <H> >- "assert"{is_eq{'v;add_var{'v;'u}}} }

interactive eq_add_var {| intro[] |}:
   sequent { <H> >- 'v in Var } -->
   sequent { <H> >- "assert"{is_eq{'v;add_var{'v}}} }

interactive not_free_eq_var 'v  :
   sequent { <H> >- 't in BTerm } -->
   sequent { <H> >- 'v in Vars_of{'t} } -->
   sequent { <H> >- 'u in Vars_of{'t} } -->
   sequent { <H> >- "assert"{is_eq{'v;'u}} } -->
   sequent { <H> >- not_free{'v; 't} } -->
   sequent { <H> >- not_free{'u; 't} }

interactive add_var_not_free1 {| intro[] |} :
   sequent { <H> >- 't in BTerm } -->
   sequent { <H> >- 'v in Vars_of{'t} } -->
   sequent { <H> >- 'u in Var } -->
   sequent { <H> >- not_free{'v;'t} } -->
   sequent { <H> >- not_free{add_var{'v;'u}; add_var{'t; 'u}} }

interactive add_var_not_free2 {| intro[AutoMustComplete] |} :
   sequent { <H> >- 't in BTerm } -->
   sequent { <H> >- 'v in Vars_of{'t} } -->
   sequent { <H> >- 'u in Var } -->
   sequent { <H> >- not_free{'v;'t} } -->
   sequent { <H> >- left{'v} < left{'u} } -->
   sequent { <H> >- not_free{'v; add_var{'t; 'u}} }

interactive add_var_not_free3 {| intro[] |}   :
   sequent { <H> >- 't in BTerm } -->
   sequent { <H> >- 'v in Vars_of{'t} } -->
   sequent { <H> >- not_free{'v; add_var{'t;'v}} }

interactive add_var_not_free {| intro[] |} :
   sequent { <H> >- 't in BTerm } -->
   sequent { <H> >- 'v in Vars_of{'t} } -->
   sequent { <H> >- not_free{'v;'t} } -->
   sequent { <H> >- not_free{'v; add_var{'t}} }

interactive add_vars_upto_not_free {| intro[] |} :
   sequent { <H> >- 't in BTerm } -->
   sequent { <H> >- 's in BTerm } -->
   sequent { <H> >- 'v in Vars_of{'t} } -->
   sequent { <H> >- bdepth{'s} >= bdepth{'t} } -->
   sequent { <H> >- not_free{'v;'t} } -->
   sequent { <H> >- not_free{'v; add_vars_upto{'t; 's}} }

interactive subst_add_vars_upto :
   sequent { <H> >- 'v in Var } -->
   sequent { <H> >- 'v2 in Vars_of{'v} } -->
   sequent { <H> >- 's1 in BTerm } -->
   sequent { <H> >- 's2 in BTerm } -->
   sequent { <H> >- bdepth{'v} >= bdepth{'s1} } -->
   sequent { <H> >- bdepth{'v} >= bdepth{'s2} } -->
   sequent { <H> >- bdepth{'v2} <= bdepth{'s1} } -->
   sequent { <H> >- not_free{'v2;'s1} } -->
   sequent { <H> >- not_free{'v2;'v} } -->
   sequent { <H> >- subst{add_vars_upto{'s1;'v};'v2;'s2} ~ add_vars_upto{'s1;'v} }

doc <:doc< @begin[doc]
   Two substitutions commute.
@end[doc] >>
interactive subst_commutativity {| intro [] |} :
   sequent { <H> >- 't in BTerm } -->
   sequent { <H> >- 'v1 in Vars_of{'s2} } -->
   sequent { <H> >- 'v2 in Vars_of{'s1} } -->
   sequent { <H> >- 's1 in BTerm } -->
   sequent { <H> >- 's2 in BTerm } -->
   sequent { <H> >- bdepth{'t} >= bdepth{'s1} } -->
   sequent { <H> >- bdepth{'t} >= bdepth{'s2} } -->
   sequent { <H> >- not{"assert"{is_eq{'v1;'v2}}} } -->
   sequent { <H> >- not_free{'v1;'s2} } -->
   sequent { <H> >- not_free{'v2;'s1} } -->
   sequent { <H> >- subst{subst{'t;'v1;'s1};'v2;'s2} ~ subst{subst{'t;'v2;'s2};'v1;'s1} }
doc docoff

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform new_var_df: new_var{'bt} = `"new_var(" slot{'bt} `")"
dform add_var_df : add_var{'bt;'v} =
   `"add_var(" slot{'bt} `"; " slot{'v} `")"
dform add_var_df1 : add_var{'bt} = `"add_var(" slot{'bt} `")"
dform add_vars_upto_df : add_vars_upto{'s;'t} =
   `"add_vars_upto(" slot{'s} `"; " slot{'t} `")"
dform subst_df : subst{'t;'v;'s} =
   `"subst(" slot{'t} `"; " slot{'v} `"; " slot{'s} `")"
dform not_free_df : not_free{'v;'t} =
   `"not_free(" slot{'v} `"; " slot{'t} `")"

(*
 *  bind(x. bterm{<H>.b[x]} ) = bterm{x,<H>.b[x]}
 *)
(*
define unfold_var_0: var_0 <--> var{0;0}
define unfold_tmp_var: tmp_var <--> var{-1;0} (* Not a real var *)

define unfold_bind:
   bind{x.'bt['x]} <-->  subst{add_var{'bt[tmp_var];var_0};tmp_var;var_0}
(*
   bind{x.'bt['x]} <-->
      fix{bind.lambda{bt.
         dest_bterm{'bt;
                    u. var{left{'u}+@1;right{'u}};
                    op,subterms. make_bterm{bind{'op}; map{x.'bind 'x; 'subterms}} }
         }} 'bt[var{-1;0}]
*)
interactive_rw bind_id_rw:
   bind{x.'x}  <--> var[0;0]

interactive_rw bind_nobind_rw:
   bind{x.bind{y.'t['x]}}  <--> add_var{{bind{x.'t['x]}}; var{1;0}}

interactive_rw nobind_rw:
   bind{x.'t}  <--> add_var{'t; var{0;0}}

interactive_rw bind__makebterm_rw:
   bind{x.make_bterm{'op['x]; 'subterms['x]}}  <--> make_bterm{'op[var{-1;0}]; map{'bt.bind{x.'bt['x]};'subterms}}
 docoff
*)
