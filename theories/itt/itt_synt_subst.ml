doc <:doc<
   @begin[doc]
   @module[Itt_synt_subst]

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

doc <:doc< @doc{@terms} >>

(*
 *  new_var(<H>.t ) = <H>,x.x
 *)
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

(*
 *  add_var( <H>;<J>.s; <H>,x,<J'>.x ) = <H>,x,<J>.s
 *)
define unfold_add_var:
   add_var{'bt;'v} <-->
      fix{add.lambda{bt.
         dest_bterm{'bt;
                    u. if left{'v} <=@ left{'u}
                        then var{left{'u}+@1;right{'u}}
                        else var{left{'u};right{'u}+@1};
                    op,subterms. make_bterm{bind{'op}; map{x.'add 'x; 'subterms}} }
         }} 'bt

let fold_add_var = makeFoldC << add_var{'bt;'v} >> unfold_add_var

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

(*
 *  add_var( <H>.s ) = <H>,x.s
 *)
define unfold_add_new_var:
   add_var{'bt} <--> add_var{'bt; new_var{'bt}}

interactive_rw add_new_var_reduce1 {| reduce |} :
   'op in BOperator -->
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

(*
 *  add_vars_upto( <H>.s; <H>,<J>.t ) = <H>,<J>.s
 *)
define unfold_add_vars_upto:
   add_vars_upto{'s;'t} <--> ind{bdepth{'t} -@ bdepth{'s};'s; k,s.add_var{'s}}

let fold_add_vars_upto = makeFoldC << add_vars_upto{'s;'t} >> unfold_add_vars_upto

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


(*
 *  subst( <H>,x,<J_1>,<J_2>.t[x]; var(<H>,x,<J_3>.x); <H>,x,<J_1>.s[x] ) = <H>,x,<J_1>,<J_2>.t[s[x]]
 *)
define unfold_subst:
   subst{'t;'v;'s} <-->
      fix{subst.lambda{t.
         dest_bterm{'t;
                    u. if is_eq{'v;'u} then add_vars_upto{'s;'u} else 'u;
                    op,subterms. make_bterm{'op;map{x.'subst 'x; 'subterms}} }
         }} 't

let fold_subst = makeFoldC << subst{'t;'v;'s} >> unfold_subst

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


define unfold_not_free: not_free{'v;'t} <-->
      fix{not_free.lambda{t.
          dest_bterm{'t;
                    u. "assert"{bnot{is_eq{'v;'u}}};
                    op,subterms.
                       all_list{ 'subterms; t.'not_free 't} }
         }} 't

let fold_not_free = makeFoldC << not_free{'v;'t} >> unfold_not_free

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

interactive subst_not_free :
   sequent { <H> >- 't in BTerm } -->
   sequent { <H> >- 'v in Vars_of{'t} } -->
   sequent { <H> >- 's in BTerm } -->
   sequent { <H> >- bdepth{'t} >= bdepth{'s} } -->
   sequent { <H> >- not_free{'v;'t} } -->
   sequent { <H> >- subst{'t;'v;'s} ~ 't }
(*
interactive add_var_not_free {| intro[] |} :
   sequent { <H> >- 't in BTerm } -->
   sequent { <H> >- 'v in Var } -->
   sequent { <H> >- 'v1 in Var } -->
   sequent { <H> >- not_free{'v;'t} } -->
   sequent { <H> >- not_free{'v; add_var{'t; 'v1}} }
*)
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
   sequent { <H> >- not_free{'v2;'s1} } -->
   sequent { <H> >- not_free{'v2;'v} } -->
   sequent { <H> >- subst{add_vars_upto{'s1;'v};'v2;'s2} ~ add_vars_upto{'s1;'v} }

interactive subst_commutativity {| intro [] |} :
   sequent { <H> >- 't in BTerm } -->
   sequent { <H> >- 'v1 in Vars_of{'t} } -->
   sequent { <H> >- 'v2 in Vars_of{'t} } -->
   sequent { <H> >- 's1 in BTerm } -->
   sequent { <H> >- 's2 in BTerm } -->
   sequent { <H> >- bdepth{'t} >= bdepth{'s1} } -->
   sequent { <H> >- bdepth{'t} >= bdepth{'s2} } -->
   sequent { <H> >- not{"assert"{is_eq{'v1;'v2}}} } -->
   sequent { <H> >- not_free{'v1;'s2} } -->
   sequent { <H> >- not_free{'v2;'s1} } -->
   sequent { <H> >- subst{subst{'t;'v1;'s1};'v2;'s2} ~ subst{subst{'t;'v2;'s2};'v1;'s1} }
(*
 * Iterated subst - the relative position of the two variables may matter
 *
 *  subst( subst( <H>,v1,<J>,v2,<K>.t[v1;v2]; var(<H>,v1,<J2>.v1); <H>,<J>,v2,<K>.s1[v2] );
 *         var(<H>,<J>,v2,<K2>.v2);
 *         <H>,<J>,<K>.s2) =
 * <H>,<J>,<K>.t[s1[s2];s2] =
 *  subst( subst( <H>,v1,<J>,v2,<K>.t[v1;v2]; var(<H>,vx,<J>,v2,<K2>.v2); <H>,vx,<J>,<K>.s2 );
 *         var(<H>,v1,<J2>.v1);
 *         subst(<H>,<J>,v2,<K>.s1[v2]; var(<H>,<J>,v2,<K2>.v2); <H>,<J>,<K>.s2 ))
 *
 *  subst( subst( <H>,v2,<J>,v1,<K>.t[v1;v2]; var(<H>,v2,<J>,v1,<K2>.v1); <H>,v2,<J>,<K>.s1[v2] );
 *         var(<H>,v2,<J2>.v2);
 *         <H>,<J>,<K>.s2) =
 * <H>,<J>,<K>.t[s1[s2];s2] =
 *  subst( subst( <H>,v2,<J>,v1,<K>.t[v1;v2]; var(<H>,v2,<J2>.v2); <H>,<J>,vx,<K>.s2);
 *         var(<H>,<J>,v1,<K2>.v1);
 *         subst(<H>,v2,<J>,<K2>.s1[v2]; var(<H>,v2,<J2>.v2); <H>,<J>,<K>.s2))
 *)

(*
interactive subst_commutes {| intro |}
   sequent{<H> >- subst{subst{'t;'v1;'s1};'v2;'s2} = ...
 *)


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

