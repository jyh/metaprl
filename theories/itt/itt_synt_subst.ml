doc <:doc<
   @begin[doc]
   @module[Itt_synt_bterm]

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
 *  add_var( <H>;<J>.s; <H>,x,<J'>.x ) = <H>,x,<J>.s
 *)
define unfold_add_var:
   add_var{'bt;'v} <-->
      fix{add.lambda{bt.
         dest_bterm{'bt;
                    u. if left{'v}<=@ left{'u} then var{left{'u}+@1;right{'u}} else var{left{'u};right{'u}+@1};
                    op,subterms. make_bterm{'op;map{x.'add 'x; 'subterms}} }
         }} 'bt

(*
 *  add_var( <H>.s ) = <H>,x.s
 *)
define unfold_add_var1:
   add_var{'bt} <--> add_var{'bt; var{bdepth{'bt};0}}

(*
 *  add_vars_upto( <H>.s; <H>,<J>.t ) = <H>,<J>.s
 *)
define unfold_add_vars_upto:
   add_vars_upto{'s;'t} <--> ind{bdepth{'t} -@ bdepth{'s};'s; k,s.add_var{'s}}


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
   ('v in Var)  -->
   ('s in BTerm)  -->
   (bdepth{'t} >= bdepth{'s})  -->
   bdepth{subst{'t;'v;'s}} <--> bdepth{'t}

interactive subst_wf {| intro [] |} :
   sequent { <H> >- 't in BTerm } -->
   sequent { <H> >- 'v in Var } -->
   sequent { <H> >- 's in BTerm } -->
   sequent { <H> >- bdepth{'t} >= bdepth{'s} } -->
   sequent { <H> >- subst{'t;'v;'s} in BTerm }

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

doc docoff

