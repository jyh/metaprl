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
extends Itt_synt_var
extends Itt_synt_operator
extends Itt_synt_bterm
doc docoff

open Basic_tactics

doc <:doc< @doc{@terms} >>

(*
 *  subst( <H>,x,<J>.t[x]; var(<H>,x,<J2>.x); <H>,<J>.s ) = <H>,<J>.t[s]
 *)
define unfold_subst:
   subst{'t;'v;'s} <-->
      fix{subst.lambda{t.
         dest_bterm{'t;
                    u. subst_var{'u;'v;'s};
                    op,subterms. make_bterm{'op;map{lambda{x.'subst 'x}; 'subterms}} }
         }} 't

interactive subst_wf {| intro [] |} :
   sequent { <H> >- 't in BTerm } -->
   sequent { <H> >- 'v in Var } -->
   sequent { <H> >- bdepth{'t} >= depth{'v} } -->
   sequent { <H> >- 's in BTerm } -->
   sequent { <H> >- subst{'t;'v;'s} in BTerm }

interactive_rw subst_bdepth {| reduce |} :
   ('t in BTerm)  -->
   ('v in Var)  -->
   (bdepth{'t} >= depth{'v})  -->
   ('s in BTerm)  -->
   bdepth{subst{'t;'v;'s}} <--> bdepth{'t} -@ 1

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

