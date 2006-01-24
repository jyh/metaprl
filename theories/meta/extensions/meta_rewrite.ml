doc <:doc<
   @spelling{rewriter}

   @module[Meta_rewrite]

   Meta-rewrites can be performed in a meta-sequent.

   @docoff
   ----------------------------------------------------------------

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 1998 Jason Hickey, Cornell University

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

   Author: Jason Hickey @email{jyh@cs.caltech.edu}
   Modified By: Aleksey Nogin @email{nogin@cs.caltech.edu}

   @end[license]

   @parents
>>
extends Base_theory
extends Meta_context_terms

doc docoff

open Perv
open Basic_tactics
open Meta_context_terms

doc <:doc<
   A substitution function is rewrite-equal if its argument is
   rewrite-equal.
>>
interactive rewrite_subterm 'x 'y bind{z. 's['z]} :
   sequent { <H> >- Perv!"rewrite"{'x; 'y} } -->
   sequent { <H> >- Perv!"rewrite"{'s['x]; 's['y]} }

doc <:doc<
   Two functions are equal if their bodies are equal.
>>
(*
 * XXX: BUG (nogin 01/23/2006): This axiom (in fact, this whole theory) is only used to prove
 * Meta_context_terms2.reduce_sequent_ind_right. This axiom is way too strong (and it also attaches 
 * some pretty specific semantics to Base_rewrite!sequent_arg) and we need to find some way to get rid of it.
 *)
prim rewrite_hlambda bind{x. 'e1['x]} bind{x. 'e2['x]} :
   sequent { <H>; x: Term{'A} >- Perv!"rewrite"{'e1['x]; 'e2['x]} } -->
   sequent { <H> >- Perv!"rewrite"{hlambda{'A; x. 'e1['x]}; hlambda{'A; x. 'e2['x]}} } =
   it
doc docoff

(*
 * Substitution functions.
 *)
let v_x = Lm_symbol.add "x"

let rewrite_so_var p =
   let t = Sequent.concl p in
   let t1, t2 = dest_rewrite_term t in
   let v1, cs, ts1 = dest_so_var t1 in
   let v2, _, ts2 = dest_so_var t2 in
      match ts1, ts2 with
         [t1], [t2] when Lm_symbol.eq v1 v2 ->
            rewrite_subterm t1 t2 (mk_bind1_term v_x (mk_so_var_term v1 cs [mk_var_term v_x]))
       | _ ->
            raise (RefineError ("rewrite_so_var", StringError "bad match"))

let rewriteSOVarT = funT rewrite_so_var

(*
 * Lambda equality.
 *)
let rewrite_hlambda p =
   let t = Sequent.concl p in
   let t1, t2 = dest_rewrite_term t in
   let v1, _, e1 = dest_hlambda_term t1 in
   let v2, _, e2 = dest_hlambda_term t2 in
   let t1 = mk_bind1_term v1 e1 in
   let t2 = mk_bind1_term v2 e2 in
      rewrite_hlambda t1 t2

let rewriteHLambdaT = funT rewrite_hlambda

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
