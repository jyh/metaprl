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

doc <:doc<
   Define a ``guard'' term << guard{'e} >> for help in defining rewrite addresses.
>>
define unfold_guard : guard{'e} <--> 'e

doc docoff

dform guard_df : guard{'e} =
   `"{" 'e `"}"

let fold_guard = makeFoldC << guard{'e} >> unfold_guard

doc <:doc<
   A rewrite context << "rewrite_context"{| <H> >- 'C |} >> is a sequent
   that expands to sequence of meta-lambdas.
>>
prim_rw unfold_meta_rewrite : sequent ["rewrite_context"] { <H> >- 'C } <-->
   sequent_ind{h. hyp{htype{'h}; x. happly{'h; 'x}}; Sequent{| <H> >- 'C |}}

doc <:doc<
   Rewrite in a context.
>>
interactive rewrite_context_intro :
   sequent { <H> >- rewrite_context{| >- Perv!"rewrite"{'e1; 'e2} |} } -->
   sequent { <H> >- Perv!"rewrite"{'e1; 'e2} }

doc <:doc<
   A substitution function is rewrite-equal if its argument is
   rewrite-equal.
>>
interactive rewriteSubTerm 'x 'y bind{z. 's['z]} :
   sequent { <H> >- rewrite_context{| <J> >- Perv!"rewrite"{'x; 'y} |} } -->
   sequent { <H> >- rewrite_context{| <J> >- Perv!"rewrite"{'s['x]; 's['y]} |} }

doc <:doc<
   Two terms are equal if they are equal in context.
>>
interactive rewriteEqual {| intro [] |} :
   sequent { <H> >- rewrite_context{| <J> >- Perv!"rewrite"{'t; 't} |} }
doc docoff

(*
 * Rewrite contexts.
 *)
let rewrite_context_term = << rewrite_context >>
let rewrite_context_opname = opname_of_term rewrite_context_term
let is_rewrite_context_term = is_no_subterms_term rewrite_context_opname

let mk_rewrite_context_term hyps concl =
   let seq =
      { sequent_args = rewrite_context_term;
        sequent_hyps = hyps;
        sequent_concl = concl
      }
   in
      mk_sequent_term seq

let dest_rewrite_context_term t =
   let { sequent_args = arg;
         sequent_hyps = hyps;
         sequent_concl = concl
       } = explode_sequent t
   in
      if is_rewrite_context_term arg then
         hyps, concl
      else
         raise (RefineError ("dest_rewrite_context", StringError "not a rewrite context term"))

(*
 * Resolve a primitive rewrite.
 *)
let v_x = Lm_symbol.add "x"

let rewrite_so_var p =
   let t = Sequent.concl p in
   let _, t = dest_rewrite_context_term t in
   let t1, t2 = dest_rewrite_term t in
   let v1, cs, ts1 = dest_so_var t1 in
   let v2, _, ts2 = dest_so_var t2 in
      match ts1, ts2 with
         [t1], [t2] when Lm_symbol.eq v1 v2 ->
            rewriteSubTerm t1 t2 (mk_bind1_term v_x (mk_so_var_term v1 cs [mk_var_term v_x]))
       | _ ->
            raise (RefineError ("rewrite_so_var", StringError "bad match"))

let rewriteSOVarT = funT rewrite_so_var

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
