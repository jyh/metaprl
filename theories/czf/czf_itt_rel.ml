doc <:doc<
   @module[Czf_itt_rel]

   The @tt[Czf_itt_rel] module defines Aczel's @emph{collection}
   scheme :

   $$
   @rel{x; y; {P[x; y]}; a; b} @equiv (@dall{x; a; @dexists{y; b; @phi}}
      @wedge @dall{y; b; @dexists{x; a; @phi}}.
   $$

   There are no rules in this module, except for well-formedness.
   The @tt{rel} term is just a definition.

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

   Author: Jason Hickey
   @email{jyh@cs.cornell.edu}
   @end[license]
>>

doc <:doc< @parents >>
extends Czf_itt_dall
extends Czf_itt_dexists
doc docoff

open Term_sig
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.RefineError

open Dtactic

open Itt_logic

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc<
   @terms
>>
declare rel{a, b. 'P['a; 'b]; 's1; 's2}
doc docoff

let rel_term = << rel{a, b. 'P['a; 'b]; 's1; 's2} >>
let rel_opname = opname_of_term rel_term
let dest_rel t =
   if Opname.eq (opname_of_term t) rel_opname then
      let { term_op = op; term_terms = terms } = dest_term t in
         match terms with
            [bterm1; bterm2; bterm3] ->
               let t2 = dest_simple_bterm bterm2 in
               let t3 = dest_simple_bterm bterm3 in
                  (match dest_bterm bterm1 with
                      { bvars = [v1; v2]; bterm = t1 } ->
                         v1, v2, t1, t2, t3
                    | _ ->
                         raise (RefineError ("dest_rel", StringError "not a rel term")))
          | _ ->
               raise (RefineError ("dest_rel", StringError "not a rel term"))
   else
      raise (RefineError ("dest_rel", StringError "not a rel term"))

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc<
   @rewrites
>>
prim_rw unfold_rel : rel{a, b. 'P['a; 'b]; 's1; 's2} <-->
   (dall{'s1; x. dexists{'s2; y. 'P['x; 'y]}} & dall{'s2; y. dexists{'s1; x. 'P['x; 'y]}})
doc docoff

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform rel_df : parens :: "prec"[prec_quant] :: rel{a, b. 'P; 's1; 's2} =
   szone pushm[3]
   Mpsymbols!mathbbB slot{'a} " " Mpsymbols!member slot{'s1} `"," hspace
   slot{'b} " " Mpsymbols!member " " slot{'s2} `"." hspace
   slot{'P}
   popm ezone

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @rules

   The @tt{rel} term is well-formed if the proposition $P$
   is well-formed, and if the arguments $s_1$ and $s_2$ are sets.
>>
interactive rel_type {| intro [] |} :
   sequent { <H>; u: set; v: set >- "type"{'P['u; 'v]} } -->
   sequent { <H> >- isset{'s1} } -->
   sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- "type"{rel{x, y. 'P['x; 'y]; 's1; 's2}} }
doc docoff

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
