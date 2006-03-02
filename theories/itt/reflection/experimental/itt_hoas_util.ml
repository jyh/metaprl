(*
 * Some utilities for wrapping and simplifying the reflection theory.
 * We define a new kind of language olang{'ops}, where 'ops is an
 * operator list, and we define several simplified theorems, including
 * induction, and squiggle equality.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2005-2006 Mojave Group, Caltech
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * Author: Jason Hickey @email{jyh@cs.caltech.edu}
 * Modified by: Aleksey Nogin @email{nogin@cs.caltech.edu}
 * @end[license]
 *)
doc <:doc< @parents >>

extends Itt_hoas_bterm

doc docoff

open Lm_printf

open Basic_tactics

open Itt_list
open Itt_struct

(************************************************************************
 * Ignore terms.
 *)
doc <:doc<
   The << dummy_term >> is used for constants that don't mean anything.
>>
declare dummy_term

define unfold_dummy_bterm {| reduce |} : dummy_bterm <--> <:xterm<
   $`"dummy_term"
>>

(************************************************************************
 * Properties of compatible_shapes.
 *)
doc <:doc<
   When using induction on a specific language, it is useful to have elimination
   rules for each of the specific operators in the language.  The << listmem_set{'ops; Operator} >>
   term can be used for a case analysis on the operators.  Once given a specific
   operator, we need to split the subterm list into a list of a specific length.
>>
interactive subterm_cons_elim 'H 'depth ('h :: 't) :
   [wf] sequent { <H>; l: list{BTerm}; <J['l]> >- 'depth in nat } -->
   [wf] sequent { <H>; l: list{BTerm}; <J['l]> >- 'h in int } -->
   [aux] sequent { <H>; l: list{BTerm}; <J['l]> >- compatible_shapes{'depth; 'h :: 't; 'l} } -->
   sequent { <H>; e: BTerm; l: list{BTerm}; <J['e :: 'l]>;
       bdepth{'e} = 'depth +@ 'h in nat;
       compatible_shapes{'depth; 't; 'l} >-
       'C['e :: 'l] } -->
   sequent { <H>; l: list{BTerm}; <J['l]> >- 'C['l] }

interactive subterm_nil_elim 'H 'depth :
   [wf] sequent { <H>; l: list{BTerm}; <J['l]> >- 'depth in nat } -->
   [aux] sequent { <H>; l: list{BTerm}; <J['l]> >- compatible_shapes{'depth; nil; 'l} } -->
   sequent { <H>; <J[nil]> >- 'C[nil] } -->
   sequent { <H>; l: list{BTerm}; <J['l]> >- 'C['l] }

doc docoff

let compatible_shapes_opname = opname_of_term << compatible_shapes{'depth; 'l1; 'l2} >>
let dest_compatible_shapes_term = dest_dep0_dep0_dep0_term compatible_shapes_opname

let rec dest_compatible_shapes i p =
   let i = get_pos_hyp_num p i in
   let t = nth_hyp p i in
   let depth, op, subs = dest_compatible_shapes_term t in
      if is_var_term subs then
         let v = dest_var subs in
         let j = get_decl_number p v in
            if is_cons_term op then
               subterm_cons_elim j depth op thenMT (thinT (i + 1) thenT funT (dest_compatible_shapes (-1)))
            else if is_nil_term op then
               subterm_nil_elim j depth thenMT thinT (-1)
            else
               raise (RefineError ("Itt_hoas_util.dest_compatible_shapes", StringTermError ("opname should be a constant", op)))
      else
         raise (RefineError ("Itt_hoas_util.dest_compatible_shapes", StringTermError ("subterms should be a variable", subs)))

let dest_compatible_shapesT i =
   funT (dest_compatible_shapes i)

let dest_compatible_shapes_shapeT i =
   rw (addrC [Subterm 2] reduceC) i thenT dest_compatible_shapesT i

let resource elim +=
    [<< compatible_shapes{'depth; 'h :: 't; !v} >>,   wrap_elim dest_compatible_shapesT;
     << compatible_shapes{'depth; nil; !v} >>,        wrap_elim dest_compatible_shapesT;
     << compatible_shapes{'depth; shape{'op}; !v} >>, wrap_elim dest_compatible_shapes_shapeT]

let resource forward +=
    [<< compatible_shapes{'depth; 'h :: 't; !v} >>,   { forward_loc = (LOCATION); forward_prec = forward_normal_prec; forward_tac = dest_compatible_shapesT };
     << compatible_shapes{'depth; nil; !v} >>,        { forward_loc = (LOCATION); forward_prec = forward_normal_prec; forward_tac = dest_compatible_shapesT };
     << compatible_shapes{'depth; shape{'op}; !v} >>, { forward_loc = (LOCATION); forward_prec = forward_normal_prec; forward_tac = dest_compatible_shapes_shapeT }]

(************************************************************************
 * Custom rewrite annotation processor.
 *)
let arith_opnames =
   OpnameSet.of_list (List.map opname_of_term [<<'a +@ 'b>>; <<-'a>>; <<'a -@ 'b>>; <<'a *@ 'b>> ])

let is_arith_term t _ =
   OpnameSet.mem arith_opnames (opname_of_term t)

let rec reduce_addrs conv = function
   [] -> conv
 | addr :: adrrs -> reduce_addrs conv adrrs thenC addrLiteralC addr reduceC

let arith_rw_annotation name ?labels rwname redex contractum _ addrs args loc rw =
   rule_labels_not_allowed loc labels;
   match addrs, args with
      { spec_ints = [||]; spec_addrs = [||] }, [] ->
         [redex, reduce_addrs (rewrite_of_pre_rewrite rw empty_rw_args []) (find_subterm contractum is_arith_term)]
    | _ ->
         raise (Invalid_argument (sprintf "%s: rewrite %s: %s resource does not support
annotations on rewrites that take arguments" (Simple_print.string_of_loc loc) rwname name))

