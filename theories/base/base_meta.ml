(*
 * Basic arithmetic operations.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/htmlman/default.html or visit http://metaprl.org/
 * for more information.
 *
 * Copyright (C) 1998 Jason Hickey, Cornell University
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
 * Author: Jason Hickey <jyh@cs.cornell.edu>
 * Modified By: Aleksey Nogin <nogin@cs.cornell.edu>
 *)

extends Shell_theory
extends Summary
extends Ocaml_df

open Term_sig
open Refiner.Refiner
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermOp
open Refiner.Refiner.RefineError

(*
 * Meta-operations.
 *)
declare typeclass MetaNum -> Term

declare meta_num[n:n]          : MetaNum
declare meta_sum[a:n, b:n]     : MetaNum
declare meta_diff[a:n, b:n]    : MetaNum
declare meta_prod[a:n, b:n]    : MetaNum
declare meta_quot[a:n, b:n]    : MetaNum
declare meta_rem[a:n, b:n]     : MetaNum

declare meta_eq[a:n,b:n]{'tt : 'a; 'ff : 'a} : 'a
declare meta_eq[a:s,b:s]{'tt : 'a; 'ff : 'a} : 'a
declare meta_eq[a:t,b:t]{'tt : 'a; 'ff : 'a} : 'a
declare meta_eq[a:l,b:l]{'tt : 'a; 'ff : 'a} : 'a
declare meta_eq[a:sh,b:sh]{'tt : 'a; 'ff : 'a} : 'a

declare meta_lt[a:n,b:n]{'tt : 'a; 'ff : 'a} : 'a
declare meta_lt[a:s,b:s]{'tt : 'a; 'ff : 'a} : 'a
declare meta_lt[a:t,b:t]{'tt : 'a; 'ff : 'a} : 'a
declare meta_lt[a:l,b:l]{'tt : 'a; 'ff : 'a} : 'a

(*
 * Arithmetic operations.
 *)
let arith op goal =
   match explode_term goal with
      MatchTerm (_, [MatchNumber (i1, _); MatchNumber (i2, _)], []) ->
         <:con< meta_num[$op i1 i2$:n] >>
    | _ ->
         raise (RefineError ("Base_int.arith", StringTermError ("ill-formed operation", goal)))

let check_zero op =
   fun a b ->
      if Lm_num.is_zero b then raise (RefineError ("Base_meta.arith", StringError "division by zero"))
      else op a b

(*
 * sum{op1[@i1:n]; op2[@i2:n]} --> op1[@i1 + @i2]
 *)
ml_rw reduce_meta_sum : ('goal : meta_sum[a:n, b:n]) =
   arith Lm_num.add_num goal

ml_rw reduce_meta_diff : ('goal : meta_diff[a:n, b:n]) =
   arith Lm_num.sub_num goal

ml_rw reduce_meta_prod : ('goal : meta_prod[a:n, b:n]) =
   arith Lm_num.mult_num goal

ml_rw reduce_meta_quot : ('goal : meta_quot[a:n, b:n]) =
   arith (check_zero Lm_num.div_num) goal

ml_rw reduce_meta_rem  : ('goal : meta_rem[a:n, b:n]) =
   arith (check_zero Lm_num.rem_num) goal

(*
 * eq[p1,p2]{t1,t2} --> t1 if p1 = p2
 *                  --> t2 if p1 <> p2
 *)
let eq goal =
   let true_term, false_term = two_subterms goal in
   let flag = match dest_params (dest_op (dest_term goal).term_op).op_params with
      [ Number i1; Number i2 ] ->
         Lm_num.eq_num i1 i2
    | [ String s1; String s2 ] ->
         s1 = s1
    | [ Token t1; Token t2 ] ->
         Opname.eq t1 t2
    | [ MLevel l1; MLevel l2 ] ->
         l1 == l2
    | [ Shape sh1; Shape sh2 ] ->
         TermShape.eq sh1 sh2
    | _ ->
         raise (RefineError ("meta_eq", StringTermError ("ill-formed operation", goal)))
   in
      if flag then
         true_term
      else
         false_term

ml_rw reduce_meta_eq_num : ('goal : meta_eq[a:n, b:n]{'tt; 'ff}) = eq goal
ml_rw reduce_meta_eq_str : ('goal : meta_eq[a:s, b:s]{'tt; 'ff}) = eq goal
ml_rw reduce_meta_eq_tok : ('goal : meta_eq[a:t, b:t]{'tt; 'ff}) = eq goal
ml_rw reduce_meta_eq_lev : ('goal : meta_eq[a:l, b:l]{'tt; 'ff}) = eq goal
ml_rw reduce_meta_eq_shp : ('goal : meta_eq[a:sh, b:sh]{'tt; 'ff}) = eq goal

let lt goal =
   let true_term, false_term = two_subterms goal in
   let flag = match dest_params (dest_op (dest_term goal).term_op).op_params with
      [ Number i1; Number i2 ] ->
         Lm_num.lt_num i1 i2
    | [ String s1; String s2 ] ->
         s1 < s2
    | [ MLevel l1; MLevel l2 ] ->
         level_lt l1 l2
    | _ ->
         raise (RefineError ("meta_lt", StringTermError ("ill-formed operation", goal)))
   in
      if flag then true_term else false_term

ml_rw reduce_meta_lt_num : ('goal : meta_lt[a:n, b:n]{'tt; 'ff}) = lt goal
ml_rw reduce_meta_lt_str : ('goal : meta_lt[a:s, b:s]{'tt; 'ff}) = lt goal
ml_rw reduce_meta_lt_lev : ('goal : meta_lt[a:l, b:l]{'tt; 'ff}) = lt goal

dform num_df  : meta_num[n:n] = slot[n:n] subm
dform sum_df  : meta_sum[m:n,n:n] = slot[m:n] `" +" subm space slot[n:n]
dform diff_df : meta_diff[m:n,n:n] = slot[m:n] `" -" subm space slot[n:n]
dform quot_df : meta_quot[m:n,n:n] = slot[m:n] `" " div subm space slot[n:n]
dform prod_df : meta_prod[m:n,n:n] = slot[m:n] `" *" subm space slot[n:n]

(*
 * -*-
 * Local Variables:
 * Caml-master: "mp.run"
 * End:
 * -*-
 *)
