(*
 * Basic arithmetic operations.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
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
 *
 *)
include Mptop
include Summary

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermOp
open Refiner.Refiner.RefineError

(*
 * Meta-operations.
 *)
declare meta_sum{'a; 'b}
declare meta_diff{'a; 'b}
declare meta_prod{'a; 'b}
declare meta_quot{'a; 'b}
declare meta_rem{'a; 'b}

declare meta_eq[a:n,b:n]{'tt; 'ff}
declare meta_eq[a:s,b:s]{'tt; 'ff}
declare meta_eq[a:v,b:v]{'tt; 'ff}
declare meta_eq[a:t,b:t]{'tt; 'ff}
declare meta_eq[a:l,b:l]{'tt; 'ff}

declare meta_lt[a:n,b:n]{'tt; 'ff}
declare meta_lt[a:s,b:s]{'tt; 'ff}
declare meta_lt[a:t,b:t]{'tt; 'ff}
declare meta_lt[a:l,b:l]{'tt; 'ff}

(*
 * Arithmetic operations.
 *)
let arith op goal =
   let a, b = two_subterms goal in
   let { term_op = op1; term_terms = terms1 } = dest_term a in
   let { term_op = op2; term_terms = terms2 } = dest_term b in
   let { op_name = name1; op_params = params1 } = dest_op op1 in
   let { op_name = name2; op_params = params2 } = dest_op op2 in
   let t =
      match params1, params2, terms1, terms2 with
         [num1], [num2], [], [] when Opname.eq name1 name2 ->
            begin
               match dest_param num1, dest_param num2 with
                  Number i1, Number i2 ->
                     mk_term (mk_op name1 [make_param (Number (op i1 i2))]) []
                | _ ->
                     raise (RefineError ("Base_int.arith", StringTermError ("ill-formed operation", goal)))
            end
       | _ ->
            raise (RefineError ("Base_int.arith", StringTermError ("ill-formed operation", goal)))
   in
      t

let check_zero op =
   fun a b ->
      if Mp_num.is_zero b then raise (RefineError ("Base_meta.arith", StringError "division by zero"))
      else op a b

(*
 * sum{op1[@i1:n]; op2[@i2:n]} --> op1[@i1 + @i2]
 *)
ml_rw reduce_meta_sum : ('goal : meta_sum{'a; 'b}) =
   arith Mp_num.add_num goal

ml_rw reduce_meta_diff : ('goal : meta_diff{'a; 'b}) =
   arith Mp_num.sub_num goal

ml_rw reduce_meta_prod : ('goal : meta_prod{'a; 'b}) =
   arith Mp_num.mult_num goal

ml_rw reduce_meta_quot : ('goal : meta_quot{'a; 'b}) =
   arith (check_zero Mp_num.div_num) goal

ml_rw reduce_meta_rem  : ('goal : meta_rem{'a; 'b}) =
   arith (check_zero Mp_num.rem_num) goal

(*
 * eq[p1,p2]{t1,t2} --> t1 if p1 = p2
 *                  --> t2 if p1 <> p2
 *)
let eq goal =
   let true_term, false_term = two_subterms goal in
   let flag = match List.map dest_param (dest_op (dest_term goal).term_op).op_params with
      [ Number i1; Number i2 ] ->
         Mp_num.eq_num i1 i2
    | [ String s1; String s2 ]
    | [ Var s1; Var s2 ] ->
         s1 = s2
    | [ Token t1; Token t2 ] ->
         t1 = t2
    | [ MLevel l1; MLevel l2 ] ->
         l1 == l2
    | _ ->
         raise (RefineError ("meta_eq", StringTermError ("ill-formed operation", goal)))
   in
      if flag then true_term else false_term

ml_rw reduce_meta_eq_num : ('goal : meta_eq[a:n,b:n]{'tt; 'ff}) = eq goal
ml_rw reduce_meta_eq_str : ('goal : meta_eq[a:s,b:s]{'tt; 'ff}) = eq goal
ml_rw reduce_meta_eq_var : ('goal : meta_eq[a:v,b:v]{'tt; 'ff}) = eq goal
ml_rw reduce_meta_eq_tok : ('goal : meta_eq[a:t,b:t]{'tt; 'ff}) = eq goal
ml_rw reduce_meta_eq_lev : ('goal : meta_eq[a:l,b:l]{'tt; 'ff}) = eq goal

let lt goal =
   let true_term, false_term = two_subterms goal in
   let flag = match List.map dest_param (dest_op (dest_term goal).term_op).op_params with
      [ Number i1; Number i2 ] ->
         Mp_num.lt_num i1 i2
    | [ String s1; String s2 ] ->
         s1 < s2
    | [ Token t1; Token t2 ] ->
         t1 < t2
    | [ MLevel l1; MLevel l2 ] ->
         level_lt l1 l2
    | _ ->
         raise (RefineError ("meta_lt", StringTermError ("ill-formed operation", goal)))
   in
      if flag then true_term else false_term

ml_rw reduce_meta_lt_num : ('goal : meta_lt[a:n, b:n]{'tt; 'ff}) = lt goal
ml_rw reduce_meta_lt_str : ('goal : meta_lt[a:s, b:s]{'tt; 'ff}) = lt goal
ml_rw reduce_meta_lt_tok : ('goal : meta_lt[a:t, b:t]{'tt; 'ff}) = lt goal
ml_rw reduce_meta_lt_lev : ('goal : meta_lt[a:l, b:l]{'tt; 'ff}) = lt goal

(*
 * -*-
 * Local Variables:
 * Caml-master: "mp.run"
 * End:
 * -*-
 *)
