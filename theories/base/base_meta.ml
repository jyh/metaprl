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

declare meta_eq{'a; 'b; 'tt; 'ff}
declare meta_le{'a; 'b; 'tt; 'ff}
declare meta_lt{'a; 'b; 'tt; 'ff}

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
 * eq{op1[@t:t]; op2[p1]; op3[p2]} --> op1["true":t] if p1 = p2
 *                                 --> op2["false":t] if p1 <> p2
 *)
let eq goal =
   let a, b, true_term, false_term = four_subterms goal in
   let { term_op = op1; term_terms = terms1 } = dest_term a in
   let { term_op = op2; term_terms = terms2 } = dest_term b in
   let { op_name = name1; op_params = params1 } = dest_op op1 in
   let { op_name = name2; op_params = params2 } = dest_op op2 in
      match params1, params2, terms1, terms2 with
         [p1], [p2], [], [] when Opname.eq name1 name2 ->
            let flag =
               match dest_param p1, dest_param p2 with
                  Number i1, Number i2 ->
                     Mp_num.eq_num i1 i2
                | String s1, String s2
                | Var s1, Var s2 ->
                     s1 = s2
                | Token t1, Token t2 ->
                     t1 = t2
                | MLevel l1, MLevel l2 ->
                     l1 == l2
                | _ ->
                     raise (RefineError ("meta_eq", StringTermError ("ill-formed operation", goal)))
            in
               if flag then true_term else false_term
       | _ ->
            raise (RefineError ("Base_int.eq", StringTermError ("ill-formed operation", goal)))

ml_rw reduce_meta_eq : ('goal : meta_eq{'a; 'b; 'tt; 'ff}) =
   eq goal

let lt goal =
   let a, b, true_term, false_term = four_subterms goal in
   let { term_op = op1; term_terms = terms1 } = dest_term a in
   let { term_op = op2; term_terms = terms2 } = dest_term b in
   let { op_name = name1; op_params = params1 } = dest_op op1 in
   let { op_name = name2; op_params = params2 } = dest_op op2 in
      match params1, params2, terms1, terms2 with
         [p1], [p2], [], [] when Opname.eq name1 name2 ->
            let flag =
               match dest_param p1, dest_param p2 with
                  Number i1, Number i2 ->
                     Mp_num.lt_num i1 i2
                | String s1, String s2 ->
                     s1 < s2
                | Token t1, Token t2 ->
                     t1 < t2
                | MLevel l1, MLevel l2 ->
                     level_lt l1 l2
                | Var s1, Var s2 ->
                     s1 = s2
                | _ ->
                     raise (RefineError ("meta_lt", StringTermError ("ill-formed operation", goal)))
            in
               if flag then true_term else false_term
       | _ ->
            raise (RefineError ("Base_int.lt", StringTermError ("ill-formed operation", goal)))

ml_rw reduce_meta_lt : ('goal : meta_lt{'a; 'b; 'tt; 'ff}) =
   lt goal

let le goal =
   let a, b, true_term, false_term = four_subterms goal in
   let { term_op = op1; term_terms = terms1 } = dest_term a in
   let { term_op = op2; term_terms = terms2 } = dest_term b in
   let { op_name = name1; op_params = params1 } = dest_op op1 in
   let { op_name = name2; op_params = params2 } = dest_op op2 in
      match params1, params2, terms1, terms2 with
         [p1], [p2], [], [] when Opname.eq name1 name2 ->
            let flag =
               match dest_param p1, dest_param p2 with
                  Number i1, Number i2 ->
                     Mp_num.le_num i1 i2
                | String s1, String s2
                | Var s1, Var s2 ->
                     s1 <= s2
                | Token t1, Token t2 ->
                     t1 <= t2
                | MLevel l1, MLevel l2 ->
                     level_le l1 l2
                | _ ->
                     raise (RefineError ("meta_le", StringTermError ("ill-formed operation", goal)))
            in
               if flag then true_term else false_term
       | _ ->
            raise (RefineError ("Base_int.le", StringTermError ("ill-formed operation", goal)))

ml_rw reduce_meta_le : ('goal : meta_le{'a; 'b; 'tt; 'ff}) =
   le goal

(*
 * -*-
 * Local Variables:
 * Caml-master: "mp.run"
 * End:
 * -*-
 *)
