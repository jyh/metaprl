(*
 * Defines term (de)construction operations for terms declared
 * in the FIR theory.
 *
 * ------------------------------------------------------------------------
 *
 * @begin[license]
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.  Additional
 * information about the system is available at
 * http://www.metaprl.org/
 *
 * Copyright (C) 2002 Brian Emre Aydemir, Caltech
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
 * Author: Brian Emre Aydemir
 * @email{emre@cs.caltech.edu}
 * @end[license]
 *)

open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermType
open Refiner.Refiner.RefineError

(**************************************************************************
 * General utility.
 **************************************************************************)

(*
 * Take a term of the form << v1. t1 >> and return ( "v1", t1 ) where
 * "v1" is a string representation of v1.
 *)

let string_term_of_dep1_term t =
   match dest_bterm t with
      { bvars = [s1]; bterm = t1 } ->
         s1, t1
    | _ ->
         raise (Invalid_argument "not a dep1 term")

(*
 * Compares an opname and arities list against those of a term.
 *)

let check_basics opname arities t =
   (Opname.eq (opname_of_term t) opname) &&
   ((subterm_arities t) == arities)

(*
 * Returns the parameter list of a term.
 *)

let get_params t =
   dest_params (dest_op (dest_term t).term_op).op_params

(*
 * Take a list of param' elts and make a list of param elts.
 **)

let mk_params params =
   List.map make_param params

(**************************************************************************
 * Main function definitions.
 **************************************************************************)

(*
 * No parameters, no subterms.
 *)

let is_0_dep0_term = is_no_subterms_term

(*
 * No parameters, 1 subterm.
 *)

let is_1_dep0_term = is_dep0_term
let mk_1_dep0_term = mk_dep0_term
let dest_1_dep0_term = dest_dep0_term

let is_0_dep0_1_dep1_term = is_dep1_term
let mk_0_dep0_1_dep1_term = mk_dep1_term
let dest_0_dep0_1_dep1_term = dest_dep1_term

(*
 * No parameters, 2 subterms.
 *)

let is_2_dep0_term = is_dep0_dep0_term
let mk_2_dep0_term = mk_dep0_dep0_term
let dest_2_dep0_term = dest_dep0_dep0_term

let is_1_dep0_1_dep1_term =
   is_dep0_dep1_term
let mk_1_dep0_1_dep1_term opname t1 str t2 =
   mk_dep0_dep1_term opname str t1 t2
let dest_1_dep0_1_dep1_term opname t =
   let str, t1,t2 = dest_dep0_dep1_term opname t in
      t1, str, t2

(*
 * No parameters, 3 subterms.
 *)

let is_3_dep0_term = is_dep0_dep0_dep0_term
let mk_3_dep0_term = mk_dep0_dep0_dep0_term
let dest_3_dep0_term = dest_dep0_dep0_dep0_term

let is_2_dep0_1_dep1_term = is_dep0_dep0_dep1_term
let mk_2_dep0_1_dep1_term = mk_dep0_dep0_dep1_term
let dest_2_dep0_1_dep1_term = dest_dep0_dep0_dep1_term

(*
 * No parameters, 4 subterms.
 *)

let is_4_dep0_term = is_dep0_dep0_dep0_dep0_term
let mk_4_dep0_term = mk_dep0_dep0_dep0_dep0_term
let dest_4_dep0_term = dest_dep0_dep0_dep0_dep0_term

let is_3_dep0_1_dep1_term opname t =
   (check_basics opname [0;0;0;1] t)

let mk_3_dep0_1_dep1_term opname t1 t2 t3 str t4 =
   mk_term  (make_op { op_name = opname; op_params = [] })
            [ mk_simple_bterm t1; mk_simple_bterm t2;
              mk_simple_bterm t3; mk_bterm [str] t4
            ]

let dest_3_dep0_1_dep1_term opname t =
   match dest_term t with
      { term_terms = [bt1; bt2; bt3; bt4] }
         when (check_basics opname [0;0;0;1] t) ->
         let s4, t4 = string_term_of_dep1_term bt4 in
            dest_simple_bterm bt1,
            dest_simple_bterm bt2,
            dest_simple_bterm bt3,
            s4,
            t4
    | _ ->
         raise (RefineError ("dest_3_dep0_1_dep1_term", StringTermError
               ("invalid term structure", t)))

(*
 * No parameters, 5 subterms.
 *)

let is_5_dep0_term opname t =
   (check_basics opname [0;0;0;0;0] t)

let mk_5_dep0_term opname t1 t2 t3 t4 t5 =
   mk_term  (make_op { op_name = opname; op_params = [] })
            [ mk_simple_bterm t1; mk_simple_bterm t2;
              mk_simple_bterm t3; mk_simple_bterm t4;
              mk_simple_bterm t5
            ]

let dest_5_dep0_term opname t =
   match subterms_of_term t with
      [t1; t2; t3; t4; t5] when is_5_dep0_term opname t ->
         t1, t2, t3, t4, t5
    | _ ->
         raise (RefineError ("dest_5_dep0_term", StringTermError
               ("invalid term structure", t)))

(*
 * 1 number parameter, 0 subterms.
 *)

let is_num_0_dep0_term = is_number_term
let mk_num_0_dep0_term = mk_number_term
let dest_num_0_dep0_term = dest_number_term

(*
 * 1 string parameter, 0 subterms.
 *)

let is_str_0_dep0_term = is_string_term
let mk_str_0_dep0_term = mk_string_term
let dest_str_0_dep0_term = dest_string_term

(*
 * 1 number parameter, 1 subterm.
 *)

let is_num_1_dep0_term opname t =
   match get_params t with
      [Number _] -> (check_basics opname [0] t)
    | _ -> false

let mk_num_1_dep0_term opname i t =
   mk_term  (make_op { op_name = opname;
                       op_params = mk_params [Number i] })
            [mk_simple_bterm t]

let dest_num_1_dep0_term opname t =
   match get_params t, subterms_of_term t with
      [Number i], [t1] when (check_basics opname [0] t) ->
         i, t1
    | _ ->
         raise (RefineError ("dest_num_1_dep0_term", StringTermError
               ("invalid term structure", t)))

(*
 * 1 string parameter, 1 subterm.
 *)

let is_str_1_dep0_term = is_string_dep0_term
let mk_str_1_dep0_term = mk_string_dep0_term
let dest_str_1_dep0_term = dest_string_dep0_term

(*
 * 1 string parameter, 2 subterms.
 *)

let is_str_2_dep0_term opname t =
   match get_params t with
      [String _] -> (check_basics opname [0;0] t)
    | _ -> false

let mk_str_2_dep0_term opname str t1 t2 =
   mk_term  (make_op { op_name = opname;
                       op_params = mk_params [String str] })
            [mk_simple_bterm t1; mk_simple_bterm t2]

let dest_str_2_dep0_term opname t =
   match get_params t, subterms_of_term t with
      [String str], [t1; t2] when (check_basics opname [0;0] t) ->
         str, t1, t2
    | _ ->
         raise (RefineError ("dest_str_2_dep0_term", StringTermError
               ("invalid term structure", t)))

(*
 * 1 string parameter, 2 subterms.
 *)

let is_num_3_dep0_term opname t =
   match get_params t with
      [Number i] -> (check_basics opname [0;0;0] t)
    | _ -> false

let mk_num_3_dep0_term opname i t1 t2 t3 =
   mk_term  (make_op { op_name = opname;
                       op_params = mk_params [Number i] })
            [mk_simple_bterm t1; mk_simple_bterm t2; mk_simple_bterm t3]

let dest_num_3_dep0_term opname t =
   match get_params t, subterms_of_term t with
      [Number i], [t1; t2; t3] when (check_basics opname [0;0;0] t) ->
         i, t1, t2, t3
    | _ ->
         raise (RefineError ("dest_num_3_dep0_term", StringTermError
               ("invalid term structure", t)))

(*
 * 1 string parameter, 4 subterms.
 *)

let is_str_3_dep0_1_dep1_term opname t =
   match get_params t with
      [String _] -> (check_basics opname [0;0;0;1] t)
    | _ -> false

let mk_str_3_dep0_1_dep1_term opname str1 t1 t2 t3 str2 t4 =
   mk_term  (make_op { op_name = opname;
                       op_params = mk_params [String str1] })
            [ mk_simple_bterm t1; mk_simple_bterm t2;
              mk_simple_bterm t3; mk_bterm [str2] t4
            ]

let dest_str_3_dep0_1_dep1_term opname t =
   match get_params t, dest_term t with
      [String str1], { term_terms = [bt1; bt2; bt3; bt4] }
         when (check_basics opname [0;0;0;1] t) ->
         let str2, t4 = string_term_of_dep1_term bt4 in
            str1,
            dest_simple_bterm bt1,
            dest_simple_bterm bt2,
            dest_simple_bterm bt3,
            str2,
            t4
    | _ ->
         raise (RefineError ("dest_str_3_dep0_1_dep1_term", StringTermError
               ("invalid term structure", t)))

(*
 * 2 number parameters, 0 subterms.
 *)

let is_num_num_0_dep0_term opname t =
   match get_params t with
      [Number _; Number _] -> (check_basics opname [] t)
    | _ -> false

let mk_num_num_0_dep0_term opname i1 i2 =
   mk_term  (make_op { op_name = opname;
                       op_params = mk_params [Number i1; Number i2] })
            []

let dest_num_num_0_dep0_term opname t =
   match get_params t with
      [Number i1; Number i2] when (check_basics opname [] t) ->
         i1, i2
    | _ ->
         raise (RefineError ("dest_num_num_0_dep0_term", StringTermError
               ("invalid term structure", t)))

(*
 * 1 number parameter, 1 string parameter, 0 subterms.
 *)

let is_num_str_0_dep0_term opname t =
   match get_params t with
      [Number _; String _] -> (check_basics opname [] t)
    | _ -> false

let mk_num_str_0_dep0_term opname i str =
   mk_term  (make_op { op_name = opname;
                       op_params = mk_params [Number i; String str] })
            []

let dest_num_str_0_dep0_term opname t =
   match get_params t with
      [Number i; String str] when (check_basics opname [] t) ->
         i, str
    | _ ->
         raise (RefineError ("dest_num_str_0_dep0_term", StringTermError
               ("invalid term structure", t)))

(*
 * 1 string parameter, 1 number parameter, 0 subterms.
 *)

let is_str_num_0_dep0_term opname t =
   match get_params t with
      [String _; Number _] -> (check_basics opname [] t)
    | _ -> false

let mk_str_num_0_dep0_term opname str i=
   mk_term  (make_op { op_name = opname;
                       op_params = mk_params [String str; Number i] })
            []

let dest_str_num_0_dep0_term opname t =
   match get_params t with
      [String str; Number i] when (check_basics opname [] t) ->
         str, i
    | _ ->
         raise (RefineError ("dest_str_num_0_dep0_term", StringTermError
               ("invalid term structure", t)))

(*
 * 1 number parameter, 1 string paramter, 1 subterm.
 *)

let is_num_str_1_dep0_term opname t =
   match get_params t with
      [Number _; String _] -> (check_basics opname [0] t)
    | _ -> false

let mk_num_str_1_dep0_term opname i str t1 =
   mk_term  (make_op { op_name = opname;
                       op_params = mk_params [Number i; String str] })
            [mk_simple_bterm t1]

let dest_num_str_1_dep0_term opname t =
   match get_params t, subterms_of_term t with
      [Number i; String str], [t1] when (check_basics opname [0] t) ->
         i, str, t1
    | _ ->
         raise (RefineError ("dest_num_str_1_dep0_term", StringTermError
               ("invalid term structure", t)))

(*
 * 1 number parameter, 1 string parameter, 2 subterms.
 *)

let is_num_str_2_dep0_term opname t =
   match get_params t with
      [Number _; String _] -> (check_basics opname [0;0] t)
    | _ -> false

let mk_num_str_2_dep0_term opname i str t1 t2 =
   mk_term  (make_op { op_name = opname;
                       op_params = mk_params [Number i; String str] })
            [mk_simple_bterm t1; mk_simple_bterm t2]

let dest_num_str_2_dep0_term opname t =
   match get_params t, subterms_of_term t with
      [Number i; String str], [t1; t2] when (check_basics opname [0;0] t) ->
         i, str, t1, t2
    | _ ->
         raise (RefineError ("dest_num_str_2_dep0_term", StringTermError
               ("invalid term structure", t)))

(*
 * 2 string paramters, 2 subterms.
 *)

let is_str_str_2_dep0_term opname t =
   match get_params t with
      [String _; String _] -> (check_basics opname [0;0] t)
    | _ -> false

let mk_str_str_2_dep0_term opname str1 str2 t1 t2 =
   mk_term  (make_op { op_name = opname;
                       op_params = mk_params [String str1; String str2] })
            [mk_simple_bterm t1; mk_simple_bterm t2]

let dest_str_str_2_dep0_term opname t =
   match get_params t, subterms_of_term t with
      [String str1; String str2], [t1; t2] when (check_basics opname [0;0] t) ->
         str1, str2, t1, t2
    | _ ->
         raise (RefineError ("dest_str_str_2_dep0_term", StringTermError
               ("invalid term structure", t)))

(*
 * 2 number parameters, 1 string parameter, 0 subterms.
 *)

(* num_num_str version *)

let is_num_num_str_0_dep0_term opname t =
   match get_params t with
      [Number _; Number _; String _] -> (check_basics opname [] t)
    | _ -> false

let mk_num_num_str_0_dep0_term opname i1 i2 s =
   mk_term  (make_op { op_name = opname;
                       op_params = mk_params [Number i1; Number i2; String s] })
            []

let dest_num_num_str_0_dep0_term opname t =
   match get_params t with
      [Number i1; Number i2; String str] when (check_basics opname [] t) ->
         i1, i2, str
    | _ -> raise (RefineError ("dest_num_num_str_0_dep0_term", StringTermError
                 ("invalid term structure", t)))

(* num_str_num version *)

let is_num_str_num_0_dep0_term opname t =
   match get_params t with
      [Number _; String _; Number _] -> (check_basics opname [] t)
    | _ -> false

let mk_num_str_num_0_dep0_term opname i1 s i2 =
   mk_term  (make_op { op_name = opname;
                       op_params = mk_params [Number i1; String s; Number i2] })
            []

let dest_num_str_num_0_dep0_term opname t =
   match get_params t with
      [Number i1; String str; Number i2] when (check_basics opname [] t) ->
         i1, str, i2
    | _ -> raise (RefineError ("dest_num_str_num_0_dep0_term", StringTermError
                 ("invalid term structure", t)))

(*
 * 3 number parameters, 1 string parameters, 0 subterms.
 *)

let is_num_str_num_num_0_dep0_term opname t=
   match get_params t with
      [Number _; String _; Number _; Number _] -> (check_basics opname [] t)
    | _ -> false

let mk_num_str_num_num_0_dep0_term opname i1 str i2 i3 =
   mk_term  (make_op { op_name = opname;
                       op_params = mk_params [Number i1; String str; Number i2; Number i3] })
            []

let dest_num_str_num_num_0_dep0_term opname t =
   match get_params t with
      [Number i1; String str; Number i2; Number i3]
         when (check_basics opname [] t) ->
         i1, str, i2, i3
    | _ -> raise (RefineError ("dest_num_str_num_num_0_dep0_term", StringTermError
                 ("bad parameters", t)))

(*
 * 2 number parameters, 2 string parameters, 0 subterms.
 *)

let is_num_str_num_str_0_dep0_term opname t =
   match get_params t with
      [Number _; String _; Number _; String _] -> (check_basics opname [] t)
    | _ -> false

let mk_num_str_num_str_0_dep0_term opname i1 str1 i2 str2 =
   mk_term  (make_op { op_name = opname;
                       op_params = mk_params [Number i1; String str1; Number i2; String str2] })
            []

let dest_num_str_num_str_0_dep0_term opname t =
   match get_params t with
      [Number i1; String str1; Number i2; String str2]
         when (check_basics opname [] t) ->
         i1, str1, i2, str2
    | _ -> raise (RefineError ("dest_num_str_num_str_0_dep0_term", StringTermError
                 ("invalid term structure", t)))
