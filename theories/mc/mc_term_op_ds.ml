(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Term construction / deconstruction convinience functions
 * for MC theory terms.
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
 * Email:  emre@its.caltech.edu
 *)

open Opname
open Refine_error_sig
open Term_ds_sig
open Term_ds

(*
 * The function naming scheme here is as follows:
 * X_depY pairs represent X terms in a row, each with Y bound variables.
 * The strings for a given subterm with bound variables come right
 * before the term they appear in both function parameters and
 * return values.
 *)

module type McTermOp_sig =
sig

   type term

   (*
    * 4 subterms.
    *)

   val is_4_dep0_term : opname -> term -> bool
   val mk_4_dep0_term : opname -> term -> term -> term -> term -> term
   val dest_4_dep0_term : opname -> term -> term * term * term * term

   val is_3_dep0_1_dep1_term : opname -> term -> bool
   val mk_3_dep0_1_dep1_term :
      opname -> term -> term -> term -> string -> term -> term
   val dest_3_dep0_1_dep1_term :
      opname -> term -> term * term * term * string * term

   (*
    * 5 subterms.
    *)

   val is_4_dep0_1_dep1_term : opname -> term -> bool
   val mk_4_dep0_1_dep1_term :
      opname -> term -> term -> term -> term -> string -> term -> term
   val dest_4_dep0_1_dep1_term :
      opname -> term -> term * term * term * term * string * term

   (*
    * 6 subterms.
    *)

   val is_5_dep0_1_dep1_term : opname -> term -> bool
   val mk_5_dep0_1_dep1_term :
      opname -> term -> term -> term -> term -> term -> string -> term -> term
   val dest_5_dep0_1_dep1_term :
      opname -> term -> term * term * term * term * term * string * term
end

(*
 * Define the actual module now.
 *)

module McTermOp
   (Term : TermDsSig
    with type level_exp_var = TermType.level_exp_var
    with type level_exp = TermType.level_exp
    with type param = TermType.param
    with type operator = TermType.operator
    with type term = TermType.term
    with type term_core = TermType.term_core
    with type bound_term = TermType.bound_term

    with type level_exp_var' = TermType.level_exp_var'
    with type level_exp' = TermType.level_exp'
    with type object_id = TermType.object_id
    with type param' = TermType.param'
    with type operator' = TermType.operator'
    with type term' = TermType.term'
    with type bound_term' = TermType.bound_term')
   (RefineError : RefineErrorSig
    with type level_exp = TermType.level_exp
    with type param = TermType.param
    with type term = TermType.term
    with type bound_term = TermType.bound_term)
=
struct

   open RefineError
   open Term
   open TermType

   (*
    * Term type.
    *)

   type term = TermType.term

   (*
    * 4 subterms.
    *)

   let is_4_dep0_term opname t = match get_core t with
      Term { term_op = { op_name = opname'; op_params = [] };
             term_terms = [bt1; bt2; bt3; bt4]
           } when Opname.eq opname' opname ->
         bt1.bvars = [] && bt2.bvars = [] && bt3.bvars = [] && bt4.bvars = []
    | _ -> false

   let mk_4_dep0_term opname t1 t2 t3 t4 =
      { free_vars = VarsDelayed;
        core = Term
         { term_op = { op_name = opname; op_params = [] };
           term_terms = [ mk_simple_bterm t1; mk_simple_bterm t2;
                          mk_simple_bterm t3; mk_simple_bterm t4 ] } }

   let dest_4_dep0_term opname t = match dest_term t with
      { term_op = { op_name = opname'; op_params = [] };
        term_terms = [ bt1; bt2; bt3; bt4 ]
      } when Opname.eq opname' opname ->
         dest_simple_bterm bt1, dest_simple_bterm bt2,
         dest_simple_bterm bt3, dest_simple_bterm bt4
    | _ -> raise (RefineError ("dest_4_dep0_term",
                              TermMatchError(t, "bad arity")))

   let is_3_dep0_1_dep1_term opname t = match get_core t with
      Term { term_op  = { op_name = opname'; op_params = [] };
             term_terms = [ { bvars = [] }; { bvars = [] };
                            { bvars = [] }; { bvars = [_] } ]
           } -> Opname.eq opname' opname
    | _ -> false

   let mk_3_dep0_1_dep1_term opname t1 t2 t3 b4 t4 =
      { free_vars = VarsDelayed;
        core = Term
         { term_op = { op_name = opname; op_params = [] };
           term_terms = [ mk_simple_bterm t1;
                          mk_simple_bterm t2;
                          mk_simple_bterm t3;
                          { bvars = [b4]; bterm = t4 } ] } }

   let dest_3_dep0_1_dep1_term opname t = match dest_term t with
      { term_op = { op_name = opname'; op_params = [] };
        term_terms = [ { bvars = []; bterm = t1 };
                       { bvars = []; bterm = t2 };
                       { bvars = []; bterm = t3 };
                       { bvars = [v]; bterm = t4 } ]
      } when Opname.eq opname' opname ->
         t1, t2, t3, v, t4
    | _ -> raise (RefineError ("dest_3_dep0_1_dep1_term",
                              TermMatchError(t, "bad arity")))

   (*
    * 5 subterms.
    *)

   let is_4_dep0_1_dep1_term opname t = match get_core t with
      Term { term_op = { op_name = opname'; op_params = [] };
             term_terms = [ { bvars = [] }; { bvars = [] };
                            { bvars = [] }; { bvars = [] };
                            { bvars = [_] } ]
           } -> Opname.eq opname' opname
    | _ -> false

   let mk_4_dep0_1_dep1_term opname t1 t2 t3 t4 b5 t5 =
      { free_vars = VarsDelayed;
        core = Term
         { term_op = { op_name = opname; op_params = [] };
           term_terms = [ mk_simple_bterm t1;
                          mk_simple_bterm t2;
                          mk_simple_bterm t3;
                          mk_simple_bterm t4;
                          { bvars = [b5]; bterm = t5 } ] } }

   let dest_4_dep0_1_dep1_term opname t = match dest_term t with
      { term_op = { op_name = opname'; op_params = [] };
        term_terms = [ { bvars = []; bterm = t1 };
                       { bvars = []; bterm = t2 };
                       { bvars = []; bterm = t3 };
                       { bvars = []; bterm = t4 };
                       { bvars = [v]; bterm = t5 } ]
      } when Opname.eq opname' opname ->
         t1, t2, t3, t4, v, t5
    | _ -> raise (RefineError ("dest_4_dep0_1_dep1_term",
                               TermMatchError(t, "bad arity")))

   (*
    * 6 subterms.
    *)

   let is_5_dep0_1_dep1_term opname t = match get_core t with
      Term { term_op = { op_name = opname'; op_params = [] };
             term_terms = [ { bvars = [] }; { bvars = [] };
                            { bvars = [] }; { bvars = [] };
                            { bvars = [] }; { bvars = [_] } ]
           } -> Opname.eq opname' opname
    | _ -> false

   let mk_5_dep0_1_dep1_term opname t1 t2 t3 t4 t5 b6 t6 =
      { free_vars = VarsDelayed;
        core = Term
         { term_op = { op_name = opname; op_params = [] };
           term_terms = [ mk_simple_bterm t1;
                          mk_simple_bterm t2;
                          mk_simple_bterm t3;
                          mk_simple_bterm t4;
                          mk_simple_bterm t5;
                          { bvars = [b6]; bterm = t6 } ] } }

   let dest_5_dep0_1_dep1_term opname t = match dest_term t with
      { term_op = { op_name = opname'; op_params = [] };
        term_terms = [ { bvars = []; bterm = t1 };
                       { bvars = []; bterm = t2 };
                       { bvars = []; bterm = t3 };
                       { bvars = []; bterm = t4 };
                       { bvars = []; bterm = t5 };
                       { bvars = [v]; bterm = t6 } ]
      } when Opname.eq opname' opname ->
         t1, t2, t3, t4, t5, v, t6
    | _ -> raise (RefineError ("dest_5_dep0_1_dep1_term",
                               TermMatchError(t, "bad arity")))

end
