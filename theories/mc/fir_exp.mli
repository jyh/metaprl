(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Define and implement the basic expression forms in the FIR.
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

include Base_theory
include Itt_theory
include Fir_state
include Fir_int_set
include Fir_ty

open Tactic_type.Conversionals

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Identity (polymorphic). *)
declare idOp

(*
 * Pointer equality.
 * Binary ops that evaluate as integer (in)equality.
 *)
declare eqEqOp
declare neqEqOp

(*
 * Subscript operators.
 * I have no clue how these are supposed to work/evaluate.
 * Consequently, I just ignore them right now.
 *)
declare blockPolySub
declare blockRawIntSub{ 'precision; 'sign }
declare blockFloatSub{ 'precision }
declare rawRawIntSub{ 'precision; 'sign }
declare rawFloatSub{ 'precision }
declare rawDataSub
declare rawFunctionSub

(*
 * Allocation operators.
 * I'm unsure about allocMalloc and allocUnion, so I haven't dealt
 * with them yet.
 *)
declare allocTuple{ 'ty; 'atom_list }
declare allocArray{ 'ty; 'atom_list }
declare allocUnion{ 'ty; 'ty_var; 'num; 'atom_list }
declare allocMalloc{ 'atom }

(*
 * Normal values.
 * atomInt evaluates to 'int (a number).
 * atomEnum evalutes to 'num (a number).
 * atomVar evaluates to 'var (a free variable).
 *)
declare atomInt{ 'int }
declare atomEnum{ 'bound; 'num }
declare atomRawInt{ 'num }
declare atomConst{ 'ty; 'ty_var; 'num }
declare atomVar{ 'var }

(*
 * Expressions.
 *)

(*
 * Primitive operations.
 * We bind 'v to the value of ('op args).
 *)
declare unop_exp{ 'op; 'a1 }
declare binop_exp{ 'op; 'a1; 'a2 }
declare letUnop{ 'op; 'ty; 'a1; v. 'exp['v] }
declare letBinop{ 'op; 'ty; 'a1; 'a2; v. 'exp['v] }

(*
 * Function application.
 * letExt is treated as a no-op; it evaluates to 'exp[it].
 *    This is on the assumption that it has a side-effect that we dont'
 *    need to worry about here.  If that's not true... uh-oh.
 * tailCall's aren't emitted by the compiler. I declare the term
 *    here for completeness.
 *)
declare letExt{ 'ty; 'string; 'ty_of_str; 'atom_list; v. 'exp['v] }
declare tailCall{ 'var; 'atom_list }

(*
 * Control.
 * A matchCase consists of an int_set an expression.
 * A match statement has a 'key (a number/int or block), and a list
 * of matchCases.
 *)
declare matchCase{ 'set; 'exp }
declare "match"{ 'key; 'cases }

(* Allocation. *)
declare letAlloc{ 'alloc_op; v. 'exp['v] }

(*
 * Subscripting.
 * In setSubscript, we bind the updated value to v in 'exp.
 * For evaluation purposes, 'subop is completely ignored.
 *)
declare letSubscript{ 'subop; 'ty; 'var; 'index; v. 'exp['v] }
declare setSubscript{ 'subop; 'ty; 'var; 'index; 'new_val; v. 'exp['v] }
declare memcpy{ 'subop; 'var1; 'atom1; 'var2; 'atom2; 'len; 'exp }

(*
 * Misc.
 * Used in making output from the mc compiler more manageable.
 * They indicate that compiler "didn't know" how to print out
 * a given term properly.
 *)

declare unknownFun
declare unknownSet
declare unknownAtom
declare unknownAlloc

(*************************************************************************
 * Rewrites.
 *************************************************************************)

topval reduce_idOp : conv
topval reduce_eqEqOp : conv
topval reduce_neqEqOp : conv
topval reduce_atomInt : conv
topval reduce_atomEnum : conv
topval reduce_atomRawInt : conv
topval reduce_atomVar : conv
topval reduce_letUnop : conv
topval reduce_letBinop : conv
topval reduce_letExt : conv
topval reduce_match_int : conv
topval reduce_match_block : conv
topval reduce_allocTuple : conv
topval reduce_allocArray : conv
topval reduce_letSubscript : conv
topval reduce_setSubscript : conv
