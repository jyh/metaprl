(*
 * This file defines the intermediate language for
 * the M language.
 *
 * Here is the abstract syntax:
 *
 *   (* Values *)
 *   v ::= i            (integers)
 *      |  v            (variables)
 *      |  fun v -> e   (functions)
 *      |  (v1, v2)     (pairs)
 *
 *   (* Atoms (functional expressions) *)
 *   a ::= i            (integers)
 *      |  v            (variables)
 *      |  a1 op a2     (binary operations)
 *
 *   (* Expressions *)
 *   e ::= let v = a in e               (LetAtom)
 *      |  f(a)                         (TailCall)
 *      |  if a then e1 else e2         (Conditional)
 *      |  let v = (a1, a2) in e        (Allocation)
 *      |  let v = a1[a2] in e          (Subscripting)
 *      |  a1[a2] <- a3; e              (Assignment)
 *
 *         (* These are eliminated during CPS *)
 *      |  let v = f(a) in e            (Function application)
 *      |  return a
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2003 Jason Hickey, Caltech
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
 * Author: Jason Hickey
 * @email{jyh@cs.caltech.edu}
 * @end[license]
 *)
extends M_util

open Opname
open Refiner.Refiner.Term

(*
 * Display form precendences.
 *)
prec prec_var
prec prec_mul
prec prec_add
prec prec_rel
prec prec_if
prec prec_fun
prec prec_let
prec prec_comma
prec prec_compilable

(*
 * Binary operators.
 *)
declare AddOp
declare SubOp
declare MulOp
declare DivOp

declare LtOp
declare LeOp
declare EqOp
declare NeqOp
declare GeOp
declare GtOp

(*
 * Atoms.
 * We use the built-in representation of variables (for now).
 *)
declare AtomFalse
declare AtomTrue
declare AtomInt[i:n]
declare AtomBinop{'op; 'a1; 'a2}
declare AtomRelop{'op; 'a1; 'a2}
declare AtomFun{x. 'e['x]}
declare AtomVar{'v}
declare AtomFunVar{'R; 'v}

(*
 * Expressions.
 *)
declare LetAtom{'a; v. 'e['v]}
declare If{'a; 'e1; 'e2}

declare ArgNil
declare ArgCons{'a; 'rest}
declare TailCall{'f; 'args}

declare Length[i:n]
declare AllocTupleNil
declare AllocTupleCons{'a; 'rest}
declare LetTuple{'length; 'tuple; v. 'e['v]}
declare LetSubscript{'a1; 'a2; v. 'e['v]}
declare SetSubscript{'a1; 'a2; 'a3; 'e}

declare Reserve[words:n]{'e}
declare Reserve[words:n]{'args; 'e}
declare ReserveCons{'a; 'rest}
declare ReserveNil

declare LetApply{'f; 'a; v. 'e['v]}
declare LetClosure{'a1; 'a2; f. 'e['f]}
declare Return{'a}

(*
 * Recursive functions.
 *)
declare LetRec{R1. 'e1['R1]; R2. 'e2['R2]}
declare Fields{'fields}
declare Label[tag:t]
declare FunDef{'label; 'exp; 'rest}
declare EndDef
declare LetFun{'R; 'label; f. 'e['f]}

(*
 * Include a term representing initialization code.
 *)
declare Initialize{'e}

(*
 * Programs are represented as sequents:
 *    declarations, definitions >- exp
 *
 * For now the language is untyped, so each declaration
 * has the form v:exp.  A definition is an equality judegment.
 *)
declare exp
declare def{'v; 'e}
declare compilable{'e}

(*
 * Sequent tag for M programs.
 *)
declare sequent_arg

(*
 * Term constructors.
 *)
val fundef_term : term
val fundef_opname : opname
val is_fundef_term : term -> bool
val dest_fundef_term : term -> term * term * term
val mk_fundef_term : term -> term -> term -> term

val letrec_term : term
val letrec_opname : opname
val is_letrec_term : term -> bool
val dest_letrec_term : term -> string * term * string * term
val mk_letrec_term : string -> term -> string -> term -> term

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
