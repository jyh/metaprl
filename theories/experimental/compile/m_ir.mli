(*
 * This file defines the intermediate language for
 * the "MC" language.
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

extends Base_theory

(*
 * Display form precendences.
 *)
prec prec_mul
prec prec_add
prec prec_if
prec prec_fun

(*
 * Binary operators.
 *)
declare AddOp
declare SubOp
declare MulOp
declare DivOp

(*
 * Values are numbers, functions, and pairs.
 *)
declare ValInt[i:n]
declare ValFun{v. 'e['v]}
declare ValPair{'v1; 'v2}

(*
 * Atoms.
 * We use the built-in representation of variables (for now).
 *)
declare AtomInt[i:n]
declare AtomBinop{'op; 'a1; 'a2}

(*
 * Expressions.
 *)
declare LetAtom{'a; v. 'e['v]}
declare LetFun{v. 'e1['v]; f. 'e2['f]}
declare TailCall{'f; 'a}
declare If{'a; 'e1; 'e2}
declare LetPair{'a1; 'a2; v. 'e['v]}
declare LetSubscript{'a1; 'a2; v. 'e['v]}
declare SetSubscript{'a1; 'a2; 'a3; 'e}

declare LetApply{'f; 'a; v. 'e['v]}
declare Return{'a}

(*
 * Programs are represented as sequents:
 *    declarations, definitions >- exp
 *
 * For now the language is untyped, so each declaration
 * has the form v:exp.  A definition is an equality judegment.
 *)
declare exp
declare def{'v; 'e}

(*
 * Sequent tag for m programs.
 *)
declare m

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
