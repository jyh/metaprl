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
 *      |  a1 op a2     (binary operation)
 *
 *   (* Expressions *)
 *   e ::= let v = a in e               (LetAtom)
 *      |  let f(v) = e1 in e2          (LetFun)
 *      |  f(a)                         (TailCall)
 *      |  if a then e1 else e2         (Conditional)
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
declare TailCall{'f; 'a}
declare If{'a; 'e1; 'e2}
declare LetPair{'a1; 'a2; v. 'e['v]}
declare LetSubscript{'a1; 'a2; v. 'e['v]}
declare SetSubscript{'a1; 'a2; 'a3; 'e}

(*
 * LetApply, Return are eliminated during CPS conversion.
 * LetFun is eliminated during closure conversion.
 *)
declare LetFun{v. 'e1['v]; f. 'e2['f]}
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

(************************************************************************
 * Display forms
 *)

(*
 * Precedences.
 *)
prec prec_mul
prec prec_add
prec prec_if
prec prec_fun

prec prec_add < prec_mul
prec prec_if < prec_add
prec prec_fun < prec_if

(* Some convenient keywords *)
declare xlet
declare xin
dform xlet_df : xlet = bf["let"]
dform xin_df : xin = bf["in"]

(* Values *)
dform val_int_df : ValInt[i:n] =
   slot[i:n]

dform val_fun_df : parens :: except_mode [src] :: "prec"[prec_fun] :: ValFun{v. 'b} =
   Nuprl_font!lambda slot{'v} `"." slot{'b}

dform val_pair_df : except_mode[src] :: ValPair{'a; 'b} =
   pushm[0] `"(" slot{'a}`"," slot{'b} `")" popm

(* Atoms *)
dform atom_int_df : AtomInt[i:n] =
   slot[i:n]

dform atom_binop_add_df : parens :: "prec"[prec_add] :: AtomBinop{AddOp; 'e1; 'e2} =
   slot["lt"]{'e1} " " `"+ " slot["le"]{'e2}

dform atom_binop_sub_df : parens :: "prec"[prec_add] :: AtomBinop{SubOp; 'e1; 'e2} =
   slot["lt"]{'e1} " " `"- " slot["le"]{'e2}

dform atom_binop_mul_df : parens :: "prec"[prec_mul] :: AtomBinop{MulOp; 'e1; 'e2} =
   slot["lt"]{'e1} " " `"* " slot["le"]{'e2}

dform atom_binop_div_df : parens :: "prec"[prec_mul] :: AtomBinop{DivOp; 'e1; 'e2} =
   slot["lt"]{'e1} " " `"/ " slot["le"]{'e2}

(* Expressions *)
dform exp_let_atom_df : LetAtom{'a; v. 'e} =
   xlet `" " slot{'v} `" = " slot{'a} `" " xin hspace 'e

dform exp_let_fun_df : LetFun{v. 'e1; f. 'e2} =
   szone pushm[0] pushm[3] xlet `" " slot{'f} `"(" slot{'v} `") =" hspace slot{'e1} popm hspace xin popm ezone
   hspace 'e2

dform exp_tail_call_df : TailCall{'f; 'a} =
   slot{'f} `"(" slot{'a} `")"

dform exp_if_df : parens :: "prec"[prec_if] :: except_mode[tex] :: If{'a; 'e1; 'e2} =
   szone pushm[0] pushm[3] `"if" `" " szone{'a} `" " `"then" hspace
   szone{'e1} popm hspace
   pushm[3] `"else" hspace szone{'e2} popm popm ezone

dform exp_let_pair_df : LetPair{'a1; 'a2; v. 'e} =
   xlet `" " slot{'v} `" = " ValPair{'a1; 'a2} `" " xin hspace 'e

dform exp_subscript_df : LetSubscript{'a1; 'a2; v. 'e} =
   xlet `" " slot{'v} `" = " slot{'a1} `"[" slot{'a2} `"] " xin hspace 'e

dform exp_set_subscript_df : SetSubscript{'a1; 'a2; 'a3; 'e} =
   slot{'a1} `"[" slot{'a2} `"] <- " slot{'a3} `";" hspace 'e

dform exp_let_apply_df : LetApply{'f; 'a; v. 'e} =
   xlet `" " slot{'v} `" = " slot{'f} `"(" slot{'a} `") " xin hspace 'e

dform exp_return_df : Return{'a} =
   bf["return"] `"(" slot{'a} `")"

(*
 * Declarations and definitions.
 *)
dform exp_df : exp = bf["exp"]

dform def_df : def{'v; 'e} =
   slot{'v} `" = " slot{'e}

(*
 * Sequent tag for the M language.
 *)
declare m

dform m_df : m = bf["m"]

(*
 * Just for testing the ext: quotation.
 *)
let tprog = <:ext<let t = 1 in t+1>>

(************************************************************************
 * Just for testing.
 *)
interactive test_prog 'H :
   sequent [m] { 'H >- <:ext<
                        let v1 = 1 in
                        let v2 = 2+v1 in
                        let f (v3) =
                           let v4 = (v2, v3) in
                           let v5 = v4[0] in
                              v5
                        in
                           f(17)>>}

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
