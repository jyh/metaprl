(*
 * This file defines the intermediate language for
 * the "MC" language.
 *
 * Here is the abstract syntax:
 *
 *   (* Atoms (functional values) *)
 *   a ::= i            (integers)
 *      |  v            (variables)
 *      |  a1 op a2     (binary operation)
 *
 *   (* Expressions *)
 *   e ::= let v = a in e               (LetAtom)
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

(*
 * Binary operators.
 *)
declare AddOp
declare SubOp
declare MulOp
declare DivOp

prec prec_mul
prec prec_add < prec_mul
prec prec_if < prec_add

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
declare LetSubscript{'a1; 'a2; v. 'e['v]}
declare SetSubscript{'a1; 'a2; 'a3; 'e}

declare LetApply{'f; 'a; v. 'e['v]}
declare Return{'a}

(************************************************************************
 * Display forms
 *)

(* Some convenient keywords *)
declare xlet
declare xin
dform xlet_df = bf["in"]
dform xin_df = bf["in"]

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
   " " xlet `" " slot{'v} `" = " slot{'a} xin 'e

dform exp_tail_call_df : TailCall{'f; 'a} =
   slot{'f} `"(" slot{'a} `")"

dform exp_if_df : parens :: "prec"[prec_if] :: except_mode[tex] :: If{'a; 'e1; 'e2} =
   szone pushm[0] pushm[3] `"if" `" " szone{'a} `" " `"then" hspace
   szone{'e1} popm hspace
   pushm[3] `"else" hspace szone{'e2} popm popm ezone

dform exp_subscript_df : LetSubscript{'a1; 'a2; v. 'e} =
   " " xlet `" " slot{'v} `" = " slot{'a1} `"[" slot{'a2} `"] " xin 'e

dform exp_set_subscript_df : SetSubscript{'a1; 'a2; 'a3; 'e} =
   slot{'a1} `"[" slot{'a2} `"] <- " slot{'a3} `";" 'e

dform exp_let_apply_df : LetApply{'f; 'a; v. 'e} =
   " " xlet `" " slot{'v} `" = " slot{'f} `"(" slot{'a} `") " xin 'e

dform exp_return_df : Return{'a} =
   bf["return"] `"(" slot{'a} `")"

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
