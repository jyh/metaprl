(*!
 * @begin[doc]
 * This file defines the intermediate language for
 * the @emph{M} language.
 *
 * Here is the abstract syntax:
 *
 * @begin[verbatim]
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
 *      |  fun x -> e   (unnamed functions)
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
 * @end[verbatim]
 *
 * A program is a set of function definitions and an program
 * expressed in a sequent.  Each function must be declared, and
 * defined separately.
 * @end[doc]
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

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
extends M_util
(*! @docoff *)

open Refiner.Refiner.Term
open Refiner.Refiner.TermOp

(*!
 * @begin[doc]
 * @terms
 * Binary operators.
 * @end[doc]
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

(*!
 * @begin[doc]
 * @modsubsection{Atoms}
 *
 * Atoms are values: integers, variables, binary operations
 * on atoms, and functions.  For now, variable are represented
 * as variables; we don't need separate atoms.
 *
 * AtomFun is a lambda-abstraction, and AtomFunVar is the projection
 * of a function from a recursive function definition (defined below).
 * @end[doc]
 *)
declare AtomFalse
declare AtomTrue
declare AtomInt[i:n]
declare AtomBinop{'op; 'a1; 'a2}
declare AtomFun{x. 'e['x]}
declare AtomFunVar{'R; 'v}

(*!
 * @begin[doc]
 * @modsubsection{Expressions}
 *
 * There are several simple kinds of expressions.
 * @end[doc]
 *)
declare LetAtom{'a; v. 'e['v]}
declare TailCall{'f; 'a}
declare TailCall{'f; 'a1; 'a2}
declare If{'a; 'e1; 'e2}
declare LetPair{'a1; 'a2; v. 'e['v]}
declare LetSubscript{'a1; 'a2; v. 'e['v]}
declare SetSubscript{'a1; 'a2; 'a3; 'e}

(*!
 * @begin[doc]
 * LetApply, Return are eliminated during CPS conversion.
 * LetClosure is like LetApply, but it is a partial application.
 * @end[doc]
 *)
declare LetApply{'f; 'a; v. 'e['v]}
declare LetClosure{'a1; 'a2; f. 'e['f]}
declare Return{'a}

(*!
 * This is the most problematic part of the description so far.
 * This documentation discusses two possible approaches.
 *
 * @begin[doc]
 * @modsubsection{Recursive values}
 *
 * We need some way to represent mutually recursive functions.
 * The normal way to do this is to define a single recursive function,
 * and use a switch to split the different parts.  The method to do this
 * would use a record.  For example, suppose we define two mutually
 * recursive functions $f$ and $g$:
 *
 * let r2 = fix{r1. record{
 *                   field["f"]{lambda{x. (r1.g)(x)}};
 *                   field["g"]{lambda{x. (r1.f)(x)}}}}
 * in
 *    r2.f(1)
 * @end[doc]
 *)
declare LetRec{R1. 'e1['R1]; R2. 'e2['R2]}

(*!
 * @begin[doc]
 * Records have a set of tagged fields.
 * We require that allthe fields be functions.
 *
 * The record construction is recursive.  The Label term is used for
 * field tags; the FunDef defines a new field in the record; and the
 * EndDef term terminates the record fields.
 * @end[doc]
 *)
declare Label[tag:t]
declare FunDef{'label; 'exp; 'rest}
declare EndDef

(*!
 * @begin[doc]
 * To simplify the presentation, we usually project the record fields
 * before each of the field branches so that we can treat functions
 * as if they were variables.
 * @end[doc]
 *)
declare LetFun{'R; 'label; f. 'e['f]}

(*!
 * @begin[doc]
 * @modsubsection{Program sequent representation}
 *
 * Programs are represented as sequents:
 *    declarations, definitions >- exp
 *
 * For now the language is untyped, so each declaration
 * has the form v:exp.  A definition is an equality judegment.
 * @end[doc]
 *)
declare exp
declare def{'v; 'e}
declare compilable{'e}

(************************************************************************
 * Display forms
 *)

(*
 * Precedences.
 *)
prec prec_var
prec prec_mul
prec prec_add
prec prec_rel
prec prec_if
prec prec_fun
prec prec_let
prec prec_compilable

prec prec_mul < prec_var
prec prec_add < prec_mul
prec prec_rel < prec_add
prec prec_let < prec_rel
prec prec_if < prec_let
prec prec_fun < prec_if
prec prec_compilable < prec_let

(* Some convenient keywords *)
declare xlet
declare xin
dform xlet_df : xlet = bf["let"]
dform xin_df : xin = bf["in"]

(* Atoms *)
dform atom_false_df : AtomFalse =
   `"false"

dform atom_false_df : AtomTrue =
   `"true"

dform atom_int_df : AtomInt[i:n] =
   `"#" slot[i:n]

dform atom_fun_var_df : parens :: "prec"[prec_var] :: AtomFunVar{'R; 'v} =
   slot{'R} `"." slot{'v}

dform atom_binop_add_df : parens :: "prec"[prec_add] :: AtomBinop{AddOp; 'e1; 'e2} =
   slot["lt"]{'e1} " " `"+ " slot["le"]{'e2}

dform atom_binop_sub_df : parens :: "prec"[prec_add] :: AtomBinop{SubOp; 'e1; 'e2} =
   slot["lt"]{'e1} " " `"- " slot["le"]{'e2}

dform atom_binop_mul_df : parens :: "prec"[prec_mul] :: AtomBinop{MulOp; 'e1; 'e2} =
   slot["lt"]{'e1} " " `"* " slot["le"]{'e2}

dform atom_binop_div_df : parens :: "prec"[prec_mul] :: AtomBinop{DivOp; 'e1; 'e2} =
   slot["lt"]{'e1} " " `"/ " slot["le"]{'e2}

dform atom_binop_lt_df : parens :: "prec"[prec_rel] :: AtomBinop{LtOp; 'e1; 'e2} =
   slot["lt"]{'e1} " " `"< " slot["le"]{'e2}

dform atom_binop_le_df : parens :: "prec"[prec_rel] :: AtomBinop{LeOp; 'e1; 'e2} =
   slot["lt"]{'e1} " " Nuprl_font!le `" " slot["le"]{'e2}

dform atom_binop_gt_df : parens :: "prec"[prec_rel] :: AtomBinop{GtOp; 'e1; 'e2} =
   slot["lt"]{'e1} " " `"> " slot["le"]{'e2}

dform atom_binop_ge_df : parens :: "prec"[prec_rel] :: AtomBinop{GeOp; 'e1; 'e2} =
   slot["lt"]{'e1} " " Nuprl_font!ge `" " slot["le"]{'e2}

dform atom_binop_eq_df : parens :: "prec"[prec_rel] :: AtomBinop{EqOp; 'e1; 'e2} =
   slot["lt"]{'e1} " " `"= " slot["le"]{'e2}

dform atom_binop_neq_df : parens :: "prec"[prec_rel] :: AtomBinop{NeqOp; 'e1; 'e2} =
   slot["lt"]{'e1} " " Nuprl_font!neq `" " slot["le"]{'e2}

dform atom_fun_df : parens :: "prec"[prec_fun] :: AtomFun{x. 'e} =
   szone pushm[3] Nuprl_font!lambda Nuprl_font!suba slot{'x} `"." hspace slot{'e} popm ezone

(* Expressions *)
dform exp_let_atom_df : parens :: "prec"[prec_let] :: LetAtom{'a; v. 'e} =
   xlet `" " slot{'v} bf[" = "] slot{'a} `" " xin hspace slot["lt"]{'e}

dform exp_tailcall2_df : parens :: "prec"[prec_let] :: TailCall{'f; 'a} =
   bf["tailcall "] slot{'f} `"(" slot{'a} `")"

dform exp_tailcall3_df : parens :: "prec"[prec_let] :: TailCall{'f; 'a1; 'a2} =
   bf["tailcall "] slot{'f} `"(" slot{'a1} `", " slot{'a2} `")"

dform exp_if_df : parens :: "prec"[prec_if] :: except_mode[tex] :: If{'a; 'e1; 'e2} =
   szone pushm[0] pushm[3] bf["if"] `" " slot{'a} `" " bf["then"] hspace
   slot{'e1} popm hspace
   pushm[3] bf["else"] hspace slot{'e2} popm popm ezone

dform exp_let_pair_df : parens :: "prec"[prec_let] :: LetPair{'a1; 'a2; v. 'e} =
   xlet `" " slot{'v} bf[" = "] `"(" 'a1 `"," 'a2 `") " xin hspace slot["lt"]{'e}

dform exp_subscript_df : parens :: "prec"[prec_let] :: LetSubscript{'a1; 'a2; v. 'e} =
   xlet `" " slot{'v} bf[" = "] slot{'a1} `"[" slot{'a2} `"] " xin hspace slot["lt"]{'e}

dform exp_set_subscript_df : parens :: "prec"[prec_let] :: SetSubscript{'a1; 'a2; 'a3; 'e} =
   slot{'a1} `"[" slot{'a2} `"] <- " slot{'a3} `";" hspace slot["lt"]{'e}

dform exp_let_apply_df : parens :: "prec"[prec_let] :: LetApply{'f; 'a; v. 'e} =
   xlet bf[" apply "] slot{'v} bf[" = "] slot{'f} `"(" slot{'a} `") " xin hspace slot["lt"]{'e}

dform exp_let_closure_df : parens :: "prec"[prec_let] :: LetClosure{'f; 'a; v. 'e} =
   xlet bf[" closure "] slot{'v} bf[" = "] slot{'f} `"(" slot{'a} `") " xin hspace slot["lt"]{'e}

dform exp_return_df : Return{'a} =
   bf["return"] `"(" slot{'a} `")"

(*
 * Recursive functions.
 *)
dform let_rec_df : parens :: "prec"[prec_let] :: LetRec{R1. 'e1; R2. 'e2} =
   szone pushm[3] xlet bf[" rec "] slot{'R1} `"." 'e1 popm ezone hspace slot{'R2} `"." xin hspace slot["lt"]{'e2}

dform fun_def_df : parens :: "prec"[prec_let] :: FunDef{'label; 'e; 'rest} =
   hspace szone pushm[3] bf["fun "] slot{'label} `" =" hspace slot{'e} popm ezone 'rest

dform end_def_df : EndDef =
   `""

dform label_df : Label[s:t] =
   slot[s:t]

dform let_fun_def : parens :: "prec"[prec_let] :: LetFun{'R; 'label; f. 'e} =
   xlet bf[" fun "] slot{'f} `" = " slot{'R} `"." slot{'label} `" " xin hspace slot["lt"]{'e}

(*
 * Declarations and definitions.
 *)
dform exp_df : exp = bf["exp"]

dform def_df : def{'v; 'e} =
   slot{'v} bf[" = "] slot{'e}

dform compilable_df : "prec"[prec_compilable] :: compilable{'e} =
   szone pushm[0] pushm[3] bf["compilable"] hspace slot{'e} popm hspace bf["end"] popm ezone

(*
 * Sequent tag for the M language.
 *)
declare m

dform m_df : m = bf["m"]

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
