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
extends Base_theory

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

(*!
 * @begin[doc]
 * Values are numbers, functions, and pairs.
 * @end[doc]
 *)
declare ValInt[i:n]
declare ValFun{v. 'e['v]}
declare ValPair{'v1; 'v2}

(*!
 * @begin[doc]
 * @modsubsection{Atoms}
 *
 * Atoms are values: integers, variables, binary operations
 * on atoms, and functions.  In this phase, unnamed functions
 * are also atoms.
 * @end[doc]
 *)
declare AtomInt[i:n]
declare AtomBinop{'op; 'a1; 'a2}
declare AtomFun{x. 'e['x]}
declare AtomVar{'v}
declare AtomFunVar{'v}

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
 * let r = fix{r. record{
 *                   field["f"]{lambda{x. (r.g)(x)}};
 *                   field["g"]{lambda{x. (r.f)(x)}}}}
 * in
 *    r.f(1)
 *
 * An alternate representation is to use side-effects.  We have to deal with
 * state anyway, and this scheme seems to be a little simpler.  The idea is
 * to separate function declarations from definitions.  A declaration
 * FunDecl{f; ...} adds a default value for $f$ to the program state.
 * A definition FunDef{f; e; ...} assigns the new value $e$ for $f$.
 *
 * The semantics is like this:
 *    FunDecl{f. e}       ==    let f = ref None in e
 *    FunDef{f; e1; e2}   ==    f := Some e1; e2
 *
 * However, this approach seems easier, so we'll pursue it for now.
 * @end[doc]
 *)
declare FunDecl{f. 'e['f]}
declare FunDef{'f; 'e1; 'e2}

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
prec prec_if
prec prec_fun
prec prec_let
prec prec_compilable

prec prec_mul < prec_var
prec prec_add < prec_mul
prec prec_let < prec_add
prec prec_if < prec_let
prec prec_fun < prec_if
prec prec_compilable < prec_let

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
   `"#" slot[i:n]

dform atom_var_df : parens :: "prec"[prec_var] :: AtomVar{'v} =
   Nuprl_font!downarrow slot{'v}

dform atom_fun_var_df : parens :: "prec"[prec_var] :: AtomFunVar{'v} =
   Nuprl_font!uparrow slot{'v}

dform atom_binop_add_df : parens :: "prec"[prec_add] :: AtomBinop{AddOp; 'e1; 'e2} =
   slot["lt"]{'e1} " " `"+ " slot["le"]{'e2}

dform atom_binop_sub_df : parens :: "prec"[prec_add] :: AtomBinop{SubOp; 'e1; 'e2} =
   slot["lt"]{'e1} " " `"- " slot["le"]{'e2}

dform atom_binop_mul_df : parens :: "prec"[prec_mul] :: AtomBinop{MulOp; 'e1; 'e2} =
   slot["lt"]{'e1} " " `"* " slot["le"]{'e2}

dform atom_binop_div_df : parens :: "prec"[prec_mul] :: AtomBinop{DivOp; 'e1; 'e2} =
   slot["lt"]{'e1} " " `"/ " slot["le"]{'e2}

dform atom_fun_df : parens :: "prec"[prec_fun] :: AtomFun{x. 'e} =
   pushm[3] Nuprl_font!lambda Nuprl_font!suba slot{'x} `"." slot{'e} popm

(* Recursive functions *)
dform fun_decl_df : parens :: "prec"[prec_let] :: FunDecl{f. 'e} =
   `"declare " slot{'f} `" " xin hspace slot["lt"]{'e}

dform fun_def_df : parens :: "prec"[prec_let] :: FunDef{'f; 'e1; 'e2} =
   `"define " slot{'f} `" = " slot{'e1} `" " xin hspace slot["lt"]{'e2}

(* Expressions *)
dform exp_let_atom_df : parens :: "prec"[prec_let] :: LetAtom{'a; v. 'e} =
   xlet `" " slot{'v} `" = " slot{'a} `" " xin hspace slot["lt"]{'e}

dform exp_tailcall2_df : parens :: "prec"[prec_let] :: TailCall{'f; 'a} =
   `"tailcall " slot{'f} `"(" slot{'a} `")"

dform exp_tailcall3_df : parens :: "prec"[prec_let] :: TailCall{'f; 'a1; 'a2} =
   `"tailcall " slot{'f} `"(" slot{'a1} `", " slot{'a2} `")"

dform exp_if_df : parens :: "prec"[prec_if] :: except_mode[tex] :: If{'a; 'e1; 'e2} =
   szone pushm[0] pushm[3] `"if" `" " szone{'a} `" " `"then" hspace
   szone{'e1} popm hspace
   pushm[3] `"else" hspace szone{'e2} popm popm ezone

dform exp_let_pair_df : parens :: "prec"[prec_let] :: LetPair{'a1; 'a2; v. 'e} =
   xlet `" " slot{'v} `" = " ValPair{'a1; 'a2} `" " xin hspace slot["lt"]{'e}

dform exp_subscript_df : parens :: "prec"[prec_let] :: LetSubscript{'a1; 'a2; v. 'e} =
   xlet `" " slot{'v} `" = " slot{'a1} `"[" slot{'a2} `"] " xin hspace slot["lt"]{'e}

dform exp_set_subscript_df : parens :: "prec"[prec_let] :: SetSubscript{'a1; 'a2; 'a3; 'e} =
   slot{'a1} `"[" slot{'a2} `"] <- " slot{'a3} `";" hspace slot["lt"]{'e}

dform exp_let_apply_df : parens :: "prec"[prec_let] :: LetApply{'f; 'a; v. 'e} =
   xlet `" apply " slot{'v} `" = " slot{'f} `"(" slot{'a} `") " xin hspace slot["lt"]{'e}

dform exp_let_closure_df : parens :: "prec"[prec_let] :: LetClosure{'f; 'a; v. 'e} =
   xlet `" closure " slot{'v} `" = " slot{'f} `"(" slot{'a} `") " xin hspace slot["lt"]{'e}

dform exp_return_df : Return{'a} =
   bf["return"] `"(" slot{'a} `")"

(*
 * Declarations and definitions.
 *)
dform exp_df : exp = bf["exp"]

dform def_df : def{'v; 'e} =
   slot{'v} `" = " slot{'e}

dform compilable_df : "prec"[prec_compilable] :: compilable{'e} =
   szone Nuprl_font!longrightarrow pushm[0] slot{'e} popm ezone

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
