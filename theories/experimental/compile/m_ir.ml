doc <:doc<
   @spelling{CPS}
   @begin[doc]
   @module[M_ir]

   This module defines the intermediate language for
   the @emph{M} language. Here is the abstract syntax:

   @begin[verbatim]
     (* Values *)
     v ::= i            (integers)
        |  b            (booleans)
        |  v            (variables)
        |  fun v -> e   (functions)
        |  (v1, v2)     (pairs)

     (* Atoms (functional expressions) *)
     a ::= i            (integers)
        |  b            (booleans)
        |  v            (variables)
        |  a1 op a2     (binary operation)
        |  fun x -> e   (unnamed functions)

     (* Expressions *)
     e ::= let v = a in e           (LetAtom)
        |  f(a)                     (TailCall)
        |  if a then e1 else e2     (Conditional)
        |  let v = a1.[a2] in e     (Subscripting)
        |  a1.[a2] <- a3; e         (Assignment)

           (* These are eliminated during CPS *)
        |  let v = f(a) in e        (Function application)
        |  return a
   @end[verbatim]

   A program is a set of function definitions and an program
   expressed in a sequent.  Each function must be declared, and
   defined separately.
   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   Copyright (C) 2003 Jason Hickey, Caltech

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

   Author: Jason Hickey
   @email{jyh@cs.caltech.edu}
   @end[license]
>>

doc <:doc<
   @begin[doc]
   @parents

     Modules in @MetaPRL are organized in a theory hierarchy.  Each theory
     module extends its parent theories.  In this case, the @tt[M_ir] module
     extends base theories that define generic proof automation.
   @end[doc]
>>
extends Base_theory
doc <:doc< @docoff >>

open Refiner.Refiner.Term
open Refiner.Refiner.TermOp

doc <:doc<
   @begin[doc]
   @terms

   The IR defines several binary operators for arithmetic and Boolean operations.
   @end[doc]
>>
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

doc <:doc<
   @begin[doc]
   @modsubsection{Atoms}

   Atoms represent expressions that are values: integers, variables, binary operations
   on atoms, and functions.

   @tt[AtomFun] is a lambda-abstraction, and @tt[AtomFunVar] is the projection
   of a function from a recursive function definition (defined below).
   @end[doc]
>>
declare AtomFalse
declare AtomTrue
declare AtomInt[i:n]
declare AtomBinop{'op; 'a1; 'a2}
declare AtomRelop{'op; 'a1; 'a2}
declare AtomFun{x. 'e['x]}
declare AtomVar{'v}
declare AtomFunVar{'R; 'v}

doc <:doc<
   @begin[doc]
   @modsubsection{Expressions}

     General expressions are not values.  There are several simple kinds of expressions,
     for conditionals, allocation, function calls, and array operations.
   @end[doc]
>>
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

doc <:doc<
   @begin[doc]
     Reserve statements are used to specify how much memory may be allocated
     in a function body.  The M_reserve module defines an explicit phase that
     calculates memory usage and adds reserve statements.  In the << Reserve[words:n]{'args; 'e} >>
     expressions, the @it[words] constant defines how much memory is to be reserved; the @it[args]
     defines the set of live variables (this information is used by the garbage collector), and @it[e]
     is the nested expression that performs the allocation.
   @end[doc]
>>
declare Reserve[words:n]{'e}
declare Reserve[words:n]{'args; 'e}
declare ReserveCons{'a; 'rest}
declare ReserveNil

doc <:doc<
     @begin[doc]
   @tt[LetApply], @tt[Return] are eliminated during CPS conversion.
   @tt[LetClosure] is like @tt[LetApply], but it represents a partial application.
   @end[doc]
>>
declare LetApply{'f; 'a; v. 'e['v]}
declare LetClosure{'a1; 'a2; f. 'e['f]}
declare Return{'a}

doc <:doc<
   This is the most problematic part of the description so far.
   This documentation discusses two possible approaches.

   @begin[doc]
   @modsubsection{Recursive values}

     We need some way to represent mutually recursive functions.
     The normal way to do this is to define a single recursive function,
     and use a switch to split the different parts.  For this purpose, we
     define a fixpoint over a record of functions.
     For example, suppose we define two mutually
     recursive functions $f$ and $g$:

   @begin[verbatim]
   let r2 = fix{r1. record{
                     field["f"]{lambda{x. (r1.g)(x)}};
                     field["g"]{lambda{x. (r1.f)(x)}}}}
   in
      r2.f(1)
   @end[verbatim]
   @end[doc]
>>
declare LetRec{R1. 'e1['R1]; R2. 'e2['R2]}

doc <:doc<
     @begin[doc]
     The following terms define the set of tagged fields used in the record definition.
     We require that all the fields be functions.

     The record construction is recursive.  The @tt[Label] term is used for
     field tags; the @tt[FunDef] defines a new field in the record; and the
     @tt[EndDef] term terminates the record fields.
   @end[doc]
>>
declare Fields{'fields}
declare Label[tag:s]
declare FunDef{'label; 'exp; 'rest}
declare EndDef

doc <:doc<
   @begin[doc]
   To simplify the presentation, we usually project the record fields
   before each of the field branches so that we can treat functions
   as if they were variables.
   @end[doc]
>>
declare LetFun{'R; 'label; f. 'e['f]}

doc <:doc< @doc{Include a term representing initialization code.} >>

declare Initialize{'e}

doc <:doc<
   @begin[doc]
   @modsubsection{Program sequent representation}

   Programs are represented as sequents:
      <<sequent{ <declarations>; <definitions> >- exp }>>

   For now the language is untyped, so each declaration
   has the form @tt["v = exp"].  A definition is an equality judgment.
   @end[doc]
>>
declare exp
declare def{'v; 'e}
declare compilable{'e}

doc <:doc< @docoff >>

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
prec prec_comma
prec prec_compilable

prec prec_mul < prec_var
prec prec_add < prec_mul
prec prec_rel < prec_add
prec prec_let < prec_rel
prec prec_if < prec_let
prec prec_fun < prec_if
prec prec_comma < prec_fun
prec prec_compilable < prec_comma

doc <:doc< Some convenient keywords (used in only display forms and do not have a formal meaning). >>
declare xlet
declare xin
doc <:doc< @docoff >>

dform xlet_df : xlet = bf["let"]
dform xin_df : xin = bf["in"]

(* Atoms *)
dform atom_false_df : AtomFalse =
   `"false"

dform atom_false_df : AtomTrue =
   `"true"

dform atom_int_df : AtomInt[i:n] =
   `"#" slot[i:n]

dform atom_var_df : AtomVar{'v} =
   Nuprl_font!downarrow slot{'v}

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

dform atom_binop_lt_df : parens :: "prec"[prec_rel] :: AtomRelop{LtOp; 'e1; 'e2} =
   slot["lt"]{'e1} " " `"< " slot["le"]{'e2}

dform atom_binop_le_df : parens :: "prec"[prec_rel] :: AtomRelop{LeOp; 'e1; 'e2} =
   slot["lt"]{'e1} " " Nuprl_font!le `" " slot["le"]{'e2}

dform atom_binop_gt_df : parens :: "prec"[prec_rel] :: AtomRelop{GtOp; 'e1; 'e2} =
   slot["lt"]{'e1} " " `"> " slot["le"]{'e2}

dform atom_binop_ge_df : parens :: "prec"[prec_rel] :: AtomRelop{GeOp; 'e1; 'e2} =
   slot["lt"]{'e1} " " Nuprl_font!ge `" " slot["le"]{'e2}

dform atom_binop_eq_df : parens :: "prec"[prec_rel] :: AtomRelop{EqOp; 'e1; 'e2} =
   slot["lt"]{'e1} " " `"= " slot["le"]{'e2}

dform atom_binop_neq_df : parens :: "prec"[prec_rel] :: AtomRelop{NeqOp; 'e1; 'e2} =
   slot["lt"]{'e1} " " Nuprl_font!neq `" " slot["le"]{'e2}

(* General bin/relop *)
dform atom_binop_gen_df : parens :: "prec"[prec_rel] :: AtomRelop{'op; 'e1; 'e2} =
   slot["lt"]{'e1} `" " slot{'op} `" " slot["le"]{'e2}

dform atom_binop_gen_df : parens :: "prec"[prec_rel] :: AtomBinop{'op; 'e1; 'e2} =
   slot["lt"]{'e1} `" " slot{'op} `" " slot["le"]{'e2}

dform atom_fun_df : parens :: "prec"[prec_fun] :: AtomFun{x. 'e} =
   szone pushm[3] Nuprl_font!lambda Nuprl_font!suba slot{'x} `"." hspace slot{'e} popm ezone

(* Expressions *)
dform exp_let_atom_df : parens :: "prec"[prec_let] :: LetAtom{'a; v. 'e} =
   szone pushm[3] xlet `" " slot{'v} bf[" = "] slot{'a} `" " xin hspace slot["lt"]{'e} popm ezone

dform exp_tailcall_df : parens :: "prec"[prec_let] :: TailCall{'f; 'args} =
   bf["tailcall "] slot{'f} `" " slot{'args}

dform arg_cons_df1 : parens :: "prec"[prec_comma] :: ArgCons{'a1; ArgCons{'a2; 'rest}} =
   slot{'a1} `", " slot["lt"]{ArgCons{'a2; 'rest}}

dform arg_cons_df2 : parens :: "prec"[prec_comma] :: ArgCons{'a; ArgNil} =
   slot{'a}

dform arg_cons_df2 : parens :: "prec"[prec_comma] :: ArgCons{'a; 'b} =
   slot{'a} `" :: " slot{'b}

dform arg_nil_df : parens :: "prec"[prec_comma] :: ArgNil =
   `""

dform exp_if_df : parens :: "prec"[prec_if] :: except_mode[tex] :: If{'a; 'e1; 'e2} =
   szone pushm[0] pushm[3] bf["if"] `" " slot{'a} `" " bf["then"] hspace
   slot{'e1} popm hspace
   pushm[3] bf["else"] hspace slot{'e2} popm popm ezone

(* TEX if *)
dform exp_if_df : parens :: "prec"[prec_if] :: mode[tex] :: If{'a; 'e1; 'e2} =
   bf["if"] `" " slot{'a} `" " bf["then "] slot{'e1} `" " bf["else "] slot{'e2}

(*
 * Reserve.
 *)
dform reserve_df1 : parens :: "prec"[prec_let] :: Reserve[words:n]{'e} =
   bf["reserve "] slot[words:n] bf[" words in"] hspace slot["lt"]{'e}

dform reserve_df2 : parens :: "prec"[prec_let] :: Reserve[words:n]{'args; 'e} =
   bf["reserve "] slot[words:n] bf[" words args "] slot{'args} bf[" in"] hspace slot["lt"]{'e}

dform reserve_cons_df1 : parens :: "prec"[prec_comma] :: ReserveCons{'a1; ReserveCons{'a2; 'rest}} =
   slot{'a1} `", " slot["lt"]{ReserveCons{'a2; 'rest}}

dform reserve_cons_df2 : parens :: "prec"[prec_comma] :: ReserveCons{'a; ArgNil} =
   slot{'a}

dform reserve_nil_df : parens :: "prec"[prec_comma] :: ReserveNil =
   `""

doc <:doc< Sequent tag for the M language. >>

declare sequent [sequent_arg] { Term : Term >- Term } : Judgment
dform sequent_arg_df: sequent_arg = subm

doc docoff

declare default_extract

dform default_extract_df : sequent { <H> >- default_extract } = `""

doc <:doc<
   @modsubsection{Subscripting.}
   Tuples are listed in reverse order.
>>
declare alloc_tuple{'l1; 'l2}
declare alloc_tuple{'l}

doc <:doc< @docoff >>

dform length_df : Length[i:n] =
   slot[i:n]

dform alloc_tuple_start_nil_df : AllocTupleNil =
   alloc_tuple{nil; AllocTupleNil}

dform alloc_tuple_start_cons_df : AllocTupleCons{'a; 'rest} =
   alloc_tuple{nil; AllocTupleCons{'a; 'rest}}

dform alloc_tuple_shift_df : alloc_tuple{'l; AllocTupleCons{'a; 'rest}} =
   alloc_tuple{cons{'a; 'l}; 'rest}

dform alloc_tuple_start_df : alloc_tuple{'l; AllocTupleNil} =
   szone pushm[1] bf["("] alloc_tuple{'l} bf[")"] popm ezone

(* General alloc_tuple *)
dform alloc_tuple_start_df : alloc_tuple{'l; 'tl} =
   slot{'l} `" :: " slot{'tl}

dform alloc_tuple_nil_df : alloc_tuple{nil} =
   `""

dform alloc_tuple_cons_nil_df : alloc_tuple{cons{'a; nil}} =
   slot{'a}

dform alloc_tuple_cons_cons_df : alloc_tuple{cons{'a1; cons{'a2; 'l}}} =
   slot{'a1} bf[","] hspace alloc_tuple{cons{'a2; 'l}}

(*
 * Actual tuple operations.
 *)
dform exp_let_tuple_df : parens :: "prec"[prec_let] :: LetTuple{'length; 'tuple; v. 'e} =
   szone pushm[3] xlet `" " slot{'v} bf[" =[length = "] slot{'length} bf["] "] slot{'tuple} `" " xin hspace slot["lt"]{'e} popm ezone

dform exp_subscript_df : parens :: "prec"[prec_let] :: LetSubscript{'a1; 'a2; v. 'e} =
   szone pushm[3] xlet `" " slot{'v} bf[" = "] slot{'a1} `".[" slot{'a2} `"] " xin hspace slot["lt"]{'e} popm ezone

dform exp_set_subscript_df : parens :: "prec"[prec_let] :: SetSubscript{'a1; 'a2; 'a3; 'e} =
   slot{'a1} `".[" slot{'a2} `"] " leftarrow `" " slot{'a3} `";" hspace slot["lt"]{'e}

(*
 * Functions and application.
 *)
dform exp_let_apply_df : parens :: "prec"[prec_let] :: LetApply{'f; 'a; v. 'e} =
   szone pushm[3] xlet bf[" apply "] slot{'v} bf[" = "] slot{'f} `"(" slot{'a} `") " xin hspace slot["lt"]{'e} popm ezone

dform exp_let_closure_df : parens :: "prec"[prec_let] :: LetClosure{'f; 'a; v. 'e} =
   szone pushm[3] xlet bf[" closure "] slot{'v} bf[" = "] slot{'f} `"(" slot{'a} `") " xin hspace slot["lt"]{'e} popm ezone

dform exp_return_df : Return{'a} =
   bf["return"] `"(" slot{'a} `")"

(*
 * Recursive functions.
 *)
dform let_rec_df : parens :: "prec"[prec_let] :: LetRec{R1. 'e1; R2. 'e2} =
   szone pushm[3] xlet bf[" rec "] slot{'R1} `"." hspace 'e1 popm ezone hspace slot{'R2} `"." xin hspace slot["lt"]{'e2}

dform fields_df : parens :: "prec"[prec_let] :: Fields{'fields} =
   szone pushm[0] pushm[2] bf["{ "] slot["lt"]{'fields} popm hspace bf["}"] popm ezone

dform fun_def_df : parens :: "prec"[prec_let] :: FunDef{'label; 'e; 'rest} =
   szone pushm[3] bf["fun "] slot{'label} `" =" hspace slot{'e} popm ezone hspace 'rest

dform end_def_df : EndDef =
   `""

dform label_df : Label[s:s] =
   `"\"" slot[s:s] `"\""

dform let_fun_def : parens :: "prec"[prec_let] :: LetFun{'R; 'label; f. 'e} =
   szone pushm[3] xlet bf[" fun "] slot{'f} `" = " slot{'R} `"." slot{'label} `" " xin hspace slot["lt"]{'e} popm ezone

(*
 * Initialization code.
 *)
dform initialize_df : parens :: "prec"[prec_let] :: Initialize{'e} =
   szone pushm[0] pushm[3] bf["initialization"] hspace slot{'e} popm hspace bf["end"] popm ezone

(*
 * Declarations and definitions.
 *)
dform exp_df : exp = bf["exp"]

dform def_df : def{'v; 'e} =
   slot{'v} bf[" = "] slot{'e}

dform compilable_df : "prec"[prec_compilable] :: compilable{'e} =
   szone pushm[0] pushm[3] bf["compilable"] hspace slot{'e} popm hspace bf["end"] popm ezone

(************************************************************************
 * ML Helpers
 *)
let fundef_term      = << FunDef{'label; 'e; 'rest} >>
let fundef_opname    = opname_of_term fundef_term
let is_fundef_term   = is_dep0_dep0_dep0_term fundef_opname
let dest_fundef_term = dest_dep0_dep0_dep0_term fundef_opname
let mk_fundef_term   = mk_dep0_dep0_dep0_term fundef_opname

let letrec_term      = << LetRec{R1. 'fields['R1]; R2. 'body['R2]} >>
let letrec_opname    = opname_of_term letrec_term
let is_letrec_term   = is_dep1_dep1_term letrec_opname
let dest_letrec_term = dest_dep1_dep1_term letrec_opname
let mk_letrec_term   = mk_dep1_dep1_term letrec_opname


(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
