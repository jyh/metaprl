doc <:doc<

   @module[M_post_parsing]
   Following parsing, we perform currying of function applications,
   and identify function variables in the body of the program.

   Note that at this point, function definitions had been curried.

   ----------------------------------------------------------------

   @begin[license]
   Copyright (C) 2003 Adam Granicz, Caltech

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

   Author: Adam Granicz
   @email{granicz@cs.caltech.edu}
   @end[license]
>>

doc <:doc<
   @parents
>>
extends M_ir
extends M_ast
doc docoff

open M_ir
open M_ast
open M_util

open Lm_printf

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError

open Mp_resource
open Simple_print
open Term_match_table

open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Tactic_type.Sequent

(************************************************************************
 * REDUCTION RESOURCE                                                   *
 ************************************************************************)

doc <:doc<
   @resources

   @bf{The @Comment!resource[pp_resource]}

   The @tt{pp} resource performs the @emph{post-parsing transformation}.
   The @conv[ppC] conversion can be used to apply this evaluator.

   The implementation of the @tt{pp_resource} and the @tt[ppC]
   conversion rely on tables to store the shape of redices, together with the
   conversions for the reduction.

   @docoff
>>
(*
 * Resource PP.
 *)
let resource pp =
   table_resource_info extract_data

let ppTopC_env e =
   get_resource_arg (env_arg e) get_pp_resource

let ppTopC = funC ppTopC_env

let ppC =
   repeatC (higherC ppTopC)

(************************************************************************
 * Post-parsing transformations
 ************************************************************************)

doc <:doc<
   @modsubsection{Application}

   Add an application that we will map through the program.
   This should be eliminated by the end of PP conversion.
>>
declare PP{'e}

dform ps_df : PP{'e} =
   szone pushm[1] bf["POST-PARSING["] 'e popm bf["]"] ezone

doc <:doc<
   @modsubsection{Currying function applications}

   We curry each tailcall or function application with multiple
   arguments. The results of the partial function applications
   are stored in temporary variables.
   Calls with one argument are mapped as identity (after removing
   the useless pair wrapper from around the argument).
>>
(*
 * Atoms.
 * We apply the tranlation to sub-atoms and expressions.
 *)
prim_rw pp_atom_false : PP{AtomFalse} <-->
   AtomFalse

prim_rw pp_atom_true : PP{AtomTrue} <-->
   AtomTrue

prim_rw pp_atom_int : PP{AtomInt[i:n]} <-->
   AtomInt[i:n]

prim_rw pp_atom_binop : PP{AtomBinop{'op; 'a1; 'a2}} <-->
   AtomBinop{'op; PP{'a1}; PP{'a2}}

prim_rw pp_atom_fun : PP{AtomFun{x. 'e['x]}} <-->
   AtomFun{x. PP{'e['x]}}

prim_rw pp_atom_var : PP{AtomVar{'v}} <-->
   AtomVar{'v}

prim_rw pp_atom_funvar : PP{AtomFunVar{'v}} <-->
   AtomFunVar{'v}

(*
 * Expressions.
 *)
prim_rw pp_let_atom : PP{LetAtom{'a; v. 'e['v]}} <-->
   LetAtom{PP{'a}; v. PP{'e['v]}}

(*
 * At this point, only TailCall{'f; mcons{...}}'s exist.
 * Tailcalls with one argument are not affected.
 *)
prim_rw pp_tailcall1 : PP{TailCall{'f; mcons{'a; mnil}}} <-->
   TailCall{'f; PP{'a}}

(*
 * Tailcalls with more than one argument get expanded into
 * a chain of LetApply's.
 *)
prim_rw pp_tailcall2 : PP{TailCall{'f; mcons{'a; 'args}}} <-->
   LetApply{'f; PP{'a}; v1.
   PP{TailCall{AtomFunVar{'v1}; 'args}}}

prim_rw pp_if : PP{If{'a; 'e1; 'e2}} <-->
   If{PP{'a}; PP{'e1}; PP{'e2}}

prim_rw pp_let_pair : PP{LetPair{'a1; 'a2; v. 'e['v]}} <-->
   LetPair{PP{'a1}; PP{'a2}; v. PP{'e['v]}}

prim_rw pp_let_subscript : PP{LetSubscript{'a1; 'a2; v. 'e['v]}} <-->
   LetSubscript{PP{'a1}; PP{'a2}; v. PP{'e['v]}}

prim_rw pp_set_subscript : PP{SetSubscript{'a1; 'a2; 'a3; 'e}} <-->
   SetSubscript{PP{'a1}; PP{'a2}; PP{'a3}; PP{'e}}

(*
 * Applications with one argument are ok.
 *)
prim_rw pp_let_apply1 : PP{LetApply{'f; mcons{'a; mnil}; v. 'e['v]}} <-->
   LetApply{'f; PP{'a}; v. PP{'e['v]}}

(*
 * Function applications with more than one argument are
 * expanded into a chain of LetApply's.
 *)
prim_rw pp_let_apply2 : PP{LetApply{'f; mcons{'a; 'args}; v. 'e['v]}} <-->
   LetApply{'f; PP{'a}; v1.
   PP{LetApply{AtomFunVar{'v1}; 'args; v. 'e['v]}}}

prim_rw pp_let_closure : PP{LetClosure{'a1; 'a2; f. 'e['f]}} <-->
   LetClosure{PP{'a1}; PP{'a2}; f. PP{'e['f]}}

prim_rw pp_return : PP{Return{'a}} <-->
   Return{PP{'a}}

prim_rw pp_fun_decl : PP{FunDecl{f. 'e['f]}} <-->
   FunDecl{f. PP{'e['f]}}

prim_rw pp_fun_def : PP{FunDef{'f; 'a; 'e}} <-->
   FunDef{'f; PP{'a}; PP{'e}}

(*
 * Add these rewrites to the pp resource.
 *)
let resource pp +=
   [<< PP{AtomFalse} >>, pp_atom_false;
    << PP{AtomTrue} >>, pp_atom_true;
    << PP{AtomInt[i:n]} >>, pp_atom_int;
    << PP{AtomBinop{'op; 'a1; 'a2}} >>, pp_atom_binop;
    << PP{AtomFun{x. 'e['x]}} >>, pp_atom_fun;
    << PP{AtomVar{'v}} >>, pp_atom_var;
    << PP{AtomFunVar{'v}} >>, pp_atom_funvar;
    << PP{LetAtom{'a; v. 'e['v]}} >>, pp_let_atom;
    << PP{TailCall{'f; mcons{'a; mnil}}} >>, pp_tailcall1;
    << PP{TailCall{'f; mcons{'a; 'args}}} >>, pp_tailcall2;
    << PP{If{'a; 'e1; 'e2}} >>, pp_if;
    << PP{LetPair{'a1; 'a2; v. 'e['v]}} >>,  pp_let_pair;
    << PP{LetSubscript{'a1; 'a2; v. 'e['v]}} >>, pp_let_subscript;
    << PP{SetSubscript{'a1; 'a2; 'a3; 'e}} >>, pp_set_subscript;
    << PP{LetApply{'f; mcons{'a; mnil}; v. 'e['v]}} >>, pp_let_apply1;
    << PP{LetApply{'f; mcons{'a; 'args}; v. 'e['v]}} >>, pp_let_apply2;
    << PP{LetClosure{'a1; 'a2; f. 'e['f]}} >>, pp_let_closure;
    << PP{Return{'a}} >>, pp_return;
    << PP{FunDecl{f. 'e['f]}} >>, pp_fun_decl;
    << PP{FunDef{'f; 'e1; 'e2}} >>, pp_fun_def]


(*
 * Toplevel PP conversion tactic.
 *)
let ppT =
   onAllHypsT (fun i -> tryT (rw ppC i)) thenT rw ppC 0
