(*!
 * @begin[doc]
 * @module[M_x86]
 *
 * Compile @emph{M} programs to x86 assembly.
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
extends M_ir
extends X86_asm
(*! @docoff *)

open M_util

open Refiner.Refiner.Term

open Mp_resource
open Term_match_table

open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Tactic_type.Sequent

(*
 * Assembler term.
 *)
declare ASM{'e}
declare ASM{'a; v. 'e['v]}

(************************************************************************
 * REDUCTION RESOURCE                                                   *
 ************************************************************************)

(*!
 * @begin[doc]
 * @resources
 *
 * @bf{The @Comment!resource[prog_resource]}
 *
 * The @tt{prog} resource provides a generic method for
 * defining @emph{CPS transformation}.  The @conv[progC] conversion
 * can be used to apply this evaluator.
 *
 * The implementation of the @tt{prog_resource} and the @tt[progC]
 * conversion rely on tables to store the shape of redices, together with the
 * conversions for the reduction.
 *
 * @docoff
 * @end[doc]
 *)
let resource assemble =
   table_resource_info identity extract_data

let assembleTopC_env e =
   get_resource_arg (env_arg e) get_assemble_resource

let assembleTopC = funC assembleTopC_env

let assembleC =
   repeatC (higherC assembleTopC)

(************************************************************************
 * Rewrites.
 *)
prim_rw asm_atom_int :
   ASM{AtomInt[i:n]; v. 'e['v]}
   <-->
   'e[ImmediateNumber[i:n]]

prim_rw asm_atom_var :
   ASM{AtomVar{'v1}; v2. 'e['v2]}
   <-->
   'e[Register{'v1}]

prim_rw asm_atom_fun_var :
   ASM{AtomFunVar{'v1}; v2. 'e['v2]}
   <-->
   'e[ImmediateLabel{'v1}]

prim_rw asm_atom_binop_add :
   ASM{AtomBinop{AddOp; 'a1; 'a2}; v. 'e['v]}
   <-->
   ASM{'a1; v1.
   ASM{'a2; v2.
   RegDecl{v.
   cons{MOV{Register{'v}; 'v1};
   cons{ADD{Register{'v}; 'v2};
   'e['v]}}}}}

prim_rw asm_atom_binop_sub :
   ASM{AtomBinop{SubOp; 'a1; 'a2}; v. 'e['v]}
   <-->
   ASM{'a1; v1.
   ASM{'a2; v2.
   RegDecl{v.
   cons{MOV{Register{'v}; 'v1};
   cons{SUB{Register{'v}; 'v2};
   'e['v]}}}}}

prim_rw asm_let_atom :
   ASM{LetAtom{'a; v. 'e['v]}}
   <-->
   ASM{'a; v2.
   RegDecl{v.
   cons{MOV{Register{'v}; 'v2};
        ASM{'e['v]}}}}

(*
 * Add all these rules to the CPS resource.
 *)
let resource assemble +=
    [<< ASM{AtomInt[i:n]; v. 'e['v]} >>, asm_atom_int;
     << ASM{AtomVar{'v1}; v2. 'e['v2]} >>, asm_atom_var;
     << ASM{AtomFunVar{'v1}; v2. 'e['v2]} >>, asm_atom_fun_var;
     << ASM{AtomBinop{AddOp; 'a1; 'a2}; v. 'e['v]} >>, asm_atom_binop_add;
     << ASM{AtomBinop{SubOp; 'a1; 'a2}; v. 'e['v]} >>, asm_atom_binop_sub;
     << ASM{LetAtom{'a; v. 'e['v]}} >>, asm_let_atom]

(*
 * Assembler.
 *)
let assembleT =
   onAllHypsT (fun i -> tryT (rw assembleC i)) thenT rw assembleC 0

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
