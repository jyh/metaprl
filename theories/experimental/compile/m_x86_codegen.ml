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
extends M_x86_frame
(*! @docoff *)

open M_util

open Refiner.Refiner.Term

open Mp_resource
open Term_match_table

open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Tactic_type.Sequent

open Top_conversionals

(************************************************************************
 * Reduction resource
 *)

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
let resource codegen =
   table_resource_info identity extract_data

let codegenTopC_env e =
   get_resource_arg (env_arg e) get_codegen_resource

let codegenTopC = funC codegenTopC_env

let codegenC =
   repeatC (higherC codegenTopC)

(*!
 * @begin[doc]
 * @modsubsection{Terms}
 * @end[doc]
 *)
declare ASM{'e}
declare ASM{'a; v. 'e['v]}
declare ASM{'R; 'e}

(*
 * Helper term to store fields into a tuple.
 *)
declare store_tuple{'v; 'tuple; 'rest}
declare store_tuple{'v; 'off; 'tuple; 'rest}

dform store_tuple_df1 : store_tuple{'v; 'tuple; 'rest} =
   bf["store_tuple["] slot{'v} `", " slot{'tuple} hspace slot{'rest}

dform store_tuple_df2 : store_tuple{'v; 'off; 'tuple; 'rest} =
    bf["store_tuple["] slot{'v} `", " slot{'off} `", " slot{'tuple} hspace slot{'rest}

prim_rw unfold_store_tuple :
   store_tuple{'v; 'tuple; 'rest}
   <-->
   Comment["unfold_store_tuple"]{
   MOV{'v; p. store_tuple{'p; number[0:n]; 'tuple; 'rest}}}

prim_rw unfold_store_tuple_cons :
   store_tuple{'v; 'off; AllocTupleCons{'a; 'tl}; 'rest}
   <-->
   ASM{'a; x.
   MOV{MemRegOff{'v; 'off}; 'x;
   store_tuple{'v; add{'off; word_size}; 'tl; 'rest}}}

prim_rw unfold_store_tuple_nil :
   store_tuple{'v; 'off; AllocTupleNil; 'rest}
   <-->
   'rest

(*!
 * @begin[doc]
 * @modsubsection{Code generation}
 * @end[doc]
 *)
prim_rw asm_atom_false :
   ASM{AtomFalse; v. 'e['v]}
   <-->
   'e[ImmediateNumber[0:n]]

prim_rw asm_atom_true :
   ASM{AtomTrue; v. 'e['v]}
   <-->
  'e[ImmediateNumber[1:n]]

prim_rw asm_atom_int :
   ASM{AtomInt[i:n]; v. 'e['v]}
   <-->
   'e[ImmediateNumber[i:n]]

prim_rw asm_atom_var :
   ASM{AtomVar{'v1}; v2. 'e['v2]}
   <-->
   'e[Register{'v1}]

prim_rw asm_atom_fun_var :
   ASM{AtomFunVar{'R; Label[label:t]}; v2. 'e['v2]}
   <-->
   'e[ImmediateCLabel[label:t]{'R}]

prim_rw asm_atom_fun :
   ASM{AtomFun{v. 'e['v]}}
   <-->
   LabelFun{v. ASM{'e['v]}}

prim_rw asm_atom_binop_add :
   ASM{AtomBinop{AddOp; 'a1; 'a2}; v. 'e['v]}
   <-->
   Comment["asm_atom_binop_add"]{
   ASM{'a1; v1.
   ASM{'a2; v2.
   MOV{'v1; x.
   ADD{Register{'x}; 'v2;
   'e[Register{'x}]}}}}}

prim_rw asm_atom_binop_sub :
   ASM{AtomBinop{SubOp; 'a1; 'a2}; v. 'e['v]}
   <-->
   ASM{'a1; v1.
   ASM{'a2; v2.
   MOV{'v1; v.
   SUB{Register{'v}; 'v2;
   'e[Register{'v}]}}}}

prim_rw asm_atom_binop_mul :
   ASM{AtomBinop{MulOp; 'a1; 'a2}; v. 'e['v]}
   <-->
   ASM{'a1; v1.
   ASM{'a2; v2.
   MOV{'v1; v.
   IMUL{Register{'v}; 'v2;
   'e[Register{'v}]}}}}

prim_rw asm_atom_binop_div :
   ASM{AtomBinop{MulOp; 'a1; 'a2}; v. 'e['v]}
   <-->
   ASM{'a1; v1.
   ASM{'a2; v2.
   MOV{ImmediateNumber[0:n]; edx.
   MOV{'v1; eax.
   DIV{Register{'edx}; Register{'eax}; 'v2;
   'e[Register{'eax}]}}}}}

(*
 * We should probably change the representation
 * of the instructions so we can fold the following
 * size rewrites together.
 *)
prim_rw asm_atom_binop_eq :
   ASM{AtomBinop{EqOp; 'a1; 'a2}; v. 'e['v]}
   <-->
   ASM{'a1; v1.
   ASM{'a2; v2.
   MOV{ImmediateNumber[0:n]; v.
   CMP{'v1; 'v2;
   SET{EQ; Register{'v};
   'e[Register{'v}]}}}}}

prim_rw asm_atom_binop_neq :
   ASM{AtomBinop{NeqOp; 'a1; 'a2}; v. 'e['v]}
   <-->
   ASM{'a1; v1.
   ASM{'a2; v2.
   MOV{ImmediateNumber[0:n]; v.
   CMP{'v1; 'v2;
   SET{NEQ; Register{'v};
   'e[Register{'v}]}}}}}

prim_rw asm_atom_binop_lt :
   ASM{AtomBinop{LtOp; 'a1; 'a2}; v. 'e['v]}
   <-->
   ASM{'a1; v1.
   ASM{'a2; v2.
   MOV{ImmediateNumber[0:n]; v.
   CMP{'v1; 'v2;
   SET{LT; Register{'v};
   'e[Register{'v}]}}}}}

prim_rw asm_atom_binop_le :
   ASM{AtomBinop{LeOp; 'a1; 'a2}; v. 'e['v]}
   <-->
   ASM{'a1; v1.
   ASM{'a2; v2.
   MOV{ImmediateNumber[0:n]; v.
   CMP{'v1; 'v2;
   SET{LE; Register{'v};
   'e[Register{'v}]}}}}}

prim_rw asm_atom_binop_gt :
   ASM{AtomBinop{GtOp; 'a1; 'a2}; v. 'e['v]}
   <-->
   ASM{'a1; v1.
   ASM{'a2; v2.
   MOV{ImmediateNumber[0:n]; v.
   CMP{'v1; 'v2;
   SET{GT; Register{'v};
   'e[Register{'v}]}}}}}

prim_rw asm_atom_binop_ge :
   ASM{AtomBinop{GeOp; 'a1; 'a2}; v. 'e['v]}
   <-->
   ASM{'a1; v1.
   ASM{'a2; v2.
   MOV{ImmediateNumber[0:n]; v.
   CMP{'v1; 'v2;
   SET{GE; Register{'v};
   'e[Register{'v}]}}}}}

prim_rw asm_let_atom :
   ASM{LetAtom{'a; v. 'e['v]}}
   <-->
   Comment["asm_let_atom"]{
   ASM{'a; v.
   ASM{'e['v]}}}

prim_rw asm_tailcall_1 :
   ASM{TailCall{'f; 'a1}}
   <-->
   Comment["asm_tailcall_1"]{
   ASM{'f;  v0.
   ASM{'a1; v1.
   JMP{'v0; 'v1}}}}

prim_rw asm_tailcall_2 :
   ASM{TailCall{'f; 'a1; 'a2}}
   <-->
   Comment["asm_tailcall_2"]{
   ASM{'f;  v0.
   ASM{'a1; v1.
   ASM{'a2; v2.
   JMP{'v0; 'v1; 'v2}}}}}

prim_rw asm_tailcall_3 :
   ASM{TailCall{'f; 'a1; 'a2; 'a3}}
   <-->
   Comment["asm_tailcall_3"]{
   ASM{'f;  v0.
   ASM{'a1; v1.
   ASM{'a2; v2.
   ASM{'a3; v3.
   JMP{'v0; 'v1; 'v2; 'v3}}}}}}

prim_rw asm_if_1 :
   ASM{If{'a; TailCall{'f; 'a1}; 'e}}
   <-->
   Comment["asm_if_1"]{
   ASM{'a;  test.
   ASM{'f;  v0.
   ASM{'a1; v1.
   CMP{'test; ImmediateNumber[0:n];
   JCC{EQ; 'v0; 'v1;
   ASM{'e}}}}}}}

prim_rw asm_if_2 :
   ASM{If{'a; TailCall{'f; 'a1; 'a2}; 'e}}
   <-->
   Comment["asm_if_2"]{
   ASM{'a;  test.
   ASM{'f;  v0.
   ASM{'a1; v1.
   ASM{'a2; v2.
   CMP{'test; ImmediateNumber[0:n];
   JCC{EQ; 'v0; 'v1; 'v2;
   ASM{'e}}}}}}}}

prim_rw asm_if_3 :
   ASM{If{'a; TailCall{'f; 'a1; 'a2; 'a3}; 'e}}
   <-->
   Comment["asm_if_3"]{
   ASM{'a;  test.
   ASM{'f;  v0.
   ASM{'a1; v1.
   ASM{'a2; v2.
   ASM{'a3; v3.
   CMP{'test; ImmediateNumber[0:n];
   JCC{EQ; 'v0; 'v1; 'v2; 'v3;
   ASM{'e}}}}}}}}}

prim_rw asm_alloc_tuple :
   ASM{LetTuple{Length[i:n]; 'tuple; v. 'e['v]}}
   <-->
   Comment["asm_alloc_tuple"]{
   LetAllocHandle{base, next, limit.
   MOV{Register{'next}; v.
   SUB{Register{'next}; ImmediateNumber{mul{add{number[i:n]; number[1:n]}; word_size}};
   MOV{MemReg{'v}; header[i:n];
   ADD{Register{'v}; ImmediateNumber{word_size};
   store_tuple{'v; 'tuple;
   ASM{'e['v]}}}}}}}}

prim_rw asm_let_subscript :
   ASM{LetSubscript{'a1; 'a2; v. 'e['v]}}
   <-->
   Comment["asm_let_subscript"]{
   ASM{'a1; v1.
   ASM{'a2; v2.
   MOV{MemRegRegOffMul{'v1; 'v2; number[0:n]; word_size}; v.
   ASM{'e['v]}}}}}

prim_rw asm_set_subscript :
   ASM{SetSubscript{'a1; 'a2; 'a3; 'e}}
   <-->
   Comment["asm_set_subscript"]{
   ASM{'a1; v1.
   ASM{'a2; v2.
   ASM{'a3; v3.
   MOV{MemRegRegOffMul{'v1; 'v2; number[0:n]; word_size}; 'v3;
   ASM{'e}}}}}}

prim_rw asm_let_closure :
   ASM{LetClosure{'a1; 'a2; v. 'e['v]}}
   <-->
   Comment["asm_let_closure"]{
   LetAllocHandle{base, next, limit.
   MOV{Register{'next}; v.
   SUB{Register{'next}; ImmediateNumber{mul{number[3:n]; word_size}};
   MOV{MemReg{'v}; header[2:n];
   ASM{'a1; v1.
   ASM{'a2; v2.
   MOV{MemRegOff{'v; word_size}; 'v1;
   MOV{MemRegOff{'v; mul{number[2:n]; word_size}}; 'v2;
   ADD{Register{'v}; ImmediateNumber{word_size};
   ASM{'e['v]}}}}}}}}}}}

prim_rw asm_letrec :
   ASM{LetRec{R1. 'fields['R1]; R2. 'e['R2]}}
   <-->
   Comment["asm_letrec"]{
   LabelRec{R1. ASM{'R1; 'fields['R1]}; R2. ASM{'e['R2]}}}

prim_rw asm_fields :
   ASM{'R; Fields{'fields}}
   <-->
   ASM{'R; 'fields}

prim_rw asm_fun_def :
   ASM{'R; FunDef{Label[label:t]; 'e; 'rest}}
   <-->
   LabelDef{LabelAsm[label:t]{'R}; ASM{'e}; ASM{'R; 'rest}}

prim_rw asm_end_def :
   ASM{'R; EndDef}
   <-->
   LabelEnd

(*
 * Cleanup.  It is debatiable whether we should have cleanup here...
 *)
prim_rw mem_reg_reg_off_mul_cleanup_1 :
   MemRegRegOffMul[off:n, mul:n]{Register{'r1}; 'r2}
   <-->
   MemRegRegOffMul[off:n, mul:n]{'r1; 'r2}

prim_rw mem_reg_reg_off_mul_cleanup_2 :
   MemRegRegOffMul[off:n, mul:n]{'r1; Register{'r2}}
   <-->
   MemRegRegOffMul[off:n, mul:n]{'r1; 'r2}

prim_rw mem_reg_reg_off_mul_cleanup_3 :
   MemRegRegOffMul[off:n, mul:n]{'r1; ImmediateNumber[j:n]}
   <-->
   MemRegOff{'r1; add{mul{number[mul:n]; number[j:n]}; number[off:n]}}

prim_rw mem_reg_off_cleanup_1 :
   MemRegOff[0:n]{'r}
   <-->
   MemReg{'r}

(*
 * Add all these rules to the CPS resource.
 *)
let resource codegen +=
    [<< ASM{AtomFalse; v. 'e['v]} >>, asm_atom_false;
     << ASM{AtomTrue; v. 'e['v]} >>, asm_atom_true;
     << ASM{AtomInt[i:n]; v. 'e['v]} >>, asm_atom_int;
     << ASM{AtomVar{'v1}; v2. 'e['v2]} >>, asm_atom_var;
     << ASM{AtomFunVar{'R; 'v1}; v2. 'e['v2]} >>, asm_atom_fun_var;
     << ASM{AtomFun{v. 'e['v]}} >>, asm_atom_fun;
     << ASM{AtomBinop{AddOp; 'a1; 'a2}; v. 'e['v]} >>, asm_atom_binop_add;
     << ASM{AtomBinop{SubOp; 'a1; 'a2}; v. 'e['v]} >>, asm_atom_binop_sub;
     << ASM{AtomBinop{MulOp; 'a1; 'a2}; v. 'e['v]} >>, asm_atom_binop_mul;
     << ASM{AtomBinop{DivOp; 'a1; 'a2}; v. 'e['v]} >>, asm_atom_binop_div;
     << ASM{AtomBinop{EqOp; 'a1; 'a2}; v. 'e['v]} >>,  asm_atom_binop_eq;
     << ASM{AtomBinop{NeqOp; 'a1; 'a2}; v. 'e['v]} >>, asm_atom_binop_neq;
     << ASM{AtomBinop{LtOp; 'a1; 'a2}; v. 'e['v]} >>,  asm_atom_binop_lt;
     << ASM{AtomBinop{LeOp; 'a1; 'a2}; v. 'e['v]} >>,  asm_atom_binop_le;
     << ASM{AtomBinop{GtOp; 'a1; 'a2}; v. 'e['v]} >>,  asm_atom_binop_gt;
     << ASM{AtomBinop{GeOp; 'a1; 'a2}; v. 'e['v]} >>,  asm_atom_binop_ge;
     << ASM{LetAtom{'a; v. 'e['v]}} >>, asm_let_atom;
     << ASM{TailCall{'f; 'a1}} >>, asm_tailcall_1;
     << ASM{TailCall{'f; 'a1; 'a2}} >>, asm_tailcall_2;
     << ASM{TailCall{'f; 'a1; 'a2; 'a3}} >>, asm_tailcall_3;
     << ASM{If{'a; TailCall{'f; 'a1}; 'e}} >>, asm_if_1;
     << ASM{If{'a; TailCall{'f; 'a1; 'a2}; 'e}} >>, asm_if_2;
     << ASM{If{'a; TailCall{'f; 'a1; 'a2; 'a3}; 'e}} >>, asm_if_3;
     << ASM{LetTuple{Length[i:n]; 'tuple; v. 'e['v]}} >>, asm_alloc_tuple;
     << ASM{LetSubscript{'a1; 'a2; v. 'e['v]}} >>, asm_let_subscript;
     << ASM{SetSubscript{'a1; 'a2; 'a3; 'e}} >>, asm_set_subscript;
     << ASM{LetClosure{'a1; 'a2; v. 'e['v]}} >>, asm_let_closure;
     << ASM{LetRec{R1. 'fields['R1]; R2. 'e['R2]}} >>, asm_letrec;
     << ASM{'R; Fields{'fields}} >>, asm_fields;
     << ASM{'R; FunDef{Label[label:t]; 'e; 'rest}} >>, asm_fun_def;
     << ASM{'R; EndDef} >>, asm_end_def;
     << MemRegRegOffMul[off:n, mul:n]{Register{'r1}; 'r2} >>, mem_reg_reg_off_mul_cleanup_1;
     << MemRegRegOffMul[off:n, mul:n]{'r1; Register{'r2}} >>, mem_reg_reg_off_mul_cleanup_2;
     << MemRegRegOffMul[off:n, mul:n]{'r1; ImmediateNumber[j:n]} >>, mem_reg_reg_off_mul_cleanup_3;
     << MemRegOff[0:n]{'r} >>, mem_reg_off_cleanup_1;
     << store_tuple{'v; 'tuple; 'rest} >>, unfold_store_tuple;
     << store_tuple{'v; 'off; AllocTupleCons{'a; 'tl}; 'rest} >>, unfold_store_tuple_cons;
     << store_tuple{'v; 'off; AllocTupleNil; 'rest} >>, unfold_store_tuple_nil]

(*!
 * @begin[doc]
 * The program is compilable if the assembly is compilable.
 * @end[doc]
 *)
interactive codegen_prog :
   sequent [m] { 'H >- compilable{ASM{'e}} } -->
   sequent [m] { 'H >- compilable{'e} }

(*
 * Assembler.
 *)
let codegenT =
   codegen_prog thenT rw (repeatC (codegenC thenC reduceC)) 0

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
