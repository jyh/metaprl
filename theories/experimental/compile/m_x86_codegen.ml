doc <:doc< 
   @spelling{compilable}
  
   @begin[doc]
   @module[M_x86_codegen]
   This module implements the translation of IR terms to
   x86 assembly.
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

doc <:doc< @doc{@parents} >>
extends M_ir
extends M_x86_frame
doc docoff

open M_util

open Refiner.Refiner.Term

open Mp_resource
open Term_match_table

open Tactic_type.Tacticals
open Tactic_type.Sequent

open Top_conversionals

doc <:doc< 
   @begin[doc]
   @modsection{Terms}

   We define several terms to represent the assembly translation. All these
   terms are eliminated by the end of the translation process.

   @begin[itemize]
   @item{<<ASM{'e}>> represents the translation of IR @emph{expressions} into sequences
   of assembly instructions.}
   @item{<<ASM{'a; v. 'e['v]}>> represents the translation of an IR @emph{atom} into
   an assembly operand, which in turn is substituted for variable $v$ in $e[v]$.}
   @item{<<ASM{'args1; 'args2; v. 'e['v]}>> represents the translation of IR function @emph{arguments} into
   assembly operands}
   @item{<<ASM{'R; 'e}>> represents the translation of the mutually recursive IR @emph{functions}
   in record $R$ and the rest of the program.}
   @end[itemize]
   @end[doc]
>>
declare ASM{'e}
declare ASM{'a; v. 'e['v]}
declare ASM{'args1; 'args2; v. 'e['v]}
declare ASM{'R; 'e}

doc <:doc< @docoff >>

dform asm_df1 : ASM{'e} =
   szone pushm[0] pushm[3]
   bf["assemble"]
   hspace
   slot{'e}
   popm hspace bf["end"]
   popm ezone

dform asm_df2 : ASM{'a; v. 'e} =
   bf["let "] slot{'v} bf[" = assemble("] slot{'a} bf[") in"] hspace slot{'e}

dform asm_df3 : ASM{'args1; 'args2; v. 'e} =
   szone pushm[0] pushm[3] bf["assemble args["]
   hspace bf["src = "] slot{'args1}
   hspace bf["dst = "] slot{'args2}
   hspace bf["as "] slot{'v} bf[" ]"]
   popm hspace bf["in"]
   popm ezone hspace slot{'e}

dform asm_df4 : ASM{'R; 'e} =
   szone pushm[0] pushm[3]
   bf["assemble ["] slot{'R} bf["]"]
   hspace
   slot{'e}
   popm hspace bf["end"]
   popm ezone

doc <:doc<
   @begin[doc]
   Helper terms to store fields into a tuple.
   @end[doc]
>>
declare store_tuple{'v; 'tuple; 'rest}
declare store_tuple{'v; 'off; 'tuple; 'rest}

prim_rw unfold_store_tuple {| reduce |} :
   store_tuple{'v; 'tuple; 'rest}
   <-->
   Comment["unfold_store_tuple"]{
   Mov{Register{'v}; p.
   store_tuple{'p; number[0:n]; 'tuple; 'rest}}}

prim_rw unfold_store_tuple_cons {| reduce |} :
   store_tuple{'v; 'off; AllocTupleCons{'a; 'tl}; 'rest}
   <-->
   Comment["unfold_store_tuple_cons"]{
   ASM{'a; v1.
   Inst2["mov"]{'v1; MemRegOff{'v; 'off};
   store_tuple{'v; add{'off; word_size}; 'tl; 'rest}}}}

prim_rw unfold_store_tuple_nil {| reduce |} :
   store_tuple{'v; 'off; AllocTupleNil; 'rest}
   <-->
   'rest

doc docoff

dform store_tuple_df1 : store_tuple{'v; 'tuple; 'rest} =
   bf["store_tuple[ "] slot{'v} `", " slot{'tuple} bf[" ]"] hspace slot{'rest}

dform store_tuple_df2 : store_tuple{'v; 'off; 'tuple; 'rest} =
    bf["store_tuple[ "] slot{'v} `", " slot{'off} `", " slot{'tuple} bf[" ]"] hspace slot{'rest}

doc <:doc<
   @begin[doc]
   Terms used to reverse the order of the atoms in tuples.
   @end[doc]
>>
declare reverse_tuple{'tuple}
declare reverse_tuple{'dst; 'src}

prim_rw unfold_reverse_tuple {| reduce |} :
   reverse_tuple{'tuple}
   <-->
   reverse_tuple{AllocTupleNil; 'tuple}

prim_rw reduce_reverse_tuple_cons {| reduce |} :
   reverse_tuple{'dst; AllocTupleCons{'a; 'rest}}
   <-->
   reverse_tuple{AllocTupleCons{'a; 'dst}; 'rest}

prim_rw reduce_reverse_tuple_nil {| reduce |} :
   reverse_tuple{'dst; AllocTupleNil}
   <-->
   'dst

doc docoff

dform reverse_tuple_df1 : reverse_tuple{'tuple} =
   bf["reverse_tuple[ "] slot{'tuple} bf[" ]"]

dform reverse_tuple_df2 : reverse_tuple{'dst; 'src} =
   bf["reverse_tuple[ src = "] slot{'src} bf[" dst = "] slot{'dst} bf[" ]"]

(************************************************************************
 * Arguments.
 *)

doc <:doc<
   @begin[doc]
   Reverse the order of arguments.
   @end[doc]
>>
declare reverse_args{'args}
declare reverse_args{'args1; 'args2}

prim_rw unfold_reverse_args {| reduce |} :
   reverse_args{'args}
   <-->
   reverse_args{AsmArgNil; 'args}

prim_rw reduce_reverse_args_cons {| reduce |} :
   reverse_args{'args; AsmArgCons{'a; 'rest}}
   <-->
   reverse_args{AsmArgCons{'a; 'args}; 'rest}

prim_rw reduce_reverse_args_nil {| reduce |} :
   reverse_args{'args; AsmArgNil}
   <-->
   'args

doc docoff

dform reverse_args_df1 : reverse_args{'args} =
   bf["reverse_args[ "] slot{'args} bf[" ]"]

dform reverse_args_df2 : reverse_args{'dst; 'src} =
   bf["reverse_args[ src = "] slot{'src} bf[" dst = "] slot{'dst} bf[" ]"]

doc <:doc<
   @begin[doc]
   Copy the arguments into registers.
   @end[doc]
>>
declare copy_args{'args; v. 'e['v]}
declare copy_args{'args1; 'args2; v. 'e['v]}

prim_rw unfold_copy_args {| reduce |} :
   copy_args{'args; v. 'e['v]}
   <-->
   copy_args{AsmArgNil; 'args; v. 'e['v]}

prim_rw reduce_copy_args_cons {| reduce |} :
   copy_args{'dst; AsmArgCons{'a; 'rest}; v. 'e['v]}
   <-->
   Mov{'a; arg.
   copy_args{AsmArgCons{Register{'arg}; 'dst}; 'rest; v. 'e['v]}}

prim_rw reduce_copy_args_nil {| reduce |} :
   copy_args{'dst; AsmArgNil; v. 'e['v]}
   <-->
   'e[reverse_args{'dst}]

doc docoff

dform copy_args_df1 : copy_args{'args; v. 'e} =
   bf["let "] slot{'v} bf[" = copy_args[ "] slot{'args} bf[" ] in"] hspace slot{'e}

dform copy_args_df2 : copy_args{'dst; 'src; v. 'e} =
   bf["let "] slot{'v} bf[" = copy_args[ src = "] slot{'src} bf[" dst = "] slot{'dst} bf[" ] in"] hspace slot{'e}

doc <:doc<
   @begin[doc]
   Assemble function arguments.
   @end[doc]
>>
prim_rw asm_arg_cons {| reduce |} :
   ASM{ArgCons{'a; 'rest}; 'args; v. 'e['v]}
   <-->
   ASM{'a; arg.
   ASM{'rest; AsmArgCons{'arg; 'args}; v. 'e['v]}}

prim_rw asm_arg_nil {| reduce |} :
   ASM{ArgNil; 'args; v. 'e['v]}
   <-->
   'e[reverse_args{'args}]

(************************************************************************
 * Atoms
 *)

doc <:doc< 
   @begin[doc]
   @modsection{Code generation}
   In our runtime, integers are shifted to the left and use the upper
   31 bits only. The least significant bit is set to 1, so that we can
   distinguish between integers and pointers.

   @modsubsection{Atoms}
   Booleans are translated to integers. We use the standard encodings,
   0 for false and 1 for true, which in our integer representation
   translate to 1 and 3, respectively.
   @end[doc]
>>
prim_rw asm_atom_false {| reduce |} :
   ASM{AtomFalse; v. 'e['v]}
   <-->
   'e[ImmediateNumber[1:n]]

prim_rw asm_atom_true {| reduce |} :
   ASM{AtomTrue; v. 'e['v]}
   <-->
  'e[ImmediateNumber[3:n]]

doc <:doc< 
   @begin[doc]
   Integers are adjusted for our runtime representation.
   @end[doc]
>>
prim_rw asm_atom_int {| reduce |} :
   ASM{AtomInt[i:n]; v. 'e['v]}
   <-->
   'e[ImmediateNumber{add{mul{number[i:n]; number[2:n]}; number[1:n]}}]

doc <:doc< 
   @begin[doc]
   Variables are translated to registers.
   @end[doc]
>>
prim_rw asm_atom_var {| reduce |} :
   ASM{AtomVar{'v1}; v2. 'e['v2]}
   <-->
   'e[Register{'v1}]

doc <:doc< 
   @begin[doc]
   Function labels become labels.
   @end[doc]
>>
prim_rw asm_atom_fun_var {| reduce |} :
   ASM{AtomFunVar{'R; Label[label:t]}; v2. 'e['v2]}
   <-->
   'e[ImmediateCLabel[label:t]{'R}]

doc <:doc< 
   @begin[doc]
   Functions are assembled.
   @end[doc]
>>
prim_rw asm_atom_fun {| reduce |} :
   ASM{AtomFun{v. 'e['v]}}
   <-->
   LabelFun{v. ASM{'e['v]}}

doc <:doc< 
   @begin[doc]
   Binary operators are translated to a sequence of assembly
   instructions that implement that operation.
   Note that each operation is followed by adjusting
   the result so that it conforms with our 31-bit
   integer representation.
   @end[doc]
>>
prim_rw asm_atom_binop_add {| reduce |} :
   ASM{AtomBinop{AddOp; 'a1; 'a2}; v. 'e['v]}
   <-->
   Comment["asm_atom_binop_add"]{
   ASM{'a1; v1.
   ASM{'a2; v2.
   Inst2["add"]{'v2; 'v1; sum_tmp.
   Inst1["dec"]{Register{'sum_tmp}; sum.
   'e[Register{'sum}]}}}}}

prim_rw asm_atom_binop_sub {| reduce |} :
   ASM{AtomBinop{SubOp; 'a1; 'a2}; v. 'e['v]}
   <-->
   Comment["asm_atom_binop_sub"]{
   ASM{'a1; v1.
   ASM{'a2; v2.
   Inst2["sub"]{'v2; 'v1; diff_tmp.
   Inst1["inc"]{Register{'diff_tmp}; diff.
   'e[Register{'diff}]}}}}}

doc <:doc< 
   @begin[doc]
   In multiplication and division we first obtain the
   standard integer representation, perform the appropriate
   operation, and adjust the result.
   @end[doc]
>>
prim_rw asm_atom_binop_mul {| reduce |} :
   ASM{AtomBinop{MulOp; 'a1; 'a2}; v. 'e['v]}
   <-->
   Comment["asm_atom_binop_mul"]{
   ASM{'a1; v1.
   ASM{'a2; v2.
   Shift["sar"]{ImmediateNumber[1:n]; 'v1; v1_int.
   Shift["sar"]{ImmediateNumber[1:n]; 'v2; v2_int.
   Inst2["imul"]{Register{'v1_int}; Register{'v2_int}; prod_tmp1.
   Shift["shl"]{ImmediateNumber[1:n]; Register{'prod_tmp1}; prod_tmp2.
   Inst2["or"]{ImmediateNumber[1:n]; Register{'prod_tmp2}; prod.
   'e[Register{'prod}]}}}}}}}}

prim_rw asm_atom_binop_div {| reduce |} :
   ASM{AtomBinop{DivOp; 'a1; 'a2}; v. 'e['v]}
   <-->
   Comment["asm_atom_binop_div"]{
   ASM{'a1; v1.
   ASM{'a2; v2.
   Shift["sar"]{ImmediateNumber[1:n]; 'v1; v1_tmp.
   Shift["sar"]{ImmediateNumber[1:n]; 'v2; v2_tmp.
   Mov{ImmediateNumber[0:n]; v3_tmp.
   Inst3["div"]{Register{'v2_tmp}; Register{'v1_tmp}; Register{'v3_tmp}; quot_tmp1, rem_tmp.
   Shift["shl"]{ImmediateNumber[1:n]; Register{'quot_tmp1}; quot_tmp2.
   Inst2["or"]{ImmediateNumber[1:n]; Register{'quot_tmp2}; quot1.
   'e[Register{'quot1}]}}}}}}}}}

doc <:doc< 
   @begin[doc]
   Assembling IR relational operators is a mapping to the appropriate
   condition codes. The operations themselves become assembly comparisons.
   @end[doc]
>>
prim_rw asm_eq  {| reduce |} : ASM{EqOp}  <--> CC["z"]
prim_rw asm_neq {| reduce |} : ASM{NeqOp} <--> CC["nz"]
prim_rw asm_lt  {| reduce |} : ASM{LtOp}  <--> CC["l"]
prim_rw asm_le  {| reduce |} : ASM{LeOp}  <--> CC["le"]
prim_rw asm_gt  {| reduce |} : ASM{GtOp}  <--> CC["g"]
prim_rw asm_ge  {| reduce |} : ASM{GeOp}  <--> CC["ge"]

prim_rw asm_atom_relop {| reduce |} :
   ASM{AtomRelop{'op; 'a1; 'a2}; v. 'e['v]}
   <-->
   Comment["asm_atom_relop"]{
   ASM{'a1; v1.
   ASM{'a2; v2.
   Cmp["cmp"]{'v1; 'v2;
   Mov{ImmediateNumber[0:n]; eqsrc.
   Set["set"]{ASM{'op}; Register{'eqsrc}; eqdst.
   'e[Register{'eqdst}]}}}}}}

(************************************************************************
 * Instructions.
 *)
doc <:doc<
   @begin[doc]
   Reserve memory.
   @end[doc]
>>
prim_rw asm_reserve_1 {| reduce |} :
   ASM{Reserve[reswords:n]{'params; 'e}}
   <-->
   Mov{ContextRegister["limit":t]; limit.
   Inst2["sub"]{ContextRegister["next":t]; Register{'limit}; bytes.
   Cmp["cmp"]{ImmediateNumber{mul{number[reswords:n]; word_size}}; Register{'bytes};
   Jcc["j"]{CC["b"];
      ASM{'params; AsmArgNil; v.
      AsmReserve[reswords:n]{'v}};
   ASM{'e}}}}}

prim_rw asm_reserve_2 {| reduce |} :
   ASM{Reserve[words:n]{'e}}
   <-->
   ASM{'e}

doc <:doc<
   @begin[doc]
   The translation of @tt[LetAtom] is straightforward: we
   first translate the atom a into an operand <<'v1>>, which is then moved
   into <<'v>>.
   @end[doc]
>>
prim_rw asm_let_atom {| reduce |} :
   ASM{LetAtom{'a; v. 'e['v]}}
   <-->
   Comment["asm_let_atom"]{
   ASM{'a; v1.
   Mov{'v1; v.
   ASM{'e['v]}}}}

doc <:doc<
   @begin[doc]
   Conditionals are translated into a comparison followed by
   a conditional branch.
   @end[doc]
>>
(* granicz: Shouldn't we compare against 1? *)
prim_rw asm_if_1 {| reduce |} :
   ASM{If{'a; 'e1; 'e2}}
   <-->
   Comment["asm_if_1"]{
   ASM{'a;  test.
   Cmp["cmp"]{ImmediateNumber[0:n]; 'test;
   Jcc["j"]{CC["z"]; ASM{'e2}; ASM{'e1}}}}}

doc <:doc<
   @begin[doc]
   If the condition is a relational operation, we carry over
   the relational operator to the conditional jump.
   @end[doc]
>>
prim_rw asm_if_2 {| reduce |} :
   ASM{If{AtomRelop{'op; 'a1; 'a2}; 'e1; 'e2}}
   <-->
   Comment["asm_if_2"]{
   ASM{'a1; v1.
   ASM{'a2; v2.
   Cmp["cmp"]{'v2; 'v1;
   Jcc["j"]{ASM{'op}; ASM{'e1}; ASM{'e2}}}}}}

doc <:doc<
   @begin[doc]
   Reading from the memory involves assembling the pointer to the
   appropriate block and the index within that block. We then fetch
   the value from the specified memory location and move it into <<'v>>.
   @end[doc]
>>
prim_rw asm_let_subscript_1 {| reduce |} :
   ASM{LetSubscript{'a1; 'a2; v. 'e['v]}}
   <-->
   Comment["asm_let_subscript"]{
   ASM{'a1; v1.
   ASM{'a2; v2.
   Mov{'v1; tuple.
   Mov{'v2; index_tmp.
   Shift["sar"]{ImmediateNumber[1:n]; Register{'index_tmp}; index.
   Mov{MemRegRegOffMul{'v1; 'index; number[0:n]; word_size}; v.
   ASM{'e['v]}}}}}}}}

prim_rw asm_let_subscript_2 {| reduce |} :
   ASM{LetSubscript{'a1; AtomInt[i:n]; v. 'e['v]}}
   <-->
   Comment["asm_let_subscript"]{
   ASM{'a1; v1.
   Mov{'v1; tuple.
   Mov{MemRegOff{'tuple; mul{number[i:n]; word_size}}; v.
   ASM{'e['v]}}}}}

doc <:doc<
   @begin[doc]
   Changing a memory location involves assembling the block pointer and
   the index within the block. The value to be written is assembled and
   moved into the specified memory location.
   @end[doc]
>>
(* granicz: we are not doing any bounds checking *)

prim_rw asm_set_subscript_1 {| reduce |} :
   ASM{SetSubscript{'a1; 'a2; 'a3; 'e}}
   <-->
   Comment["asm_set_subscript"]{
   ASM{'a1; v1.
   ASM{'a2; v2.
   Mov{'v1; tuple.
   Mov{'v2; index_tmp.
   Shift["sar"]{ImmediateNumber[1:n]; Register{'index_tmp}; index.
   ASM{'a3; v3.
   Inst2["mov"]{'v3; MemRegRegOffMul{'v1; 'index; number[0:n]; word_size};
   ASM{'e}}}}}}}}}

prim_rw asm_set_subscript_2 {| reduce |} :
   ASM{SetSubscript{'a1; AtomInt[i:n]; 'a3; 'e}}
   <-->
   Comment["asm_set_subscript"]{
   ASM{'a1; v1.
   Mov{'v1; tuple.
   ASM{'a3; v3.
   Inst2["mov"]{'v3; MemRegOff{'v1; mul{number[i:n]; word_size}};
   ASM{'e}}}}}}

doc <:doc<
   @begin[doc]
   Allocating a tuple involves obtaining a block from the store by 
   advancing the @bf[next] pointer by the size of the tuple 
   (plus its header), creating the header for the
   new block, and storing the tuple elements in that block.
   @end[doc]
>>
prim_rw asm_alloc_tuple {| reduce |} :
   ASM{LetTuple{Length[i:n]; 'tuple; v. 'e['v]}}
   <-->
   Comment["asm_alloc_tuple"]{
   Mov{ContextRegister["next":t]; v.
   Inst2["add"]{ImmediateNumber{mul{add{number[i:n]; number[1:n]}; word_size}}; ContextRegister["next":t];
   Inst2["mov"]{header[i:n]; MemReg{'v};
   Inst2["add"]{ImmediateNumber{word_size}; Register{'v}; p.
   store_tuple{'p; reverse_tuple{'tuple};
   ASM{'e['p]}}}}}}}

doc <:doc<
   @begin[doc]
   Allocating a closure is similar to 2-tuple allocation.
   @end[doc]
>>
prim_rw asm_let_closure {| reduce |} :
   ASM{LetClosure{'a1; 'a2; v. 'e['v]}}
   <-->
   Comment["asm_let_closure"]{
   Mov{ContextRegister["next":t]; v.
   Inst2["add"]{ImmediateNumber{mul{number[3:n]; word_size}}; ContextRegister["next":t];
   Inst2["mov"]{ header[2:n]; MemReg{'v};
   ASM{'a1; v1.
   ASM{'a2; v2.
   Inst2["mov"]{'v1; MemRegOff{'v; word_size};
   Inst2["mov"]{'v2; MemRegOff{'v; mul{number[2:n]; word_size}};
   Inst2["add"]{ImmediateNumber{word_size}; Register{'v}; p.
   ASM{'e['p]}}}}}}}}}}

doc <:doc<
   @begin[doc]
   Assembling tail-calls to IR functions involve assembling
   the function arguments and jumping to the appropriate
   function label.
   @end[doc]
>>
prim_rw asm_tailcall_direct {| reduce |} :
   ASM{TailCall{AtomFunVar{'R; Label[label:t]}; 'args}}
   <-->
   Comment["asm_tailcall_direct"]{
   ASM{'args; AsmArgNil; args1.
   copy_args{'args1; args2.
   Jmp["jmp"]{ImmediateLabel[label:t]{'R}; 'args2}}}}

prim_rw asm_tailcall_indirect {| reduce |} :
   ASM{TailCall{'a; 'args}}
   <-->
   Comment["asm_tailcall"]{
   ASM{'a;  closure_tmp.
   ASM{'args; AsmArgNil; args1.
   Mov{'closure_tmp; closure.
   Mov{MemRegOff[4:n]{'closure}; env.
   copy_args{'args1; args2.
   Jmp["jmp"]{MemReg{'closure}; AsmArgCons{Register{'env}; 'args2}}}}}}}}

doc <:doc<
   @begin[doc]
   An IR program is a set of recursive functions. These are
   assembled and identified by function labels.
   @end[doc]
>>
prim_rw asm_letrec {| reduce |} :
   ASM{LetRec{R1. 'fields['R1]; R2. 'e['R2]}}
   <-->
   Comment["asm_letrec"]{
   LabelRec{R1. ASM{'R1; 'fields['R1]}; R2. ASM{'e['R2]}}}

prim_rw asm_fields {| reduce |} :
   ASM{'R; Fields{'fields}}
   <-->
   ASM{'R; 'fields}

prim_rw asm_fun_def {| reduce |} :
   ASM{'R; FunDef{Label[label:t]; 'e; 'rest}}
   <-->
   LabelDef{LabelAsm[label:t]{'R}; ASM{'e}; ASM{'R; 'rest}}

prim_rw asm_end_def {| reduce |} :
   ASM{'R; EndDef}
   <-->
   LabelEnd

prim_rw asm_initialize {| reduce |} :
   ASM{Initialize{'e}}
   <-->
   Init{ASM{'e}}

(*
 * Cleanup.  It is debatiable whether we should have cleanup here...
 *)
doc <:doc< @docoff >>

prim_rw mem_reg_reg_off_mul_cleanup_1 {| reduce |} :
   MemRegRegOffMul[off:n, mul:n]{Register{'r1}; 'r2}
   <-->
   MemRegRegOffMul[off:n, mul:n]{'r1; 'r2}

prim_rw mem_reg_reg_off_mul_cleanup_2 {| reduce |} :
   MemRegRegOffMul[off:n, mul:n]{'r1; Register{'r2}}
   <-->
   MemRegRegOffMul[off:n, mul:n]{'r1; 'r2}

prim_rw mem_reg_reg_off_mul_cleanup_3 {| reduce |} :
   MemRegRegOffMul[off:n, mul:n]{'r1; ImmediateNumber[j:n]}
   <-->
   MemRegOff{'r1; add{mul{number[mul:n]; number[j:n]}; number[off:n]}}

prim_rw mem_reg_off_cleanup_1 {| reduce |} :
   MemRegOff[0:n]{'r}
   <-->
   MemReg{'r}

(*
 * Illegal operands.
 *)
declare invert_cc{'cc}

prim_rw invert_cc_z {| reduce |} :
   invert_cc{CC["z"]}
   <-->
   CC["z"]

prim_rw invert_cc_nz {| reduce |} :
   invert_cc{CC["nz"]}
   <-->
   CC["nz"]

prim_rw invert_cc_lt {| reduce |} :
   invert_cc{CC["l"]}
   <-->
   CC["ge"]

prim_rw invert_cc_le {| reduce |} :
   invert_cc{CC["le"]}
   <-->
   CC["g"]

prim_rw invert_cc_gt {| reduce |} :
   invert_cc{CC["g"]}
   <-->
   CC["le"]

prim_rw invert_cc_ge {| reduce |} :
   invert_cc{CC["ge"]}
   <-->
   CC["l"]

prim_rw cmp_cleanup {| reduce |} :
   Cmp[cmp_opcode:s]{'src1; ImmediateNumber[i:n]; Jcc[jcc_opcode:s]{'cc; 'rest1; 'rest2}}
   <-->
   Cmp[cmp_opcode:s]{ImmediateNumber[i:n]; 'src1; Jcc[jcc_opcode:s]{invert_cc{'cc}; 'rest1; 'rest2}}

dform invert_cc_df : invert_cc{'cc} =
   bf["invert "] slot{'cc}

(*
 * Register type.
 *)
declare register

doc docoff

dform register_df : register =
   bf["register"]

doc <:doc< 
   @begin[doc]
   The program is compilable if the assembly is compilable.
   @end[doc]
>>
interactive codegen_prog :
   sequent [m] { <H> >- compilable{ASM{'e}} } -->
   sequent [m] { <H> >- compilable{'e} }

doc <:doc< @docoff >>

(*
 * Assembler.
 *)
let codegenT =
   codegen_prog thenT rw reduceC 0

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
