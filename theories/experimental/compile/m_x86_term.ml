(*
 * ML functions for dealing with instructions.
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
 * @docoff
 *)
extends M_ir
extends M_x86_inst_type

open Lm_symbol

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.RefineError

open M_x86_inst_type

(*
 * Term operations.
 *)
let immediate_number_term = << ImmediateNumber[i:n] >>
let immediate_label_term = << ImmediateLabel[label:t]{'R} >>
let immediate_clabel_term = << ImmediateCLabel[label:t]{'R} >>
let register_term = << Register{'v} >>
let spill_memory_term = << SpillMemory{'spill} >>
let spill_register_term = << SpillRegister{'v; 'spill} >>
let context_register_term = << ContextRegister[reg:t] >>
let mem_reg_term = << MemReg{'r} >>
let mem_reg_off_term = << MemRegOff[i:n]{'r} >>
let mem_reg_reg_off_mul_term = << MemRegRegOffMul[off:n, mul:n]{'r1; 'r2} >>

let immediate_number_opname = opname_of_term immediate_number_term
let immediate_label_opname = opname_of_term immediate_label_term
let immediate_clabel_opname = opname_of_term immediate_clabel_term
let register_opname = opname_of_term register_term
let spill_memory_opname = opname_of_term spill_memory_term
let spill_register_opname = opname_of_term spill_register_term
let context_register_opname = opname_of_term context_register_term
let mem_reg_opname = opname_of_term mem_reg_term
let mem_reg_off_opname = opname_of_term mem_reg_off_term
let mem_reg_reg_off_mul_opname = opname_of_term mem_reg_reg_off_mul_term

let cc_term           = << CC["z"] >>
let cc_opname         = opname_of_term cc_term

let compilable_term   = << compilable{'t} >>
let mov_term          = << Mov{'src; dst. 'rest['dst]} >>
let spill_term        = << Spill[reg:s]{'src; dst. 'rest['dst]} >>
let inst1_term        = << Inst1["neg"]{'dst; 'rest} >>
let inst2_term        = << Inst2["mov"]{'src; 'dst; 'rest} >>
let inst3_term        = << Inst3["mul"]{'src1; 'src2; 'src3; dst2, dst3. 'rest['dst2; 'dst3]} >>
let shift_term        = << Shift["sar"]{'src; 'dst; 'rest} >>
let cmp_term          = << Cmp["test"]{'src1; 'src2; 'rest} >>
let set_term          = << Set["set"]{'cc; 'dst; 'rest} >>
let asm_arg_cons_term = << AsmArgCons{'a; 'rest} >>
let asm_arg_nil_term  = << AsmArgNil >>
let jmp_term          = << Jmp["jmp"]{'label; 'args} >>
let jcc_term          = << Jcc["j"]{'cc; 'rest1; 'rest2} >>
let asm_reserve_term  = << AsmReserve[words:n]{'params} >>
let comment_term      = << Comment[comment:s]{'rest} >>
let init_term         = << Init{'rest} >>
let label_asm_term    = << LabelAsm[label:t]{'R} >>
let label_rec_term    = << LabelRec{R1. 'fields['R1]; R2. 'rest['R2]} >>
let label_def_term    = << LabelDef{'label; 'code; 'rest} >>
let label_end_term    = << LabelEnd >>
let label_fun_term    = << LabelFun{v. 'insts['v]} >>

let compilable_opname    = opname_of_term compilable_term
let mov_opname           = opname_of_term mov_term
let spill_opname         = opname_of_term spill_term
let inst1_opname         = opname_of_term inst1_term
let inst2_opname         = opname_of_term inst2_term
let inst3_opname         = opname_of_term inst3_term
let shift_opname         = opname_of_term shift_term
let cmp_opname           = opname_of_term cmp_term
let set_opname           = opname_of_term set_term
let asm_arg_cons_opname  = opname_of_term asm_arg_cons_term
let asm_arg_nil_opname   = opname_of_term asm_arg_nil_term
let jmp_opname           = opname_of_term jmp_term
let jcc_opname           = opname_of_term jcc_term
let asm_reserve_opname   = opname_of_term asm_reserve_term
let comment_opname       = opname_of_term comment_term
let init_opname          = opname_of_term init_term
let label_asm_opname     = opname_of_term label_asm_term
let label_rec_opname     = opname_of_term label_rec_term
let label_def_opname     = opname_of_term label_def_term
let label_end_opname     = opname_of_term label_end_term
let label_fun_opname     = opname_of_term label_fun_term

(************************************************************************
 * Destruction.
 *)

(*
 * Condition codes.
 *)
let dest_cc t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = List.map dest_param params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [String cc], [] ->
            (match cc with
                "l" -> LT
              | "le" -> LE
              | "z"  -> EQ
              | "nz" -> NEQ
              | "g" -> GT
              | "ge" -> GE
              | "b"  -> ULT
              | "be" -> ULE
              | "a"  -> UGT
              | "ae" -> UGE
              | _ -> raise (RefineError ("dest_cc", StringStringError ("bogus condition code", cc))))
       | _ ->
            raise (RefineError ("dest_cc", StringTermError ("bogus condition code", t)))

let mk_cc = function
   LT -> "l"
 | LE -> "le"
 | EQ -> "z"
 | NEQ -> "nz"
 | GT -> "g"
 | GE -> "ge"
 | ULT -> "b"
 | ULE -> "be"
 | UGT -> "a"
 | UGE -> "ae"

let invert_cc = function
   LT -> GE
 | LE -> GT
 | EQ -> NEQ
 | NEQ -> EQ
 | GT -> LE
 | GE -> LT
 | ULT -> UGE
 | ULE -> UGT
 | UGT -> ULE
 | UGE -> ULT

(*
 * Opcodes.
 *)
let dest_spill_opcode = function
   "set" -> SpillSet
 | "get" -> SpillGet
 | "copy" -> SpillCopy
 | s -> raise (RefineError ("dest_spill_opcode", StringStringError ("bogus spill opcode", s)))

let mk_spill_opcode = function
   SpillSet -> "set"
 | SpillGet -> "get"
 | SpillCopy -> "copy"

let dest_inst1_opcode = function
   "neg" -> NEG
 | "not" -> NOT
 | "inc" -> INC
 | "dec" -> DEC
 | s -> raise (RefineError ("dest_inst1_opcode", StringStringError ("bogus inst1 opcode", s)))

let mk_inst1_opcode = function
   NEG -> "neg"
 | NOT -> "not"
 | INC -> "inc"
 | DEC -> "dec"

let dest_inst2_opcode = function
   "mov" -> MOV
 | "add" -> ADD
 | "lea" -> LEA
 | "sub" -> SUB
 | "imul" -> IMUL
 | "and" -> AND
 | "or" -> OR
 | "xor" -> XOR
 | s -> raise (RefineError ("dest_inst2_opcode", StringStringError ("bogus inst2 opcode", s)))

let mk_inst2_opcode = function
   MOV -> "mov"
 | ADD -> "add"
 | LEA -> "lea"
 | SUB -> "sub"
 | IMUL -> "imul"
 | AND  -> "and"
 | OR   -> "or"
 | XOR  -> "xor"

let dest_inst3_opcode = function
   "mul" -> MUL
 | "div" -> DIV
 | s -> raise (RefineError ("dest_instm_opcode", StringStringError ("bogus instm opcode", s)))

let mk_inst3_opcode = function
   MUL -> "mul"
 | DIV -> "div"

let dest_shift_opcode = function
   "sar" -> SAR
 | "shl" -> SHL
 | "shr" -> SHR
 | s -> raise (RefineError ("dest_shift_opcode", StringStringError ("bogus shift opcode", s)))

let mk_shift_opcode = function
   SAR -> "sar"
 | SHL -> "shl"
 | SHR -> "shr"

let dest_set_opcode = function
   "set" -> SET
 | s -> raise (RefineError ("dest_set_opcode", StringStringError ("bogus set opcode", s)))

let mk_set_opcode = function
   SET -> "set"

let dest_cmp_opcode = function
   "cmp" -> CMP
 | "test" -> TEST
 | s -> raise (RefineError ("dest_cmp_opcode", StringStringError ("bogus cmp opcode", s)))

let mk_cmp_opcode = function
   CMP -> "cmp"
 | TEST -> "test"

let dest_jmp_opcode = function
   "jmp" -> JMP
 | s -> raise (RefineError ("dest_jmp_opcode", StringStringError ("bogus jmp opcode", s)))

let mk_jmp_opcode = function
   JMP -> "jmp"

let dest_jcc_opcode = function
   "j" -> JCC
 | s -> raise (RefineError ("dest_jcc_opcode", StringStringError ("bogus jcc opcode", s)))

let mk_jcc_opcode = function
   JCC -> "j"

(*
 * Get the name of a label.
 *)
let init_label = Lm_symbol.add ".init"

let is_init_label_asm = function
   LabelAsm (v, _) ->
      Lm_symbol.eq v init_label
 | _ ->
      false

let label_of_asm_label v1 v2 =
   let r = string_of_symbol v2 in
   let s = string_of_symbol v1 in
   let s = r ^ "." ^ s in
      Lm_symbol.add s

let label_of_label_asm = function
   LabelAsm (v1, v2) ->
      label_of_asm_label v1 v2
 | _ ->
      raise (RefineError ("symbol_of_label_asm_term", StringError "not a label term"))

(*
 * Operands.
 *)
let int32_of_num i =
   Int32.of_string (Lm_num.string_of_num i)

let dest_spill_reg t =
   if is_var_term t then
      SpillRegRegister (dest_var t)
   else
      let { term_op = op; term_terms = bterms } = dest_term t in
      let { op_name = op; op_params = params } = dest_op op in
      let bterms = List.map dest_bterm bterms in
         match params, bterms with
            [], [{ bvars = []; bterm = v };
                 { bvars = []; bterm = spill }]
            when Opname.eq op spill_register_opname ->
               SpillRegSpill (dest_var v, dest_var spill)
          | _ ->
               raise (RefineError ("dest_spill_reg", StringTermError ("not a valid spill register", t)))

let dest_operand_aux dest_reg t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = List.map dest_param params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         (* ImmediateNumber *)
         [Number i], []
         when Opname.eq op immediate_number_opname ->
            ImmediateNumber (int32_of_num i)

         (* ImmediateLabel *)
       | [Token label], [{ bvars = []; bterm = t }]
         when Opname.eq op immediate_label_opname ->
            ImmediateLabel (Lm_symbol.add label, dest_var t)

         (* ImmediateCLabel *)
       | [Token label], [{ bvars = []; bterm = t }]
         when Opname.eq op immediate_clabel_opname ->
            ImmediateCLabel (Lm_symbol.add label, dest_var t)

         (* Register *)
       | [], [{ bvars = []; bterm = t }]
         when Opname.eq op register_opname ->
            Register (dest_reg t)

         (* SpillMemory *)
       | [], [{ bvars = []; bterm = spill }]
         when Opname.eq op spill_memory_opname ->
            SpillMemory (dest_var spill)

         (* SpillRegister *)
       | [], [{ bvars = []; bterm = v };
              { bvars = []; bterm = spill }]
         when Opname.eq op spill_register_opname ->
            SpillRegister (dest_var v, dest_var spill)

         (* ContextRegister *)
       | [Token s], []
         when Opname.eq op context_register_opname ->
            ContextRegister (Lm_symbol.add s)

         (* MemReg *)
       | [], [{ bvars = []; bterm = t }]
         when Opname.eq op mem_reg_opname ->
            MemReg (dest_reg t)

         (* MemRegOff *)
       | [Number i], [{ bvars = []; bterm = t }]
         when Opname.eq op mem_reg_off_opname ->
            MemRegOff (dest_reg t, int32_of_num i)

         (* MemRegRegOffMul *)
       | [Number off; Number mul], [{ bvars = []; bterm = t1 };
                                    { bvars = []; bterm = t2 }]
         when Opname.eq op mem_reg_off_opname ->
            MemRegRegOffMul (dest_reg t1,
                             dest_reg t2,
                             int32_of_num off,
                             int32_of_num mul)

       | _ ->
            raise (RefineError ("dest_operand", StringTermError ("not an x86 operand", t)))

let dest_operand_term op =
   dest_operand_aux dest_var op

let dest_operand_spill op =
   dest_operand_aux dest_spill_reg op

(*
 * Make sure it is a memory operand.
 *)
let dest_mem_operand_term dest_reg t =
   match dest_operand_aux dest_reg t with
      ImmediateNumber _
    | ImmediateCLabel _
    | SpillRegister _
    | Register _ ->
         raise (RefineError ("dest_mem_operand_term", StringTermError ("not a memory operand", t)))
    | op ->
         op

let dest_reg_operand_term dest_reg t =
   match dest_operand_aux dest_reg t with
      Register r ->
         r
    | _ ->
         raise (RefineError ("dest_reg_operand_term", StringTermError ("not a register operand", t)))

(*
 * Arguments to jmp/jcc
 *)
let rec dest_arg_term t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = List.map dest_param params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [], [{ bvars = []; bterm = arg }; { bvars = []; bterm = rest }]
         when Opname.eq op asm_arg_cons_opname ->
            arg :: dest_arg_term rest
       | [], []
         when Opname.eq op asm_arg_nil_opname ->
            []
       | _ ->
            raise (RefineError ("dest_arg_term", StringTermError ("unexpected argument", t)))

let dest_operand_args dest_reg t =
   List.map (dest_reg_operand_term dest_reg) (dest_arg_term t)

(*
 * Break apart the instruction.
 *)
let dest_inst_aux dest_reg dest_rest t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = List.map dest_param params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [], [{ bvars = []; bterm = rest }]
         when Opname.eq op compilable_opname ->
            Compilable (dest_rest rest)

         (* Mov *)
       | [], [{ bvars = []; bterm = src };
              { bvars = [dst]; bterm = rest }]
         when Opname.eq op mov_opname ->
            Mov (dest_operand_aux dest_reg src,
                 dst, dest_rest rest)

         (* Spill *)
       | [String opcode], [{ bvars = [];  bterm = src };
                           { bvars = [dst]; bterm = rest }]
         when Opname.eq op spill_opname ->
            Spill (dest_spill_opcode opcode,
                   dest_operand_aux dest_reg src,
                   dst, dest_rest rest)

         (* Inst1 *)
       | [String opcode], [{ bvars = []; bterm = dst };
                           { bvars = []; bterm = rest }]
         when Opname.eq op inst1_opname ->
            Inst1Mem (dest_inst1_opcode opcode,
                      dest_mem_operand_term dest_reg dst,
                      dest_rest rest)
       | [String opcode], [{ bvars = []; bterm = src };
                           { bvars = [dst]; bterm = rest }]
         when Opname.eq op inst1_opname ->
            Inst1Reg (dest_inst1_opcode opcode,
                      dest_reg_operand_term dest_reg src,
                      dst, dest_rest rest)

         (* Inst2 *)
       | [String opcode], [{ bvars = []; bterm = src };
                           { bvars = []; bterm = dst };
                           { bvars = []; bterm = rest }]
         when Opname.eq op inst2_opname ->
            Inst2Mem (dest_inst2_opcode opcode,
                      dest_operand_aux dest_reg src,
                      dest_mem_operand_term dest_reg dst,
                      dest_rest rest)
       | [String opcode], [{ bvars = []; bterm = src1 };
                           { bvars = []; bterm = src2 };
                           { bvars = [dst]; bterm = rest }]
         when Opname.eq op inst2_opname ->
            Inst2Reg (dest_inst2_opcode opcode,
                      dest_operand_aux dest_reg src1,
                      dest_reg_operand_term dest_reg src2,
                      dst, dest_rest rest)

         (* Inst3 *)
       | [String opcode], [{ bvars = []; bterm = src1 };
                           { bvars = []; bterm = src2 };
                           { bvars = []; bterm = src3 };
                           { bvars = [dst1; dst2]; bterm = rest }]
         when Opname.eq op inst3_opname ->
            Inst3Reg (dest_inst3_opcode opcode,
                      dest_operand_aux dest_reg src1,
                      dest_reg_operand_term dest_reg src2,
                      dest_reg_operand_term dest_reg src3,
                      dst1, dst2, dest_rest rest)

         (* Shift *)
       | [String opcode], [{ bvars = []; bterm = src };
                           { bvars = []; bterm = dst };
                           { bvars = []; bterm = rest }]
         when Opname.eq op shift_opname ->
            ShiftMem (dest_shift_opcode opcode,
                      dest_operand_aux dest_reg src,
                      dest_mem_operand_term dest_reg dst,
                      dest_rest rest)
       | [String opcode], [{ bvars = []; bterm = src1 };
                           { bvars = []; bterm = src2 };
                           { bvars = [dst]; bterm = rest }]
         when Opname.eq op shift_opname ->
            ShiftReg (dest_shift_opcode opcode,
                      dest_operand_aux dest_reg src1,
                      dest_reg_operand_term dest_reg src2,
                      dst, dest_rest rest)

         (* Cmp *)
       | [String opcode], [{ bvars = []; bterm = src1 };
                           { bvars = []; bterm = src2 };
                           { bvars = []; bterm = rest }]
         when Opname.eq op cmp_opname ->
            Cmp (dest_cmp_opcode opcode,
                 dest_operand_aux dest_reg src1,
                 dest_operand_aux dest_reg src2,
                 dest_rest rest)

         (* Set *)
       | [String opcode], [{ bvars = []; bterm = cc };
                           { bvars = []; bterm = dst };
                           { bvars = []; bterm = rest }]
         when Opname.eq op set_opname ->
            SetMem (dest_set_opcode opcode,
                    dest_cc cc,
                    dest_mem_operand_term dest_reg dst,
                    dest_rest rest)
       | [String opcode], [{ bvars = []; bterm = cc };
                           { bvars = []; bterm = src };
                           { bvars = [dst]; bterm = rest }]
         when Opname.eq op set_opname ->
            SetReg (dest_set_opcode opcode,
                    dest_cc cc,
                    dest_reg_operand_term dest_reg src,
                    dst, dest_rest rest)

         (* Jmp *)
       | [String opcode], [{ bvars = []; bterm = f };
                           { bvars = []; bterm = args }]
         when Opname.eq op jmp_opname ->
            Jmp (dest_jmp_opcode opcode,
                 dest_operand_aux dest_reg f,
                 dest_operand_args dest_reg args)

         (* Jcc *)
       | [String opcode], [{ bvars = []; bterm = cc };
                           { bvars = []; bterm = rest1 };
                           { bvars = []; bterm = rest2 }]
         when Opname.eq op jcc_opname ->
            Jcc (dest_jcc_opcode opcode,
                 dest_cc cc,
                 dest_rest rest1,
                 dest_rest rest2)

         (* Comment *)
       | [String comment], [{ bvars = []; bterm = rest }]
         when Opname.eq op comment_opname ->
            Comment (comment, dest_rest rest)

         (* Reserve *)
       | [Number words], [{ bvars = []; bterm = params }]
         when Opname.eq op asm_reserve_opname ->
            Reserve (int32_of_num words, dest_operand_args dest_reg params)

         (* Init *)
       | [], [{ bvars = []; bterm = rest }]
         when Opname.eq op init_opname ->
            Init (dest_rest rest)

         (* LabelAsm *)
       | [Token label], [{ bvars = []; bterm = v }]
         when Opname.eq op label_asm_opname ->
            LabelAsm (Lm_symbol.add label, dest_var v)

         (* LabelRec *)
       | [], [{ bvars = [v1]; bterm = fields };
              { bvars = [v2]; bterm = rest }]
         when Opname.eq op label_rec_opname ->
            LabelRec (v1, dest_rest fields, v2, dest_rest rest)

         (* LabelDef *)
       | [], [{ bvars = []; bterm = label };
              { bvars = []; bterm = code };
              { bvars = []; bterm = rest }]
         when Opname.eq op label_def_opname ->
            LabelDef (dest_rest label, dest_rest code, dest_rest rest)

         (* LabelEnd *)
       | [], []
         when Opname.eq op label_end_opname ->
            LabelEnd

         (* LabelFun *)
       | [], [{ bvars = [v]; bterm = code }]
         when Opname.eq op label_fun_opname ->
            LabelFun (v, dest_rest code)

       | _ ->
            raise (RefineError ("not an x86 instruction", TermError t))

let dest_inst_term t =
   dest_inst_aux dest_var (fun rest -> rest) t

let dest_inst_spill t =
   dest_inst_aux dest_spill_reg (fun rest -> rest) t

let rec dest_inst t =
   Inst (dest_inst_aux dest_var dest_inst t)

(*
 * Get the operands of the term in a list.
 *)
let operands_of_inst inst =
   match inst with
      Compilable _
    | Comment    _
    | Init       _
    | LabelAsm   _
    | LabelFun   _
    | LabelRec   _
    | LabelDef   _
    | LabelEnd
    | Jcc _ ->
         []
    | IMov (src, _, _) ->
         [Register src]
    | Mov (src, _, _)
    | Spill (_, src, _, _) ->
         [src]
    | Inst1Mem (_, dst, _)
    | SetMem (_, _, dst, _) ->
         [dst]
    | Inst1Reg (_, src, dst, _)
    | SetReg (_, _, src, dst, _) ->
         [Register src; Register dst]
    | Inst2Mem (_, src, dst, _)
    | ShiftMem (_, src, dst, _)
    | Cmp (_, src, dst, _) ->
         [dst; src]
    | Inst2Reg (_, src1, src2, dst, _)
    | ShiftReg (_, src1, src2, dst, _) ->
         [src1; Register src2; Register dst]
    | Inst3Reg (_, src1, src2, src3, dst1, dst2, _) ->
         [src1; Register src2; Register src3; Register dst1; Register dst2]
    | Reserve (_, args) ->
         List.map (fun v -> Register v) args
    | Jmp (_, f, args) ->
         f :: List.map (fun v -> Register v) args

(*
 * Address of the rest of the instruction.
 *)
let next_inst inst =
   match inst with
      Compilable t
    | Comment (_, t)
    | Init t
    | LabelFun (_, t) ->
         0, t
    | IMov (_, _, t)
    | Mov (_, _, t)
    | Spill (_, _, _, t)
    | Inst1Mem (_, _, t)
    | LabelRec (_, t, _, _)
    | LabelDef (_, t, _) ->
         1, t
    | Inst1Reg (_, _, _, t)
    | Inst2Mem (_, _, _, t)
    | ShiftMem (_, _, _, t)
    | Cmp (_, _, _, t)
    | SetMem (_, _, _, t) ->
         2, t
    | SetReg (_, _, _, _, t)
    | Inst2Reg (_, _, _, _, t)
    | ShiftReg (_, _, _, _, t) ->
         3, t
    | Inst3Reg (_, _, _, _, _, _, t) ->
         4, t
    | Jmp _
    | Jcc _
    | Reserve _
    | LabelEnd
    | LabelAsm _ ->
         raise (RefineError ("addr_of_rest", StringError "no rest for JMP"))

(************************************************************************
 * Construction.
 *)

(*
 * Make a number.
 *)
let num_of_int32 i =
   Lm_num.num_of_string (Int32.to_string i)

(*
 * A generic term constructor.
 *)
let mk_term opname params bterms =
   let bterms = List.map make_bterm bterms in
   let params = List.map make_param params in
   let op = mk_op opname params in
      mk_term op bterms

(*
 * Spill register.
 *)
let mk_spill_reg_term op =
   match op with
      SpillRegRegister v ->
         mk_term register_opname (**)
            []
            [{ bvars = []; bterm = mk_var_term v }]
    | SpillRegSpill (v1, v2) ->
         let t =
            mk_term spill_register_opname (**)
               []
               [{ bvars = []; bterm = mk_var_term v1 };
                { bvars = []; bterm = mk_var_term v2 }]
         in
            mk_term register_opname (**)
               []
               [{ bvars = []; bterm = t }]

(*
 * Operands.
 *)
let mk_operand_aux mk_reg op =
   match op with
      ImmediateNumber i ->
         mk_term immediate_number_opname (**)
            [Number (num_of_int32 i)]
            []
    | ImmediateLabel (v1, v2) ->
         mk_term immediate_label_opname (**)
            [Token (string_of_symbol v1)]
            [{ bvars = []; bterm = mk_var_term v2 }]
    | ImmediateCLabel (v1, v2) ->
         mk_term immediate_clabel_opname (**)
            [Token (string_of_symbol v1)]
            [{ bvars = []; bterm = mk_var_term v2 }]
    | Register v ->
         mk_term register_opname (**)
            []
            [{ bvars = []; bterm = mk_reg v }]
    | SpillMemory v ->
         mk_term spill_memory_opname (**)
            []
            [{ bvars = []; bterm = mk_var_term v }]
    | SpillRegister (v1, v2) ->
         mk_term spill_register_opname (**)
            []
            [{ bvars = []; bterm = mk_var_term v1 };
             { bvars = []; bterm = mk_var_term v2 }]
    | ContextRegister v ->
         mk_term context_register_opname (**)
            []
            [{ bvars = []; bterm = mk_var_term v }]
    | MemReg v ->
         mk_term mem_reg_opname (**)
            []
            [{ bvars = []; bterm = mk_reg v }]
    | MemRegOff (v, off) ->
         mk_term mem_reg_off_opname (**)
            [Number (num_of_int32 off)]
            [{ bvars = []; bterm = mk_reg v }]
    | MemRegRegOffMul (v1, v2, off, mul) ->
         mk_term mem_reg_reg_off_mul_opname (**)
            [Number (num_of_int32 off);
             Number (num_of_int32 mul)]
            [{ bvars = []; bterm = mk_reg v1 };
             { bvars = []; bterm = mk_reg v2 }]

let mk_operand_term = mk_operand_aux mk_var_term
let mk_operand_spill = mk_operand_aux mk_spill_reg_term

let mk_cc_term cc =
   mk_string_term cc_opname (mk_cc cc)

(*
 * Arguments.
 *)
let rec mk_args_term mk_reg args =
   match args with
      arg :: args ->
         mk_term asm_arg_cons_opname (**)
            []
            [{ bvars = []; bterm = mk_reg arg };
             { bvars = []; bterm = mk_args_term mk_reg args }]
    | [] ->
         asm_arg_nil_term

(*
 * Instructions.
 *)
let mk_inst_aux mk_reg mk_rest inst =
   match inst with
      Mov (src, dst, rest) ->
         mk_term mov_opname (**)
            []
            [{ bvars = []; bterm = mk_operand_aux mk_reg src };
             { bvars = [dst]; bterm = mk_rest rest }]
    | Spill (opcode, src, dst, rest) ->
         mk_term spill_opname (**)
            [String (mk_spill_opcode opcode)]
            [{ bvars = []; bterm = mk_operand_aux mk_reg src };
             { bvars = [dst]; bterm = mk_rest rest }]
    | Inst1Mem (opcode, dst, rest) ->
         mk_term inst1_opname (**)
            [String (mk_inst1_opcode opcode)]
            [{ bvars = []; bterm = mk_operand_aux mk_reg dst };
             { bvars = []; bterm = mk_rest rest }]
    | Inst1Reg (opcode, src, dst, rest) ->
         mk_term inst1_opname (**)
            [String (mk_inst1_opcode opcode)]
            [{ bvars = []; bterm = mk_reg src };
             { bvars = [dst]; bterm = mk_rest rest }]
    | Inst2Mem (opcode, src, dst, rest) ->
         mk_term inst2_opname (**)
            [String (mk_inst2_opcode opcode)]
            [{ bvars = []; bterm = mk_operand_aux mk_reg src };
             { bvars = []; bterm = mk_operand_aux mk_reg dst };
             { bvars = []; bterm = mk_rest rest }]
    | Inst2Reg (opcode, src1, src2, dst, rest) ->
         mk_term inst2_opname (**)
            [String (mk_inst2_opcode opcode)]
            [{ bvars = []; bterm = mk_operand_aux mk_reg src1 };
             { bvars = []; bterm = mk_reg src2 };
             { bvars = [dst]; bterm = mk_rest rest }]
    | Inst3Reg (opcode, src1, src2, src3, dst2, dst3, rest) ->
         mk_term inst3_opname (**)
            [String (mk_inst3_opcode opcode)]
            [{ bvars = []; bterm = mk_operand_aux mk_reg src1 };
             { bvars = []; bterm = mk_reg src2 };
             { bvars = []; bterm = mk_reg src3 };
             { bvars = [dst2; dst3]; bterm = mk_rest rest }]
    | ShiftMem (opcode, src, dst, rest) ->
         mk_term shift_opname (**)
            [String (mk_shift_opcode opcode)]
            [{ bvars = []; bterm = mk_operand_aux mk_reg src };
             { bvars = []; bterm = mk_operand_aux mk_reg dst };
             { bvars = []; bterm = mk_rest rest }]
    | ShiftReg (opcode, src1, src2, dst, rest) ->
         mk_term shift_opname (**)
            [String (mk_shift_opcode opcode)]
            [{ bvars = []; bterm = mk_operand_aux mk_reg src1 };
             { bvars = []; bterm = mk_reg src2 };
             { bvars = [dst]; bterm = mk_rest rest }]
    | Cmp (opcode, src1, src2, rest) ->
         mk_term cmp_opname (**)
            [String (mk_cmp_opcode opcode)]
            [{ bvars = []; bterm = mk_operand_aux mk_reg src1 };
             { bvars = []; bterm = mk_operand_aux mk_reg src2 };
             { bvars = []; bterm = mk_rest rest }]
    | SetMem (opcode, cc, dst, rest) ->
         mk_term set_opname (**)
            [String (mk_set_opcode opcode)]
            [{ bvars = []; bterm = mk_cc_term cc };
             { bvars = []; bterm = mk_operand_aux mk_reg dst };
             { bvars = []; bterm = mk_rest rest }]
    | SetReg (opcode, cc, src, dst, rest) ->
         mk_term set_opname (**)
            [String (mk_set_opcode opcode)]
            [{ bvars = []; bterm = mk_cc_term cc };
             { bvars = []; bterm = mk_reg src };
             { bvars = [dst]; bterm = mk_rest rest }]
    | Jmp (opcode, f, args) ->
         mk_term jmp_opname (**)
            [String (mk_jmp_opcode opcode)]
            [{ bvars = []; bterm = mk_operand_aux mk_reg f };
             { bvars = []; bterm = mk_args_term mk_reg args }]
    | Jcc (opcode, cc, rest1, rest2) ->
         mk_term jcc_opname (**)
            [String (mk_jcc_opcode opcode)]
            [{ bvars = []; bterm = mk_cc_term cc };
             { bvars = []; bterm = mk_rest rest1 };
             { bvars = []; bterm = mk_rest rest2 }]
    | Reserve (words, args) ->
         mk_term asm_reserve_opname (**)
            [Number (num_of_int32 words)]
            [{ bvars = []; bterm = mk_args_term mk_reg args }]
    | Comment (s, rest) ->
         mk_term comment_opname (**)
            [String s]
            [{ bvars = []; bterm = mk_rest rest }]
    | Init rest ->
         mk_term init_opname (**)
            []
            [{ bvars = []; bterm = mk_rest rest }]
    | Compilable rest ->
         mk_term compilable_opname (**)
            []
            [{ bvars = []; bterm = mk_rest rest }]
    | LabelAsm (label, v) ->
         mk_term label_asm_opname (**)
            [Token (string_of_symbol label)]
            [{ bvars = []; bterm = mk_var_term v }]
    | LabelRec (v1, rest1, v2, rest2) ->
         mk_term label_rec_opname (**)
            []
            [{ bvars = [v1]; bterm = mk_rest rest1 };
             { bvars = [v2]; bterm = mk_rest rest2 }]
    | LabelDef (rest1, rest2, rest3) ->
         mk_term label_def_opname (**)
            []
            [{ bvars = []; bterm = mk_rest rest1 };
             { bvars = []; bterm = mk_rest rest2 };
             { bvars = []; bterm = mk_rest rest3 }]

    | LabelEnd ->
         label_end_term
    | LabelFun (v, rest) ->
         mk_term label_fun_opname (**)
            []
            [{ bvars = [v]; bterm = mk_rest rest }]

    | IMov _ ->
         raise (RefineError ("mk_inst_aux", StringError "illegal IMov instruction"))

let mk_inst_term = mk_inst_aux mk_var_term (fun rest -> rest)

let rec mk_inst (Inst inst) =
   mk_inst_aux mk_var_term mk_inst inst

let mk_inst_spill = mk_inst_aux mk_spill_reg_term (fun rest -> rest)

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
