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
 *)
extends M_ir
extends X86_asm

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.RefineError

type operand =
   ImmediateNumber of int32
 | ImmediateLabel of string * term
 | ImmediateCLabel of string * term
 | Register of string
 | SpillRegister of string
 | MemReg of string
 | MemRegOff of int32 * string
 | MemRegRegOffMul of int32 * int32 * string * string

type inst =
   Compilable of term
 | Let      of term * string * term
 | LetReg   of string * term * string * term
 | LetSpill of string * term * string * term
 | Inst1    of string * term * term
 | Inst2    of string * term * term * term
 | Instm    of string * term * term * term * term
 | Shift    of string * term * term * term
 | Cmp      of string * term * term * term
 | Set      of string * term * term * term
 | Jmp      of string * term * term list
 | Jcc      of string * term * term list * term
 | Comment  of string * term
 | LabelAsm of string * term
 | LabelRec of string * term * string * term
 | LabelDef of term * term * term
 | LabelEnd
 | LabelFun of string * term

let immediate_number_term = << ImmediateNumber[i:n] >>
let immediate_label_term = << ImmediateLabel[label:t]{'R} >>
let immediate_clabel_term = << ImmediateCLabel[label:t]{'R} >>
let register_term = << Register{'v} >>
let spill_register_term = << SpillRegister{'v} >>
let mem_reg_term = << MemReg{'r} >>
let mem_reg_off_term = << MemRegOff[i:n]{'r} >>
let mem_reg_reg_off_mul_term = << MemRegRegOffMul[off:n, mul:n]{'r1; 'r2} >>

let immediate_number_opname = opname_of_term immediate_number_term
let immediate_label_opname = opname_of_term immediate_label_term
let immediate_clabel_opname = opname_of_term immediate_clabel_term
let register_opname = opname_of_term register_term
let spill_register_opname = opname_of_term spill_register_term
let mem_reg_opname = opname_of_term mem_reg_term
let mem_reg_off_opname = opname_of_term mem_reg_off_term
let mem_reg_reg_off_mul_opname = opname_of_term mem_reg_reg_off_mul_term

let compilable_term = << compilable{'t} >>
let let_term       = << Let{'src; dst. 'rest['dst]} >>
let let_reg_term   = << Let[reg:t]{'src; dst. 'rest['dst]} >>
let let_spill_term = << LetSpill[reg:s]{'src; dst. 'rest['dst]} >>
let inst1_term     = << Inst1["neg"]{'dst; 'rest} >>
let inst2_term     = << Inst2["mov"]{'dst; 'src; 'rest} >>
let instm_term     = << Instm["mul"]{'dst1; 'dst2; 'src; 'rest} >>
let shift_term     = << Shift["sar"]{'dst; 'src; 'rest} >>
let cmp_term       = << Cmp["test"]{'src1; 'src2; 'rest} >>
let set_term       = << Set["set"]{'cc; 'dst; 'rest} >>
let jmp_term       = << Jmp["jmp"]{'label; 'arg1} >>
let jcc_term       = << Jcc["jcc"]{'cc; 'label; 'arg1; 'rest} >>
let comment_term   = << Comment[comment:s]{'rest} >>
let label_asm_term = << LabelAsm[label:t]{'R} >>
let label_rec_term = << LabelRec{R1. 'fields['R1]; R2. 'rest['R2]} >>
let label_def_term = << LabelDef{'label; 'code; 'rest} >>
let label_end_term = << LabelEnd >>
let label_fun_term = << LabelFun{v. 'insts['v]} >>

let compilable_opname = opname_of_term compilable_term
let let_opname        = opname_of_term let_term
let let_spill_opname  = opname_of_term let_spill_term
let inst1_opname      = opname_of_term inst1_term
let inst2_opname      = opname_of_term inst2_term
let instm_opname      = opname_of_term instm_term
let shift_opname      = opname_of_term shift_term
let cmp_opname        = opname_of_term cmp_term
let set_opname        = opname_of_term set_term
let jmp_opname        = opname_of_term jmp_term
let jcc_opname        = opname_of_term jcc_term
let comment_opname    = opname_of_term comment_term
let label_asm_opname  = opname_of_term label_asm_term
let label_rec_opname  = opname_of_term label_rec_term
let label_def_opname  = opname_of_term label_def_term
let label_end_opname  = opname_of_term label_end_term
let label_fun_opname  = opname_of_term label_fun_term

(*
 * Basic term construction.
 *)
let mk_register_term s =
   mk_dep0_term register_opname (mk_var_term s)

let mk_let_term t1 v t2 =
   mk_dep0_dep1_term let_opname t1 v t2

(*
 * Break apart the instruction.
 *)
let dest_inst_term t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = List.map dest_param params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [], [{ bvars = []; bterm = t }] when Opname.eq op compilable_opname ->
            Compilable t
       | [], [{ bvars = []; bterm = t1 }; { bvars = [v]; bterm = t2}]
         when Opname.eq op let_opname ->
            Let (t1, v, t2)
       | [String reg], [{ bvars = []; bterm = t1 }; { bvars = [v]; bterm = t2}]
         when Opname.eq op let_opname ->
            LetReg (reg, t1, v, t2)
       | [String opcode], [{ bvars = []; bterm = t1 }; { bvars = [v]; bterm = t2}]
         when Opname.eq op let_spill_opname ->
            LetSpill (opcode, t1, v, t2)
       | [String opcode], [{ bvars = []; bterm = dst }; { bvars = []; bterm = rest }]
         when Opname.eq op inst1_opname ->
            Inst1 (opcode, dst, rest)
       | [String opcode], [{ bvars = []; bterm = dst };
                           { bvars = []; bterm = src };
                           { bvars = []; bterm = rest }]
         when Opname.eq op inst2_opname ->
            Inst2 (opcode, dst, src, rest)
       | [String opcode], [{ bvars = []; bterm = dst1 };
                           { bvars = []; bterm = dst2 };
                           { bvars = []; bterm = src };
                           { bvars = []; bterm = rest }]
         when Opname.eq op instm_opname ->
            Instm (opcode, dst1, dst2, src, rest)
       | [String opcode], [{ bvars = []; bterm = cc };
                           { bvars = []; bterm = dst };
                           { bvars = []; bterm = rest }]
         when Opname.eq op set_opname ->
            Set (opcode, cc, dst, rest)
       | [String opcode], [{ bvars = []; bterm = dst };
                           { bvars = []; bterm = src };
                           { bvars = []; bterm = rest }]
         when Opname.eq op shift_opname ->
            Shift (opcode, dst, src, rest)
       | [String opcode], [{ bvars = []; bterm = src1 };
                           { bvars = []; bterm = src2 };
                           { bvars = []; bterm = rest }]
         when Opname.eq op cmp_opname ->
            Cmp (opcode, src1, src2, rest)
       | [String opcode], { bvars = []; bterm = f } :: args
                                                       when Opname.eq op jmp_opname ->
            Jmp (opcode, f, List.map (fun { bterm = t } -> t) args)
       | [String opcode], [{ bvars = []; bterm = cc };
                           { bvars = []; bterm = f };
                           { bvars = []; bterm = a1 };
                           { bvars = []; bterm = rest }]
         when Opname.eq op jcc_opname ->
            Jcc (opcode, f, [a1], rest)
       | [String opcode], [{ bvars = []; bterm = cc };
                           { bvars = []; bterm = f };
                           { bvars = []; bterm = a1 };
                           { bvars = []; bterm = a2 };
                           { bvars = []; bterm = rest }]
         when Opname.eq op jcc_opname ->
            Jcc (opcode, f, [a1; a2], rest)
       | [String opcode], [{ bvars = []; bterm = cc };
                           { bvars = []; bterm = f };
                           { bvars = []; bterm = a1 };
                           { bvars = []; bterm = a2 };
                           { bvars = []; bterm = a3 };
                           { bvars = []; bterm = rest }]
         when Opname.eq op jcc_opname ->
            Jcc (opcode, f, [a1; a2; a3], rest)
       | [String comment], [{ bvars = []; bterm = rest }]
         when Opname.eq op comment_opname ->
            Comment (comment, rest)
       | [Token label], [{ bvars = []; bterm = record }]
         when Opname.eq op label_asm_opname ->
            LabelAsm (label, record)
       | [], [{ bvars = [v1]; bterm = fields };
              { bvars = [v2]; bterm = rest }]
         when Opname.eq op label_rec_opname ->
            LabelRec (v1, fields, v2, rest)
       | [], [{ bvars = []; bterm = label };
              { bvars = []; bterm = code };
              { bvars = []; bterm = rest }]
         when Opname.eq op label_def_opname ->
            LabelDef (label, code, rest)
       | [], []
         when Opname.eq op label_end_opname ->
            LabelEnd
       | [], [{ bvars = [v]; bterm = code }]
         when Opname.eq op label_fun_opname ->
            LabelFun (v, code)
       | _ ->
            raise (RefineError ("not an x86 instruction", TermError t))

(*
 * Operands.
 *)
let int32_of_num i =
   Int32.of_string (Mp_num.string_of_num i)

let dest_operand_term t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = List.map dest_param params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [Number i], []
         when Opname.eq op immediate_number_opname ->
            ImmediateNumber (int32_of_num i)
       | [Token label], [{ bvars = []; bterm = t }]
         when Opname.eq op immediate_label_opname ->
            ImmediateLabel (label, t)
       | [Token label], [{ bvars = []; bterm = t }]
         when Opname.eq op immediate_clabel_opname ->
            ImmediateCLabel (label, t)
       | [], [{ bvars = []; bterm = t }]
         when Opname.eq op register_opname ->
            Register (dest_var t)
       | [], [{ bvars = []; bterm = t }]
         when Opname.eq op mem_reg_opname ->
            MemReg (dest_var t)
       | [Number i], [{ bvars = []; bterm = t }]
         when Opname.eq op mem_reg_off_opname ->
            MemRegOff (int32_of_num i, dest_var t)
       | [Number off; Number mul], [{ bvars = []; bterm = t1 };
                                    { bvars = []; bterm = t2 }]
         when Opname.eq op mem_reg_off_opname ->
            MemRegRegOffMul (int32_of_num off,
                             int32_of_num mul,
                             dest_var t1,
                             dest_var t2)
       | _ ->
            raise (RefineError ("not an x86 instruction", TermError t))

(*
 * Get the operands of the term in a list.
 *)
let operands_of_inst inst =
   match inst with
      Compilable _
    | Comment    _
    | LabelAsm   _
    | LabelFun   _
    | LabelRec   _
    | LabelDef   _
    | LabelEnd ->
         []
    | Let (src, _, _)
    | LetReg (_, src, _, _)
    | LetSpill (_, src, _, _) ->
         [src]
    | Inst1 (_, dst, _)
    | Set (_, _, dst, _) ->
         [dst]
    | Inst2 (_, dst, src, _)
    | Shift (_, dst, src, _)
    | Cmp (_, dst, src, _) ->
         [dst; src]
    | Instm (_, dst1, dst2, src, _) ->
         [dst1; dst2; src]
    | Jmp (_, f, args)
    | Jcc (_, f, args, _) ->
         f :: args

(*
 * Address of the rest of the instruction.
 *)
let next_inst inst =
   match inst with
      Compilable t
    | Comment (_, t)
    | LabelAsm (_, t)
    | LabelFun (_, t) ->
         0, t
    | Let (_, _, t)
    | LetReg (_, _, _, t)
    | LetSpill (_, _, _, t)
    | Inst1 (_, _, t)
    | LabelRec (_, t, _, _)
    | LabelDef (_, t, _) ->
         1, t
    | Inst2 (_, _, _, t)
    | Shift (_, _, _, t)
    | Cmp (_, _, _, t)
    | Set (_, _, _, t) ->
         2, t
    | Instm (_, _, _, _, t) ->
         3, t
    | Jmp _
    | LabelEnd ->
         raise (RefineError ("addr_of_rest", StringError "no rest for JMP"))
    | Jcc (_, _, args, t) ->
         2 + List.length args, t

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
