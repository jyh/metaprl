doc <:doc< 
   Define the architecture-specific part of the x86 backend.
  
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
   @docoff
>>
extends M_x86_term
extends M_ra_type

open Format

open Lm_debug
open Lm_symbol
open Lm_trace

open Refiner.Refiner.RefineError

open M_x86_inst_type
open M_x86_term
open M_ra_type
open M_ra_state

(*
 * A basic block.
 * The type of instructions is as-yet undefined.
 *   block_debug     Debugging information
 *   block_label     (local) label for this block
 *   block_code      Instructions for this block
 *   block_jumps     Local labels this block jumps to
 *)
type 'inst poly_block =
   { block_debug  : string;
     block_label  : label;
     block_code   : 'inst;
     block_jumps  : label list;
   }

type inst_block = inst poly_block
type code_block = inst code poly_block
type live_block = inst live poly_block

(*
 * Reservations are either base pointers or infix pointers.
 * These are operands because they may refer to Registers,
 * SpillRegisters, or MemRegOff forms (into the context).
 *
 * For the infix pointers, the first operand is the base
 * pointer, and the second operand is the infix pointer
 * (which is a real pointer).
 *)
type reserve =
   ResBase of operand
 | ResInfix of operand * operand

(* Flag modifer states *)
type flag =
   FlagTest   of reg * reg_class
 | FlagModify of reg * reg_class

(************************************************************************
 * Registers.
 *)

(*
 * Names of the standard args.
 *)
let eax    = Lm_symbol.add "eax"
let ebx    = Lm_symbol.add "ebx"
let ecx    = Lm_symbol.add "ecx"
let edx    = Lm_symbol.add "edx"
let esi    = Lm_symbol.add "esi"
let edi    = Lm_symbol.add "edi"
let esp    = Lm_symbol.add "esp"
let ebp    = Lm_symbol.add "ebp"
let fp0    = Lm_symbol.add "fp0"
let fp1    = Lm_symbol.add "fp1"
let fp2    = Lm_symbol.add "fp2"
let fp3    = Lm_symbol.add "fp3"
let fp4    = Lm_symbol.add "fp4"
let fp5    = Lm_symbol.add "fp5"
let iflags = Lm_symbol.add "iflags"
let fflags = Lm_symbol.add "fflags"
let fpmap  = [fp0, 0; fp1, 1; fp2, 2; fp3, 3; fp4, 4; fp5, 5]
let mmx0   = Lm_symbol.add "mmx0"
let mmx1   = Lm_symbol.add "mmx1"
let mmx2   = Lm_symbol.add "mmx2"
let mmx3   = Lm_symbol.add "mmx3"
let mmx4   = Lm_symbol.add "mmx4"
let mmx5   = Lm_symbol.add "mmx5"
let mmx6   = Lm_symbol.add "mmx6"
let mmx7   = Lm_symbol.add "mmx7"

(*
 * Register classes.
 *)
let int_reg_class   = 0
let float_reg_class = 1
let reg_class_count = 2

let int_registers = [eax; ebx; ecx; edx; esi; edi; esp; ebp]
let int_registers_special = [esp; ebp; iflags]
let arg_registers = [eax; ebx; ecx; edx; esi; edi]

let float_registers = [fp0; fp1; fp2; fp3; fp4; fp5]
let float_registers_special = [fflags]

let registers = [|int_registers; float_registers|]
let registers_special = [|int_registers_special; float_registers_special|]

let vars_initial = SymbolTable.empty
let vars_initial =
   List.fold_left (fun vars v ->
         SymbolTable.add vars v int_reg_class) vars_initial int_registers
let vars_initial =
   List.fold_left (fun vars v ->
         SymbolTable.add vars v float_reg_class) vars_initial float_registers

(************************************************************************
 * Printing.
 ************************************************************************)

let rec pp_print_symbols buf vars =
   match vars with
      [v] ->
         pp_print_symbol buf v
    | [] ->
         ()
    | v :: vars ->
         fprintf buf "%a, %a" pp_print_symbol v pp_print_symbols vars

let pp_print_operand buf op =
   match op with
      ImmediateNumber off ->
         fprintf buf "$%ld" off
    | ImmediateLabel (l, r) ->
         pp_print_symbol buf (label_of_asm_label l r)
    | ImmediateCLabel (l, r) ->
         fprintf buf "$%a" pp_print_symbol (label_of_asm_label l r)
    | Register r
    | SpillRegister (r, _) ->
         fprintf buf "%%%a" pp_print_symbol r
    | MemReg r ->
         fprintf buf "(%%%a)" pp_print_symbol r
    | MemRegOff (r, i) ->
         fprintf buf "%ld(%%%a)" i pp_print_symbol r
    | MemRegRegOffMul (r1, r2, i1, i2) ->
         fprintf buf "%ld(%%%a,%%%a,%ld)" (**)
            i1
            pp_print_symbol r1
            pp_print_symbol r2
            i2
    | SpillMemory label ->
         fprintf buf "%a(%%ebp)" pp_print_symbol label
    | ContextRegister r ->
         let s =
            match string_of_symbol r with
               "next" -> "__mem_next"
             | "limit" -> "__mem_limit"
             | s -> raise (Invalid_argument ("pp_print_operand: bad context var: " ^ s))
         in
            pp_print_string buf s

let rec pp_print_operands buf ops =
   match ops with
      [op] ->
         pp_print_operand buf op
    | [] ->
         ()
    | op :: ops ->
         fprintf buf "%a, %a" pp_print_operand op pp_print_operands ops

let pp_print_operand_byte out op =
   match op with
      Register r when r = eax -> fprintf out "%%al"
    | Register r when r = ebx -> fprintf out "%%bl"
    | Register r when r = ecx -> fprintf out "%%cl"
    | Register r when r = edx -> fprintf out "%%dl"
    | _                       -> pp_print_operand out op

let pp_print_operand_word out op =
   match op with
      Register r when r = eax -> fprintf out "%%ax"
    | Register r when r = ebx -> fprintf out "%%bx"
    | Register r when r = ecx -> fprintf out "%%cx"
    | Register r when r = edx -> fprintf out "%%dx"
    | Register r when r = esi -> fprintf out "%%si"
    | Register r when r = edi -> fprintf out "%%di"
    | _                       -> pp_print_operand out op

(*
 * Print out an instruction.
 *)
let rec pp_print_inst bound depth out (Inst inst) =
   if depth < bound then
      let pp_print_rest = pp_print_inst bound (succ depth) out in
         match inst with
            (* Mov *)
            Mov (src, dst, rest) ->
               fprintf out "\tmovl\t%a, %%%a\n" (**)
                  pp_print_operand src
                  pp_print_symbol dst;
               pp_print_rest rest

            (* We don't print implicit moves, they are printed in the actual instruction *)
          | IMov (src, dst, rest) ->
               fprintf out "\t/*\tmovl\t%%%a, %%%a\timplicit */\n" (**)
                  pp_print_symbol src
                  pp_print_symbol dst;
               pp_print_rest rest

            (* Spill *)
          | Spill (SpillGet, src, dst, rest)
          | Spill (SpillCopy, src, dst, rest) ->
               fprintf out "\tmovl\t%a, %%%a\n" (**)
                  pp_print_operand src
                  pp_print_symbol dst;
               pp_print_rest rest
          | Spill (SpillSet, src, dst, rest) ->
               fprintf out "\tmovl\t%a, %a(%%ebp)\n" (**)
                  pp_print_operand src
                  pp_print_symbol dst;
               pp_print_rest rest

            (* Inst1 *)
          | Inst1Mem (opcode, dst, rest) ->
               fprintf out "\t%sl\t%a\t/* Memory operand */\n" (**)
                  (mk_inst1_opcode opcode)
                  pp_print_operand dst;
               pp_print_rest rest
          | Inst1Reg (opcode, src, dst, rest) ->
               if not (Lm_symbol.eq src dst) then
                  fprintf out "\tmovl\t%%%a, %%%a\t/* implicit inst1 move */\n" (**)
                     pp_print_symbol src
                     pp_print_symbol dst;
               fprintf out "\t%sl\t%%%a\n" (**)
                  (mk_inst1_opcode opcode)
                  pp_print_symbol dst;
               pp_print_rest rest

            (* Inst2 *)
          | Inst2Mem (opcode, src, dst, rest) ->
               fprintf out "\t%sl\t%a, %a\t/* Memory operand */\n" (**)
                  (mk_inst2_opcode opcode)
                  pp_print_operand src
                  pp_print_operand dst;
               pp_print_rest rest
          | Inst2Reg (opcode, src1, src2, dst, rest) ->
               if not (Lm_symbol.eq src2 dst) then
                  fprintf out "\tmovl\t%%%a, %%%a\t/* implicit inst2 move */\n" (**)
                     pp_print_symbol src2
                     pp_print_symbol dst;
               fprintf out "\t%sl\t%a, %%%a\n" (**)
                  (mk_inst2_opcode opcode)
                  pp_print_operand src1
                  pp_print_symbol dst;
               pp_print_rest rest

            (* Inst3 *)
          | Inst3Reg (opcode, src1, src2, src3, dst2, dst3, rest) ->
               if not (Lm_symbol.eq src2 dst2) then
                   fprintf out "\tmovl\t%%%a, %%%a\t/* implicit inst3 move */\n" (**)
                     pp_print_symbol src2
                     pp_print_symbol dst2;
               if not (Lm_symbol.eq src3 dst3) then
                   fprintf out "\tmovl\t%%%a, %%%a\t/* implicit inst3 move */\n" (**)
                     pp_print_symbol src3
                     pp_print_symbol dst3;
               fprintf out "\t%sl\t%a\t/* dst(%%%a, %%%a) */\n" (**)
                  (mk_inst3_opcode opcode)
                  pp_print_operand src1
                  pp_print_symbol dst2
                  pp_print_symbol dst3;
               pp_print_rest rest

            (* Shift *)
          | ShiftMem (opcode, src, dst, rest) ->
               fprintf out "\t%sl\t%a, %a\t/* Memory operand */\n" (**)
                  (mk_shift_opcode opcode)
                  pp_print_operand_byte src
                  pp_print_operand dst;
               pp_print_rest rest
          | ShiftReg (opcode, src1, src2, dst, rest) ->
               if not (Lm_symbol.eq src2 dst) then
                  fprintf out "\tmovl\t%%%a, %%%a\t/* implicit shift move */\n" (**)
                     pp_print_symbol src2
                     pp_print_symbol dst;
               fprintf out "\t%sl\t%a, %%%a\n" (**)
                  (mk_shift_opcode opcode)
                  pp_print_operand_byte src1
                  pp_print_symbol src2;
               pp_print_rest rest

            (* Cmp *)
          | Cmp (opcode, src1, src2, rest) ->
               fprintf out "\t%sl\t%a, %a\n" (**)
                  (mk_cmp_opcode opcode)
                  pp_print_operand src1
                  pp_print_operand src2;
               pp_print_rest rest

            (* Set *)
          | SetMem (opcode, cc, dst, rest) ->
               fprintf out "\t%s%sl\t%a\t/* Memory operand */\n" (**)
                  (mk_set_opcode opcode)
                  (mk_cc cc)
                  pp_print_operand dst;
               pp_print_rest rest
          | SetReg (opcode, cc, src, dst, rest) ->
               if not (Lm_symbol.eq src dst) then
                  fprintf out "\tmovl\t%%%a, %%%a\t/* implicit set move */\n" (**)
                     pp_print_symbol src
                     pp_print_symbol dst;
               fprintf out "\t%s%sl\t%%%a\n" (**)
                  (mk_set_opcode opcode)
                  (mk_cc cc)
                  pp_print_symbol src;
               pp_print_rest rest

            (* Branching *)
          | Jmp (opcode, ImmediateLabel (dst, r), args) ->
               fprintf out "\t%s\t%a\t/* args(%a) */\n" (**)
                  (mk_jmp_opcode opcode)
                  pp_print_symbol dst
                  pp_print_symbols args
          | Jmp (opcode, dst, args) ->
               fprintf out "\t%s\t*%a\t/* args(%a) */\n" (**)
                  (mk_jmp_opcode opcode)
                  pp_print_operand dst
                  pp_print_symbols args
          | Jcc (_, cc, rest1, rest2) ->
               let cc = mk_cc (invert_cc cc) in
               let label = new_symbol_string cc in
                  fprintf out "\tj%s\t%a\n" cc pp_print_symbol label;
                  pp_print_rest rest1;
                  fprintf out "\n%a:\n" pp_print_symbol label;
                  pp_print_rest rest2

            (* Reserve *)
          | Reserve (words, params) ->
               let label = Lm_symbol.new_symbol_string "reserve" in
                  fprintf out "\t/* reserve %ld words (%a) */\n" (**)
                     words
                     pp_print_symbols params;
                  fprintf out "\t.data\n";
                  fprintf out "\t.align\t4\n";
                  fprintf out "%a:\n" pp_print_symbol label;
                  fprintf out "\t.long\t%d\n" ((1 lsl (List.length params)) - 1);
                  fprintf out "\t.long\t-1\n";
                  fprintf out "\t.text\n";
                  fprintf out "\tpushl\t$%ld*4\n" words;
                  fprintf out "\tpushl\t$%a\n" pp_print_symbol label;
                  fprintf out "\tcall\t__gc\n";
                  fprintf out "\taddl\t$8, %%esp\n"

            (* Comments *)
          | Comment (comment, rest) ->
               fprintf out "\t/* Comment: %s */\n" comment;
               pp_print_rest rest

          | Init _ ->
               (* Ignore initialization *)
               ()
          | LabelAsm _ ->
               fprintf out "\t/* LabelAsm */\n"
          | LabelRec (_, rest1, _, rest2) ->
               fprintf out "\t/* LabelRec */\n";
               pp_print_rest rest1;
               pp_print_rest rest2
          | LabelDef (Inst label, body, rest) ->
               if is_init_label_asm label then
                  fprintf out "\n\t.global\t__m_main\n__m_main:\n%a:\n" pp_print_symbol (label_of_label_asm label)
               else
                  fprintf out "\n%a:\n" pp_print_symbol (label_of_label_asm label);
               pp_print_rest body;
               pp_print_rest rest
          | LabelEnd ->
               fprintf out "\t/* LabelEnd */\n"
          | LabelFun (v, rest) ->
               fprintf out "\t/* Param: %a */\n" pp_print_symbol v;
               pp_print_rest rest
          | Compilable rest ->
               fprintf out "\t/* Compilable */\n";
               pp_print_rest rest

let pp_print_inst1 = pp_print_inst 1 0
let pp_print_inst  = pp_print_inst max_int 0

let pp_print_prog out t =
   fprintf out "/* Context specification */\n";
   fprintf out "\t.equ\tcontext_next,20\n";
   fprintf out "\t.equ\tcontext_limit,24\n\n";
   fprintf out "\t.text\n\n";
   pp_print_inst out (dest_inst t)

(*
 * Print a code block.
 *)
let rec pp_print_code out
    { code_src = src;
      code_dst = dst;
      code_class = cclass;
      code_inst = inst;
      code_rest = rest
    } =
   let pp_print_var_set vars =
      ignore (SymbolSet.fold (fun flag v ->
                    if flag then
                       pp_print_string out ", ";
                    fprintf out "%s" (string_of_symbol v);
                    true) false vars)
   in
   let pp_print_code_class out cclass =
      match cclass with
         CodeNormal ->
            fprintf out "CodeNormal"
       | CodeMove ->
            fprintf out "CodeMove"
       | CodeJump l ->
            fprintf out "CodeJump %a" pp_print_symbol l
   in
      fprintf out "# src = ";
      pp_print_var_set src;
      fprintf out "\n# dst = ";
      pp_print_var_set dst;
      fprintf out "\n# class = %a\n" pp_print_code_class cclass;
      pp_print_inst1 out inst;
      List.iter (pp_print_code out) rest

let rec pp_print_live out
    { live_src = src;
      live_dst = dst;
      live_out = live;
      live_class = cclass;
      live_inst = inst;
      live_rest = rest
    } =
   let pp_print_var_set vars =
      ignore (SymbolSet.fold (fun flag v ->
                    if flag then
                       pp_print_string out ", ";
                    fprintf out "%s" (string_of_symbol v);
                    true) false vars)
   in
   let pp_print_code_class out cclass =
      match cclass with
         CodeNormal ->
            fprintf out "CodeNormal"
       | CodeMove ->
            fprintf out "CodeMove"
       | CodeJump l ->
            fprintf out "CodeJump %a" pp_print_symbol l
   in
      fprintf out "# src = ";
      pp_print_var_set src;
      fprintf out "\n# dst = ";
      pp_print_var_set dst;
      fprintf out "\n# live_out = ";
      pp_print_var_set live;
      fprintf out "\n# class = %a\n" pp_print_code_class cclass;
      pp_print_inst1 out inst;
      List.iter (pp_print_live out) rest

(*
 * Print a single block.
 *)
let pp_print_block print_code out block =
   let { block_debug  = debug;
         block_label  = label;
         block_code   = code;
         block_jumps  = jumps;
       } = block
   in
      (* Print the code *)
      fprintf out "\t.skip\t64\n";
      fprintf out "%a:\n" pp_print_symbol label;
      print_code out code;

      (* Print jumps *)
      List.iter (fun v -> fprintf out "\t# Jumps to: %a\n" pp_print_symbol v) jumps;

      (* Print extra newline *)
      fprintf out "\n"

let pp_print_inst_blocks out (blocks : inst_block trace) =
   Lm_trace.iter (pp_print_block pp_print_inst out) blocks

let pp_print_code_blocks out (blocks : code_block trace) =
   Lm_trace.iter (pp_print_block pp_print_code out) blocks

let pp_print_live_blocks out (blocks : live_block trace) =
   Lm_trace.iter (pp_print_block pp_print_live out) blocks

(************************************************************************
 * Rename table.
 *
 * The rename table is used to force some register assignments.
 * For example, MUL requires that src2=eax and src3=edx.
 * The rename table contains these mappings.
 *
 * The rename table is constructed by the vars_ functions
 * below.
 *)

type rename = var SymbolTable.t

let rename_empty = SymbolTable.empty

let rename_add = SymbolTable.add

let rename_find table v =
   try SymbolTable.find table v with
      Not_found ->
         v

(*
 * Flatten the rename table.
 *)
let rename_flatten table =
   let rec lookup v =
      try lookup (SymbolTable.find table v) with
         Not_found ->
            v
   in
      SymbolTable.map lookup table

(*
 * Rename the shift operand if it is a register.
 *)
let rename_shift rename op =
   match op with
      ImmediateNumber _
    | ImmediateCLabel _ ->
         rename
    | Register v ->
         rename_add rename v ecx
    | ContextRegister _
    | SpillRegister _
    | SpillMemory _
    | ImmediateLabel _
    | MemReg _
    | MemRegOff _
    | MemRegRegOffMul _ ->
         raise (RefineError ("rename_shift", StringError "illegal shift operand"))

let rename_mul rename dst2 dst3 =
   let rename = rename_add rename dst2 eax in
   let rename = rename_add rename dst3 edx in
      rename

(* Assign args to registers *)
let rename_args rename args =
   let rec add rename regs params =
      match regs, params with
         reg :: regs, v :: params ->
            add (rename_add rename v reg) regs params
       | _, [] ->
            rename
       | [], _ ->
            raise (RefineError ("assign_args", StringIntError ("too many arguments", List.length args)))
   in
      add rename arg_registers args

(*
 * Get the vars in an instruction.
 *)
let rec rename_inst rename (Inst inst) =
   match inst with
      (* Instructions that don't require renaming *)
      Mov        (_, _, rest)
    | IMov       (_, _, rest)
    | Spill      (_, _, _, rest)
    | Inst1Mem   (_, _, rest)
    | SetMem     (_, _, _, rest)
    | Inst1Reg   (_, _, _, rest)
    | SetReg     (_, _, _, _, rest)
    | Inst2Mem   (_, _, _, rest)
    | Cmp        (_, _, _, rest)
    | Inst2Reg   (_, _, _, _, rest)
    | Comment    (_, rest)
    | LabelFun   (_, rest)
    | Compilable rest ->
         rename_inst rename rest

      (* Shift src must be in %cl *)
    | ShiftMem   (_, src, _, rest)
    | ShiftReg   (_, src, _, _, rest) ->
         let rename = rename_shift rename src in
            rename_inst rename rest

      (* Multiply in %eax, %edx *)
    | Inst3Reg   (_, _, _, _, dst2, dst3, rest) ->
         let rename = rename_mul rename dst2 dst3 in
            rename_inst rename rest

      (* Calling convention *)
    | Jmp     (_, _, args) ->
         rename_args rename args
    | Reserve (_, params) ->
         rename_args rename params

      (* Conditional *)
    | Jcc      (_, _, rest1, rest2)
    | LabelDef (_, rest1, rest2) ->
         let rename = rename_inst rename rest1 in
            rename_inst rename rest2
    | LabelRec (v1, rest1, v2, rest2) ->
         let rename = rename_add rename v2 v1 in
         let rename = rename_inst rename rest1 in
            rename_inst rename rest2

      (* Ignore initialization code *)
    | Init _
    | LabelAsm _
    | LabelEnd ->
         (* Ignore intialization code *)
         rename

(*
 * Get the vars in the term.
 *)
let rename_term t =
   rename_inst rename_empty (dest_inst t)

(************************************************************************
 * Get all the vars mentioned in any of the instructions.
 *)

(*
 * Add a var, translating through the rename table.
 *)
let vars_var = SymbolTable.add

let vars_vars vars vars' reg_class =
   List.fold_left (fun vars v ->
         vars_var vars v int_reg_class) vars vars'

(*
 * Get the vars in an operand.
 *)
let vars_operand vars op =
   match op with
      ImmediateNumber _
    | ImmediateLabel _
    | ImmediateCLabel _ ->
         vars
    | ContextRegister _
    | SpillMemory _ ->
         (* These registers are implicitly accessed through %ebp *)
         vars_var vars ebp int_reg_class
    | Register r
    | MemReg r
    | MemRegOff (r, _)
    | SpillRegister (r, _) ->
         vars_var vars r int_reg_class
    | MemRegRegOffMul (r1, r2, _, _) ->
         let vars = vars_var vars r1 int_reg_class in
         let vars = vars_var vars r2 int_reg_class in
            vars

let vars_operands vars operands =
   List.fold_left vars_operand vars operands

let vars_operand_mov vars src dst =
   let vars = vars_operand vars src in
   let vars = vars_var vars dst int_reg_class in
      vars

let vars_operand1_mem vars dst =
   vars_operand vars dst

let vars_operand1_reg vars src dst =
   let vars = vars_var vars src int_reg_class in
   let vars = vars_var vars dst int_reg_class in
      vars

let vars_operand2_mem vars src dst =
   let vars = vars_operand vars src in
   let vars = vars_operand vars dst in
      vars

let vars_operand2_reg vars src1 src2 dst =
   let vars = vars_operand vars src1 in
   let vars = vars_var vars src2 int_reg_class in
   let vars = vars_var vars dst int_reg_class in
      vars

let vars_operand_shift_mem vars src dst =
   let vars = vars_operand vars src in
   let vars = vars_operand vars dst in
      vars

let vars_operand_shift_reg vars src1 src2 dst =
   let vars = vars_operand vars src1 in
   let vars = vars_var vars src2 int_reg_class in
   let vars = vars_var vars dst int_reg_class in
      vars

let vars_operand3_mul vars src1 src2 src3 dst2 dst3 =
   let vars = vars_operand vars src1 in
   let vars = vars_var vars src2 int_reg_class in
   let vars = vars_var vars src3 int_reg_class in
   let vars = vars_var vars dst2 int_reg_class in
   let vars = vars_var vars dst3 int_reg_class in
      vars

let vars_jmp vars src args =
   let vars = vars_operand vars src in
   let vars = vars_vars vars args int_reg_class in
      vars

let vars_reserve vars args =
   vars_vars vars args int_reg_class

let vars_fun vars v =
   vars_var vars v int_reg_class

(*
 * Get the vars in an instruction.
 *)
let rec vars_inst vars (Inst inst) =
   match inst with
      Mov     (src, dst, rest)
    | Spill   (SpillGet, src, dst, rest)
    | Spill   (SpillCopy, src, dst, rest) ->
         let vars = vars_operand_mov vars src dst in
            vars_inst vars rest
    | Spill   (SpillSet, src, _, rest) ->
         let vars = vars_operand vars src in
            vars_inst vars rest
    | Inst1Mem   (_, dst, rest)
    | SetMem     (_, _, dst, rest) ->
         let vars = vars_operand1_mem vars dst in
            vars_inst vars rest
    | IMov       (src, dst, rest)
    | Inst1Reg   (_, src, dst, rest)
    | SetReg     (_, _, src, dst, rest) ->
         let vars = vars_operand1_reg vars src dst in
            vars_inst vars rest
    | Inst2Mem   (_, src, dst, rest)
    | Cmp        (_, src, dst, rest) ->
         let vars = vars_operand2_mem vars src dst in
            vars_inst vars rest
    | Inst2Reg   (_, src1, src2, dst, rest) ->
         let vars = vars_operand2_reg vars src1 src2 dst in
            vars_inst vars rest
    | ShiftMem   (_, src, dst, rest) ->
         let vars = vars_operand_shift_mem vars src dst in
            vars_inst vars rest
    | ShiftReg   (_, src1, src2, dst, rest) ->
         let vars = vars_operand_shift_reg vars src1 src2 dst in
            vars_inst vars rest
    | Inst3Reg   (_, src1, src2, src3, dst2, dst3, rest) ->
         let vars = vars_operand3_mul vars src1 src2 src3 dst2 dst3 in
            vars_inst vars rest

    | Jmp     (_, src, args) ->
         vars_jmp vars src args
    | Jcc     (_, _, rest1, rest2) ->
         let vars = vars_inst vars rest1 in
            vars_inst vars rest2

    | Reserve (_, args) ->
         vars_reserve vars args
    | Comment (_, rest) ->
         vars_inst vars rest
    | Init _ ->
         (* Ignore intialization code *)
         vars
    | LabelFun (v, rest) ->
         let vars = vars_fun vars v in
            vars_inst vars rest

    | LabelAsm _
    | LabelRec _
    | LabelDef _
    | LabelEnd
    | Compilable _ ->
         raise (RefineError ("vars_inst", StringError "illegal instruction"))

(*
 * Get the vars in a block.
 *)
let vars_block vars block =
   vars_inst vars block.block_code

(*
 * Get the vars in the blocks.
 *)
let vars_blocks blocks =
   Lm_trace.fold vars_block vars_initial blocks

(************************************************************************
 * Abstract instructions.
 *
 * For each instruction, get the operands.
 *)

(*
 * Registers in a src operand.
 *)
let src_regs src regs =
   match src with
      ImmediateNumber _
    | ImmediateLabel _
    | ImmediateCLabel _
    | SpillMemory _
    | ContextRegister _ ->
         regs
    | SpillRegister (r, _)
    | Register r
    | MemReg r
    | MemRegOff (r, _) ->
         SymbolSet.add regs r
    | MemRegRegOffMul (r1, r2, _, _) ->
         SymbolSet.add (SymbolSet.add regs r1) r2

let src_regs_list srcs regs =
   List.fold_left (fun regs src ->
         src_regs src regs) regs srcs

let dst_regs rename dst regs =
   match dst with
      Register r ->
         SymbolSet.add regs r
    | ImmediateNumber _
    | ImmediateLabel _
    | ImmediateCLabel _
    | MemReg _
    | MemRegOff _
    | MemRegRegOffMul _
    | SpillRegister _
    | SpillMemory _
    | ContextRegister _ ->
         regs

(* get_operands_param
   We pretend that this instruction defines the var.  *)
let get_operands_param inst rest dst =
   { code_dst   = SymbolSet.singleton dst;
     code_src   = SymbolSet.empty;
     code_class = CodeNormal;
     code_inst  = inst;
     code_rest  = [rest]
   }

(* move_operands
   Constructs a move expression from src to dst.  *)
let get_operands_mov_int32 inst rest src dst =
   { code_dst   = SymbolSet.singleton dst;
     code_src   = SymbolSet.singleton src;
     code_class = CodeMove;
     code_inst  = inst;
     code_rest  = [rest]
   }


(* get_operands_mov
   Get the operands for a move instruction, with one source
   as well as one destination (the destination may be in
   memory in which case dst is a source regs, but not dest).  *)
let get_operands_mov inst rest src dst =
   let dst, src =
      match dst with
         Register r ->
            SymbolSet.singleton r, src_regs src SymbolSet.empty
       | _ ->
            SymbolSet.empty, src_regs dst (src_regs src SymbolSet.empty)
   in
      { code_dst   = dst;
        code_src   = src;
        code_class = CodeNormal;
        code_inst  = inst;
        code_rest  = [rest]
      }


(*
 * Branches.
 *)
let get_operands_jmp inst src args =
   let srcs = List.fold_left SymbolSet.add SymbolSet.empty args in
      match src with
         ImmediateLabel (l, _) ->
            { code_dst   = SymbolSet.empty;
              code_src   = srcs;
              code_class = CodeJump l;
              code_inst  = inst;
              code_rest  = []
            }
       | _ ->
            { code_dst   = SymbolSet.empty;
              code_src   = src_regs src srcs;
              code_class = CodeNormal;
              code_inst  = inst;
              code_rest  = []
            }

let get_operands_jcc inst rest1 rest2 =
   { code_dst   = SymbolSet.empty;
     code_src   = SymbolSet.empty;
     code_class = CodeNormal;
     code_inst  = inst;
     code_rest  = [rest1; rest2]
   }

let get_operands_reserve inst args =
      { code_dst = SymbolSet.empty;
        code_src = List.fold_left SymbolSet.add SymbolSet.empty args;
        code_class = CodeNormal;
        code_inst = inst;
        code_rest = []
      }


(* For multi-operand instructions that don't exist,
   add an implicit move before the instruction.  *)
let add_implicit_mov rest inst src dst =
   let inst = Inst (IMov (src, dst, inst)) in
   let code =
      { code_dst = SymbolSet.singleton dst;
        code_src = SymbolSet.singleton src;
        code_class = CodeMove;
        code_inst  = inst;
        code_rest  = [rest]
      }
   in
      inst, code


(* get_operands1
   Get the operands for an instruction with src = dst.  *)
let get_operands1_mem inst rest src =
   { code_dst   = SymbolSet.empty;
     code_src   = src_regs src SymbolSet.empty;
     code_class = CodeNormal;
     code_inst  = inst;
     code_rest  = [rest]
   }

let get_operands1_reg inst rest src dst =
   let code =
      { code_dst = SymbolSet.singleton dst;
        code_src = SymbolSet.singleton src;
        code_class = CodeNormal;
        code_inst  = inst;
        code_rest  = [rest]
      }
   in
   let _, code = add_implicit_mov code inst src dst in
      code


(* get_operands2
   Get the operands for an instruction with a separate src/dst *)
let get_operands2_mem inst rest src dst =
   { code_dst   = SymbolSet.empty;
     code_src   = src_regs src (src_regs dst SymbolSet.empty);
     code_class = CodeNormal;
     code_inst  = inst;
     code_rest  = [rest]
   }

let get_operands2_reg inst rest src1 src2 dst =
   let code =
      { code_dst   = SymbolSet.singleton dst;
        code_src   = src_regs src1 (SymbolSet.singleton src2);
        code_class = CodeNormal;
        code_inst  = inst;
        code_rest  = [rest]
      }
   in
   let _, code = add_implicit_mov code inst src2 dst in
      code


(* get_operands_mul
   Construct the special case for MUL, where eax:edx are
   destination registers, and eax is a source register. *)
let get_operands_mul inst rest src1 src2 src3 dst2 dst3 =
   let code =
      { code_dst   = SymbolSet.add (SymbolSet.singleton dst2) dst3;
        code_src   = src_regs src1 (SymbolSet.add (SymbolSet.singleton src2) src3);
        code_class = CodeNormal;
        code_inst  = inst;
        code_rest  = [rest]
      }
   in
   let inst, code = add_implicit_mov code inst src2 dst2 in
   let _, code = add_implicit_mov code inst src3 dst3 in
      code


(* get_operands_cmp
   Get operands for an instruction which reads both arguments
   as its sources, but makes no modification and has no dst.  *)
let get_operands_cmp inst rest src1 src2 =
   { code_dst   = SymbolSet.empty;
     code_src   = src_regs src1 (src_regs src2 SymbolSet.empty);
     code_class = CodeNormal;
     code_inst  = inst;
     code_rest  = [rest]
   }


(* null_inst has no dst,src *)
let get_operands_null inst rest =
   { code_dst   = SymbolSet.empty;
     code_src   = SymbolSet.empty;
     code_class = CodeNormal;
     code_inst  = inst;
     code_rest  = rest
   }


let rec get_operands inst =
   let Inst inst' = inst in
      match inst' with
         LabelFun (v, rest) ->
            let rest = get_operands rest in
               get_operands_param inst rest v

       | Mov    (Register src, dst, rest)
       | IMov   (src, dst, rest) ->
            let rest = get_operands rest in
               get_operands_mov_int32 inst rest src dst
       | Mov    (src, dst, rest) ->
            let rest = get_operands rest in
               get_operands_mov inst rest src (Register dst)
       | Spill(SpillSet, src, dst, rest) ->
            let rest = get_operands rest in
               get_operands_mov inst rest src (SpillMemory dst)
       | Spill (SpillGet, src, dst, rest)
       | Spill (SpillCopy, src, dst, rest) ->
            let rest = get_operands rest in
               get_operands_mov inst rest src (Register dst)

       | Inst1Mem (_, dst, rest)
       | SetMem (_, _, dst, rest) ->
            let rest = get_operands rest in
               get_operands1_mem inst rest dst

       | Inst1Reg (_, src, dst, rest)
       | SetReg (_, _, src, dst, rest) ->
            let rest = get_operands rest in
               get_operands1_reg inst rest src dst

       | Inst2Mem (_, src, dst, rest)
       | ShiftMem (_, src, dst, rest) ->
            let rest = get_operands rest in
               get_operands2_mem inst rest src dst

       | Inst2Reg (_, src1, src2, dst, rest)
       | ShiftReg (_, src1, src2, dst, rest) ->
            let rest = get_operands rest in
               get_operands2_reg inst rest src1 src2 dst

       | Inst3Reg (_, src1, src2, src3, dst2, dst3, rest) ->
            let rest = get_operands rest in
               get_operands_mul inst rest src1 src2 src3 dst2 dst3

       | Cmp    (_, src1, src2, rest) ->
            let rest = get_operands rest in
               get_operands_cmp inst rest src1 src2

       | Jmp    (_, src, args) ->
            get_operands_jmp inst src args

       | Jcc    (_, _, rest1, rest2) ->
            let rest1 = get_operands rest1 in
            let rest2 = get_operands rest2 in
               get_operands_jcc inst rest1 rest2

       | Reserve (_, srcs) ->
            get_operands_reserve inst srcs

       | Comment (_, rest) ->
            let rest = get_operands rest in
               get_operands_null inst [rest]
       | Init _ ->
            get_operands_null inst []

       | Compilable _
       | LabelAsm _
       | LabelDef _
       | LabelEnd
       | LabelRec _ ->
            raise (RefineError ("get_operands", StringError "bad instruction"))

(*
 * Filter operands lists.
 *)
let rec filter_code_operands filter code =
   let { code_src = src;
         code_dst = dst;
         code_rest = rest
       } = code
   in
      { code with code_src = filter src;
                  code_dst = filter dst;
                  code_rest = List.map (filter_code_operands filter) rest
      }

(*
 * Derive dst/src for each instruction.
 *)
let block_code block =
   get_operands block.block_code

let block_code ignore block =
   let code = block_code block in
   let filter vars =
      SymbolSet.fold (fun vars v ->
            if List.mem v ignore then
               vars
            else
               SymbolSet.add vars v) SymbolSet.empty vars
   in
   let code =
      if ignore = [] then
         code
      else
         filter_code_operands filter code
   in
      if debug debug_live then
         eprintf "@[<v 3>Block code: @ %a@]@." pp_print_code code;
      code

(************************************************************************
 * Collect blocks from the goal.
 *)

(*
 * Convert the goal of the program into a block list.
 *)
let blocks_of_term t =
   (* Collect all functions *)
   let rec collect blocks (Inst inst) =
      match inst with
         Compilable rest
       | Comment (_, rest) ->
            collect blocks rest
       | LabelRec (_, rest1, _, rest2) ->
            (* For debugging *)
            collect (collect blocks rest1) rest2
       | LabelDef (Inst label, body, rest) ->
            let label = label_of_label_asm label in
            let block =
               { block_debug = string_of_symbol label;
                 block_label = label;
                 block_code = body;
                 block_jumps = []
               }
            in
               collect (block :: blocks) rest
       | LabelEnd ->
            blocks
       | Init _ ->
            (* Ignore the initialization code *)
            blocks
       | _ ->
            raise (RefineError ("blocks_of_term", StringTermError ("unexpected term", t)))
   in
      Lm_trace.of_list (collect [] (dest_inst t))

(************************************************************************
 * The Frame module.
 *)

(*
 * The abstract frame.
 *)
module Frame : FrameSig =
struct
   (* Types *)
   type 'a block = 'a poly_block
   type inst = M_x86_inst_type.inst

   (*
    * Spill costs.  These numbers are the relative costs
    * of loads/stores.  Larger numbers cost more.
    *
    * BUG: I don't know the architecture well enough to estimate
    * the cost of memory operations.  However, I assume defs are
    * more expensive that uses because of cache behavior.
    *)
   let def_cost = 5
   let use_cost = 3
   let mov_def_cost = 2
   let mov_use_cost = 1
   let min_spill_length = 5

   (* Basic blocks *)
   let block_label { block_label = label } =
      label

   let block_code = block_code

   let block_live block live =
      { block with block_code = live }

   let pp_print_inst_blocks = pp_print_inst_blocks
   let pp_print_code_blocks = pp_print_code_blocks
   let pp_print_live_blocks = pp_print_live_blocks

   (*
    * Register sets.
    *)
   let registers = registers
   let registers_special = registers_special
   let reg_class_count = reg_class_count

   (*
    * Get all the vars defined in any instruction.
    *)
   let vars_blocks = vars_blocks

   (*
    * Get the blocks of a term.
    *)
   let blocks_of_term = blocks_of_term
end

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
