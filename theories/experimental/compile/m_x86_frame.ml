(*
 * Basic parameters of the runtime.
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
extends M_arith
extends M_x86_util

open Base_meta

open Top_conversionals

(*
 * We need more general operands during code construction.
 *)
declare ImmediateNumber{'i}
declare MemRegOff{'r; 'off}
declare MemRegRegOffMul{'r1; 'r2; 'off; 'mul}

dform immediate_number_df : ImmediateNumber{'i} =
   `"<$" slot{'i} `">"

dform mem_reg_off_df : MemRegOff{'r; 'off} =
   slot{'off} `"<" slot{'r} `">"

dform mem_reg_reg_off_mul_df : MemRegRegOffMul{'r1; 'r2; 'off; 'mul} =
   `"<" slot{'r1} `"," slot{'r2} `"," slot{'off} `"," slot{'mul} `">"

prim_rw fold_immediate_number :
   ImmediateNumber{number[i:n]} <--> ImmediateNumber[i:n]

prim_rw fold_mem_reg_off :
   MemRegOff{'r; number[off:n]} <--> MemRegOff[off:n]{'r}

prim_rw fold_mem_reg_reg_off_mul :
   MemRegRegOffMul{'r1; 'r2; number[off:n]; number[mul:n]} <--> MemRegRegOffMul[off:n, mul:n]{'r1; 'r2}

(*
 * Size of a word on this platform, in bytes.
 *)
define unfold_word_size : word_size <--> number[4:n]

dform word_size_df : word_size = `"$word_size"

(*
 * This is the format of the header word of a given size.
 *)
declare header[i:n]
declare header{'i}

dform header_df1 : header[i:n] =
   bf["header["] slot[i:n] bf["]"]

dform header_df2 : header{'i} =
   bf["header<"] slot{'i} bf[">"]

prim_rw unfold_header : header[i:n] <--> ImmediateNumber{mul{number[i:n]; word_size}}
prim_rw fold_header : header{number[i:n]} <--> header[i:n]

(*
 * We need a way to refer to actual registers.  We give each of the
 * actual registers a term, and then replace the terms with
 * the actual registers.
 *)

(*
 * Allocation handles.
 *)
declare RegisterLabel[label:t]

(*
 * Normal registers.
 *)
define unfold_eax : eax <--> RegisterLabel["eax":t]
define unfold_ebx : ebx <--> RegisterLabel["ebx":t]
define unfold_ecx : ecx <--> RegisterLabel["ecx":t]
define unfold_edx : edx <--> RegisterLabel["edx":t]
define unfold_esi : esi <--> RegisterLabel["esi":t]
define unfold_edi : edi <--> RegisterLabel["edi":t]
define unfold_esp : esp <--> RegisterLabel["esp":t]
define unfold_ebp : ebp <--> RegisterLabel["ebp":t]

(*
 * Context values.
 *)
define unfold_next : next <--> RegisterLabel["next":t]

(*
 * Register assignment.
 *)
declare AssignRegisters{'registers}
declare RegisterNil
declare RegisterCons[label:t]{'reg; 'rest}
declare LookupRegister[label:t]{'registers}

(*
 * Display.
 *)
dform register_label_df : RegisterLabel[label:t] =
   bf["reg["] slot[label:t] bf["]"]

dform eax_df : eax = bf["eax"]
dform ebx_df : eax = bf["ebx"]
dform ecx_df : eax = bf["ecx"]
dform edx_df : eax = bf["edx"]
dform esi_df : eax = bf["esi"]
dform edi_df : eax = bf["edi"]
dform esp_df : eax = bf["esp"]
dform ebp_df : eax = bf["ebp"]
dform next_df : next = bf["next"]

dform assign_registers_df : AssignRegisters{'regs} =
   szone pushm[3] bf["assign "] 'regs popm ezone

dform lookup_register_df : LookupRegister[label:t]{'regs} =
   szone pushm[3] bf["lookup "] slot[label:t] 'regs popm ezone

dform register_nil_df : RegisterNil =
   `""

dform register_cons_df : RegisterCons[label:t]{'reg; 'rest} =
   hspace bf["reg["] slot[label:t] bf["] = "] slot{'reg} 'rest

(*
 * Assign operands.
 *)
prim_rw assign_reg_number :
   MapOperand{AssignRegisters{'registers}; ImmediateNumber[i:n]}
   <-->
   ImmediateNumber[i:n]

prim_rw assign_reg_label :
   MapOperand{AssignRegisters{'registers}; ImmediateLabel[label:t]{'R}}
   <-->
   ImmediateLabel[label:t]{'R}

prim_rw assign_reg_clabel :
   MapOperand{AssignRegisters{'registers}; ImmediateCLabel[label:t]{'R}}
   <-->
   ImmediateCLabel[label:t]{'R}

prim_rw assign_reg_register :
   MapOperand{AssignRegisters{'registers}; Register{'v}}
   <-->
   Register{'v}

prim_rw assign_reg_spill :
   MapOperand{AssignRegisters{'registers}; SpillRegister{'v}}
   <-->
   SpillRegister{'v}

prim_rw assign_reg_mem_reg :
   MapOperand{AssignRegisters{'registers}; MemReg{'r}}
   <-->
   MemReg{'r}

prim_rw assign_reg_mem_reg_off :
   MapOperand{AssignRegisters{'registers}; MemRegOff[i:n]{'r}}
   <-->
   MemRegOff[i:n]{'r}

prim_rw assign_reg_mem_reg_reg_off_mul :
   MapOperand{AssignRegisters{'registers}; MemRegRegOffMul[off:n, mul:n]{'r1; 'r2}}
   <-->
   MemRegRegOffMul[off:n, mul:n]{'r1; 'r2}

prim_rw assign_reg_reg_label :
   MapOperand{AssignRegisters{'registers}; RegisterLabel[label:t]}
   <-->
   LookupRegister[label:t]{'registers}

prim_rw lookup_reg_lookup_cons :
   LookupRegister[label1:t]{RegisterCons[label2:t]{'reg; 'rest}}
   <-->
   meta_eq[label1:t, label2:t]{'reg; LookupRegister[label1:t]{'rest}}

(*
 * Add common reductions to reduce resource.
 *)
let resource reduce +=
    [<< ImmediateNumber{number[i:n]} >>, fold_immediate_number;
     << MemRegOff{'r; number[off:n]} >>, fold_mem_reg_off;
     << MemRegRegOffMul{'r1; 'r2; number[off:n]; number[mul:n]} >>, fold_mem_reg_reg_off_mul;
     << word_size >>, unfold_word_size;
     << header[i:n] >>, unfold_header;
     << header{number[i:n]} >>, fold_header;
     << eax >>, unfold_eax;
     << ebx >>, unfold_ebx;
     << ecx >>, unfold_ecx;
     << edx >>, unfold_edx;
     << esi >>, unfold_esi;
     << edi >>, unfold_edi;
     << esp >>, unfold_esp;
     << ebp >>, unfold_ebp;
     << next >>, unfold_next;
     << MapOperand{AssignRegisters{'registers}; ImmediateNumber[i:n]} >>, assign_reg_number;
     << MapOperand{AssignRegisters{'registers}; ImmediateLabel[label:t]{'R}} >>, assign_reg_label;
     << MapOperand{AssignRegisters{'registers}; ImmediateCLabel[label:t]{'R}} >>, assign_reg_clabel;
     << MapOperand{AssignRegisters{'registers}; Register{'v}} >>, assign_reg_register;
     << MapOperand{AssignRegisters{'registers}; SpillRegister{'v}} >>, assign_reg_spill;
     << MapOperand{AssignRegisters{'registers}; MemReg{'r}} >>, assign_reg_mem_reg;
     << MapOperand{AssignRegisters{'registers}; MemRegOff[i:n]{'r}} >>, assign_reg_mem_reg_off;
     << MapOperand{AssignRegisters{'registers}; MemRegRegOffMul[off:n, mul:n]{'r1; 'r2}} >>, assign_reg_mem_reg_reg_off_mul;
     << MapOperand{AssignRegisters{'registers}; RegisterLabel[label:t]} >>, assign_reg_reg_label;
     << LookupRegister[label1:t]{RegisterCons[label2:t]{'reg; 'rest}} >>,
     (lookup_reg_lookup_cons thenC reduce_meta_eq_tok)]

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
