(*
 * Utilities for manipulating instructions.
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
extends X86_asm

(*
 * Map over all operands in the program.
 *)
declare MapOperands{'arg; 'code}
declare MapOperand{'arg; 'operand}

(*
 * Display forms.
 *)
dform map_operands_df : MapOperands{'arg; 'code} =
   szone pushm[3] bf["map("] slot{'arg} `") over" popm ezone hspace slot{'code}

dform map_operand_df : MapOperand{'arg; 'operand} =
   szone pushm[3] bf["apply("] slot{'arg} bf[","] hspace slot{'operand} bf[")"] popm ezone

(*
 * Assign to instructions.
 *)
prim_rw map_operands_let :
   MapOperands{'arg; Let{'src; dst. 'rest['dst]}}
   <-->
   Let{MapOperand{'arg; 'src}; dst. MapOperands{'arg; 'rest['dst]}}

prim_rw map_operands_inst1 :
   MapOperands{'arg; Inst1[opcode:s]{'dst; 'rest}}
   <-->
   Inst1[opcode:s]{MapOperand{'arg; 'dst}; MapOperands{'arg; 'rest}}

prim_rw map_operands_inst2 :
   MapOperands{'arg; Inst2[opcode:s]{'dst; 'src; 'rest}}
   <-->
   Inst2[opcode:s]{MapOperand{'arg; 'dst};
                   MapOperand{'arg; 'src};
                   MapOperands{'arg; 'rest}}

prim_rw map_operands_instm :
   MapOperands{'arg; Instm[opcode:s]{'dst1; 'dst2; 'src; 'rest}}
   <-->
   Instm[opcode:s]{MapOperand{'arg; 'dst1};
                   MapOperand{'arg; 'dst2};
                   MapOperand{'arg; 'src};
                   MapOperands{'arg; 'rest}}

prim_rw map_operands_shift :
   MapOperands{'arg; Shift[opcode:s]{'dst; 'src; 'rest}}
   <-->
   Shift[opcode:s]{MapOperand{'arg; 'dst};
                   MapOperand{'arg; 'src};
                   MapOperands{'arg; 'rest}}

prim_rw map_operands_cmp :
   MapOperands{'arg; Cmp[opcode:s]{'src1; 'src2; 'rest}}
   <-->
   Cmp[opcode:s]{MapOperand{'arg; 'src1};
                 MapOperand{'arg; 'src2};
                 MapOperands{'arg; 'rest}}

prim_rw map_operands_set :
   MapOperands{'arg; Set[opcode:s]{'cc; 'dst; 'rest}}
   <-->
   Set[opcode:s]{'cc;
                 MapOperand{'arg; 'dst};
                 MapOperands{'arg; 'rest}}

prim_rw map_operands_jmp_1 :
   MapOperands{'arg; Jmp[opcode:s]{'f; 'a1}}
   <-->
   Jmp[opcode:s]{MapOperand{'arg; 'f};
                 MapOperand{'arg; 'a1}}

prim_rw map_operands_jmp_2 :
   MapOperands{'arg; Jmp[opcode:s]{'f; 'a1; 'a2}}
   <-->
   Jmp[opcode:s]{MapOperand{'arg; 'f};
                 MapOperand{'arg; 'a1};
                 MapOperand{'arg; 'a2}}

prim_rw map_operands_jmp_3 :
   MapOperands{'arg; Jmp[opcode:s]{'f; 'a1; 'a2; 'a3}}
   <-->
   Jmp[opcode:s]{MapOperand{'arg; 'f};
                 MapOperand{'arg; 'a1};
                 MapOperand{'arg; 'a2};
                 MapOperand{'arg; 'a3}}

prim_rw map_operands_jcc_1 :
   MapOperands{'arg; Jcc[opcode:s]{'cc; 'f; 'a1; 'rest}}
   <-->
   Jcc[opcode:s]{'cc;
                 MapOperand{'arg; 'f};
                 MapOperand{'arg; 'a1};
                 MapOperands{'arg; 'rest}}

prim_rw map_operands_jcc_2 :
   MapOperands{'arg; Jcc[opcode:s]{'cc; 'f; 'a1; 'a2; 'rest}}
   <-->
   Jcc[opcode:s]{'cc;
                 MapOperand{'arg; 'f};
                 MapOperand{'arg; 'a1};
                 MapOperand{'arg; 'a2};
                 MapOperands{'arg; 'rest}}

prim_rw map_operands_jcc_3 :
   MapOperands{'arg; Jcc[opcode:s]{'cc; 'f; 'a1; 'a2; 'a3; 'rest}}
   <-->
   Jcc[opcode:s]{'cc;
                 MapOperand{'arg; 'f};
                 MapOperand{'arg; 'a1};
                 MapOperand{'arg; 'a2};
                 MapOperand{'arg; 'a3};
                 MapOperands{'arg; 'rest}}

prim_rw map_operands_comment :
   MapOperands{'arg; Comment[comment:s]{'rest}}
   <-->
   Comment[comment:s]{MapOperands{'arg; 'rest}}

prim_rw map_operands_label_rec :
   MapOperands{'arg; LabelRec{R1. 'fields['R1]; R2. 'rest['R2]}}
   <-->
   LabelRec{R1. MapOperands{'arg; 'fields['R1]};
            R2. MapOperands{'arg; 'rest['R2]}}

prim_rw map_operands_label_def :
   MapOperands{'arg; LabelDef{'label; 'code; 'rest}}
   <-->
   LabelDef{'label; MapOperands{'arg; 'code}; MapOperands{'arg; 'rest}}

prim_rw map_operands_label_end :
   MapOperands{'arg; LabelEnd}
   <-->
   LabelEnd

prim_rw map_operands_label_fun :
   MapOperands{'arg; LabelFun{v. 'insts['v]}}
   <-->
   LabelFun{v. MapOperands{'arg; 'insts['v]}}

let resource reduce +=
    [<< MapOperands{'registers; Let{'src; dst. 'rest['dst]}} >>, map_operands_let;
     << MapOperands{'registers; Inst1[opcode:s]{'dst; 'rest}} >>, map_operands_inst1;
     << MapOperands{'registers; Inst2[opcode:s]{'dst; 'src; 'rest}} >>, map_operands_inst2;
     << MapOperands{'registers; Instm[opcode:s]{'dst1; 'dst2; 'src; 'rest}} >>, map_operands_instm;
     << MapOperands{'registers; Shift[opcode:s]{'dst; 'src; 'rest}} >>, map_operands_shift;
     << MapOperands{'registers; Cmp[opcode:s]{'src1; 'src2; 'rest}} >>, map_operands_cmp;
     << MapOperands{'registers; Set[opcode:s]{'cc; 'dst; 'rest}} >>, map_operands_set;
     << MapOperands{'registers; Jmp[opcode:s]{'f; 'a1}} >>, map_operands_jmp_1;
     << MapOperands{'registers; Jmp[opcode:s]{'f; 'a1; 'a2}} >>, map_operands_jmp_2;
     << MapOperands{'registers; Jmp[opcode:s]{'f; 'a1; 'a2; 'a3}} >>, map_operands_jmp_3;
     << MapOperands{'registers; Jcc[opcode:s]{'cc; 'f; 'a1; 'rest}} >>, map_operands_jcc_1;
     << MapOperands{'registers; Jcc[opcode:s]{'cc; 'f; 'a1; 'a2; 'rest}} >>, map_operands_jcc_2;
     << MapOperands{'registers; Jcc[opcode:s]{'cc; 'f; 'a1; 'a2; 'a3; 'rest}} >>, map_operands_jcc_3;
     << MapOperands{'registers; Comment[comment:s]{'rest}} >>, map_operands_comment;
     << MapOperands{'registers; LabelRec{R1. 'fields['R1]; R2. 'rest['R2]}} >>, map_operands_label_rec;
     << MapOperands{'registers; LabelDef{'label; 'code; 'rest}} >>, map_operands_label_def;
     << MapOperands{'registers; LabelEnd} >>, map_operands_label_end;
     << MapOperands{'registers; LabelFun{v. 'insts['v]}} >>, map_operands_label_fun]

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
