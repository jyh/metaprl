(*
 * Instruction destruction and creation.
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
extends M_x86_inst_type

open Refiner.Refiner.Term

open M_x86_inst_type

(*
 * Main destructors.
 *)
val dest_inst : term -> inst
val dest_inst_term : term -> term_inst
val dest_inst_spill : term -> spill_inst
val dest_operand_term : term -> operand

(*
 * Make constructors.
 *)
val mk_inst : inst -> term
val mk_inst_term : term_inst -> term
val mk_inst_spill : spill_inst -> term

val mk_operand_term : operand -> term

(*
 * Other destructors.
 *)
val is_init_label_asm  : ('a, 'b) poly_inst -> bool
val label_of_asm_label : label -> label -> label
val label_of_label_asm : ('a, 'b) poly_inst -> label

(*
 * Strings for opcodes.
 *)
val mk_cc           : cc -> string
val invert_cc       : cc -> cc

val mk_inst1_opcode : inst1_opcode -> string
val mk_inst2_opcode : inst2_opcode -> string
val mk_inst3_opcode : inst3_opcode -> string
val mk_shift_opcode : shift_opcode -> string
val mk_set_opcode   : set_opcode   -> string
val mk_cmp_opcode   : cmp_opcode   -> string
val mk_jmp_opcode   : jmp_opcode   -> string
val mk_jcc_opcode   : jcc_opcode   -> string

(*
 * Get operands in arbitrary order.
 *)
val operands_of_inst : (reg, 'a) poly_inst -> operand list

(*
 * Addr of the next instruction.
 *)
val next_inst : term_inst -> int * term

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
