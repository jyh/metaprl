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
extends X86_asm

open Refiner.Refiner.Term

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

(*
 * Term operations.
 *)
val dest_inst_term : term -> inst
val dest_operand_term : term -> operand

val mk_register_term : string -> term

val mk_let_term : string -> term -> term -> term

(*
 * Get operands in arbitrary order.
 *)
val operands_of_inst : inst -> term list

(*
 * Addr of the next instruction.
 *)
val next_inst : inst -> int * term

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
