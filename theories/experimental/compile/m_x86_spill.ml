(*
 * Split a live range.
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
extends X86_term
extends M_util

open Printf
open Mp_debug

open X86_term
open M_util

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermAddr
open Refiner.Refiner.RefineError

open Mp_resource
open Simple_print.SimplePrint
open Term_match_table

open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Tactic_type.Sequent

(************************************************************************
 * Reduction resource
 *)

(*!
 * @begin[doc]
 * @resources
 *
 * @bf{The @Comment!resource[spill_resource]}
 *
 * The @tt{spill} resource provides a generic method for
 * defining @emph{CPS transformation}.  The @conv[spillC] conversion
 * can be used to apply this evaluator.
 *
 * The implementation of the @tt{spill_resource} and the @tt[spillC]
 * conversion rely on tables to store the shape of redices, together with the
 * conversions for the reduction.
 *
 * @docoff
 * @end[doc]
 *)
let resource spill =
   table_resource_info identity extract_data

let spillTopC_env e =
   get_resource_arg (env_arg e) get_spill_resource

let spillTopC = funC spillTopC_env

let spillC =
   repeatC (higherC spillTopC)

(************************************************************************
 * Spill code.
 *)

(*
 * We split a live range by creating a new spill.
 * The first step is to apply this rewrite in
 * the reverse direction at the point where you
 * want to place the spill.
 *)
prim_rw reduce_let :
   Let{Register{'v1}; v2. 'e['v2]} <--> 'e['v1]

(*
 * The second rewrite converts a normal move to spill code.
 * Once the spill is added, the Let should be migrated down
 * as far as possible.
 *)
prim_rw spill :
   Let{'a; v. 'e['v]}
   <-->
   LetSpill["set"]{'a; spill.
   LetSpill["get"]{'spill; v. 'e['v]}}

(*
 * Spill-migration.
 *)
prim_rw spill_let :
   LetSpill["get"]{'a1; v1. Let{'a2; v2. 'e['v1; 'v2]}}
   <-->
   Let{'a2; v2. LetSpill["get"]{'a1; v1. 'e['v1; 'v2]}}

prim_rw spill_inst1 :
   LetSpill["get"]{'a; v. Inst1[opcode:s]{'dst; 'rest['v]}}
   <-->
   Inst1[opcode:s]{'dst; LetSpill["get"]{'a; v. 'rest['v]}}

prim_rw spill_inst2 :
   LetSpill["get"]{'a; v. Inst2[opcode:s]{'dst; 'src; 'rest['v]}}
   <-->
   Inst2[opcode:s]{'dst; 'src; LetSpill["get"]{'a; v. 'rest['v]}}

prim_rw spill_instm :
   LetSpill["get"]{'a; v. Instm[opcode:s]{'dst1; 'dst2; 'src; 'rest['v]}}
   <-->
   Instm[opcode:s]{'dst1; 'dst2; 'src; LetSpill["get"]{'a; v. 'rest['v]}}

prim_rw spill_shift :
   LetSpill["get"]{'a; v. Shift[opcode:s]{'dst; 'src; 'rest['v]}}
   <-->
   Shift[opcode:s]{'dst; 'src; LetSpill["get"]{'a; v. 'rest['v]}}

prim_rw spill_cmp :
   LetSpill["get"]{'a; v. Cmp[opcode:s]{'src1; 'src2; 'rest['v]}}
   <-->
   Cmp[opcode:s]{'src1; 'src2; LetSpill["get"]{'a; v. 'rest['v]}}

prim_rw spill_set :
   LetSpill["get"]{'a; v. Set[opcode:s]{'cc; 'dst; 'rest['v]}}
   <-->
   Set[opcode:s]{'cc; 'dst; LetSpill["get"]{'a; v. 'rest['v]}}

prim_rw spill_comment :
   LetSpill["get"]{'a; v. Comment[comment:s]{'rest['v]}}
   <-->
   Comment[comment:s]{LetSpill["get"]{'a; v. 'rest['v]}}

(*
 * Add the rewrites to the resource.
 *)
let resource spill +=
    [<< LetSpill["get"]{'a1; v1. Let{'a2; v2. 'e['v1; 'v2]}} >>, spill_let;
     << LetSpill["get"]{'a; v. Inst1[opcode:s]{'dst; 'rest['v]}} >>, spill_inst1;
     << LetSpill["get"]{'a; v. Inst2[opcode:s]{'dst; 'src; 'rest['v]}} >>, spill_inst2;
     << LetSpill["get"]{'a; v. Instm[opcode:s]{'dst1; 'dst2; 'src; 'rest['v]}} >>, spill_instm;
     << LetSpill["get"]{'a; v. Shift[opcode:s]{'dst; 'src; 'rest['v]}} >>, spill_shift;
     << LetSpill["get"]{'a; v. Cmp[opcode:s]{'src1; 'src2; 'rest['v]}} >>, spill_cmp;
     << LetSpill["get"]{'a; v. Set[opcode:s]{'cc; 'dst; 'rest['v]}} >>, spill_set;
     << LetSpill["get"]{'a; v. Comment[comment:s]{'rest['v]}} >>, spill_comment]

(*
 * Test whether a variable is mentioned in an operand.
 *)
let mem_operand v op =
   match op with
      ImmediateNumber _
    | ImmediateLabel _
    | ImmediateCLabel _
    | SpillRegister _ ->
         false
    | Register v'
    | MemReg v'
    | MemRegOff (_, v') ->
         v' = v
    | MemRegRegOffMul (_, _, v1, v2) ->
         v1 = v || v2 = v

let mem_operands v ops =
   List.exists (mem_operand v) ops

(*
 * Spill a particular variable.
 * We search down from the root until we find the first
 * place the variable is used, and we spill it right afterwards.
 *)
let splitC s =
   (* Have the rewriter search for the outermost occurrence *)
   let convC e =
      let t = env_term e in
      let inst = dest_inst_term t in
      let operands = List.map dest_operand_term (operands_of_inst inst) in
      let addr, t = next_inst inst in
         if mem_operands s operands then
            let r = mk_register_term s in
            let t = mk_let_term s r t in
               addrC [addr] (foldC t reduce_let thenC spill)
         else
            failC
   in
      funC convC

(*
 * Split a spill.
 *)
let rec spillT vars =
   match vars with
      v :: vars ->
         rwh (splitC v) 0 thenT spillT vars
    | [] ->
         rw spillC 0

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
