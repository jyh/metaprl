doc <:doc<
   @begin[spelling]
   CPS SpillRegister dst vars
   @end[spelling]

   @begin[doc]
   @module[M_x86_spill]

   This module defines a tactic @tt[spillT] that takes as input the program
   and a set of variables to spill (as determined by the register allocator)
   and generates the appropriate spills, rewriting the assembly as needed.
   The tactic splits the live ranges of all spilled registers as an
   optimization.
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

doc <:doc<
   @begin[doc]
   @parents
   @end[doc]
>>
extends M_x86_backend
doc <:doc< @docoff >>

open Basic_tactics

open M_x86_inst_type
open M_x86_term
open M_util

(************************************************************************
 * Reduction resource
 *)

doc <:doc<
   @begin[doc]
   @resources

   The @tt{spill} resource provides a generic method for defining a method
   for spilling registers in a program.  The @conv[spillC] conversion can be
   used to apply this evaluator.  The implementation of the
   @tt{spill_resource} and the @tt[spillC] conversion rely on tables to
   store the shape of redices, together with the conversions for the
   reduction.

   @end[doc]
   @docoff
>>
let resource (term * conv, conv) spill =
   table_resource_info extract_data

let spillTopC_env e =
   get_resource_arg (env_arg e) get_spill_resource

let spillTopC = funC spillTopC_env

let spillC =
   repeatC (higherC spillTopC)

(************************************************************************
 * Generating spills.
 *)

doc <:doc<
   @begin[doc]
   @modsection{Generating spills}

   Code to spill registers is generated in two phases.
   @end[doc]
>>

(************************************************************************
 * Phase 1.
 *)

doc <:doc<
   @begin[doc]
   @modsubsection{Phase 1}

   When the register allocator first asks that a register be spilled, we
   make it a ``potential spill,'' meaning that we assign it a spill
   location, but leave it in a register.  The operand changes from <<
   Register{'v} >> to << SpillRegister{'v; 'spill} >> where << 'spill >> is
   the new spill location.  The following rules add the spill after a
   binding occurrence.
   @end[doc]
>>
prim_rw spill_mov :
   Mov{'src; dst. 'rest['dst]}
   <-->
   Mov{'src; dst.
   Spill["set"]{Register{'dst}; spill.
   'rest[SpillRegister{'dst; 'spill}]}}

prim_rw spill_inst1 :
   Inst1[opcode:s]{'src; dst. 'rest['dst]}
   <-->
   Inst1[opcode:s]{'src; dst.
   Spill["set"]{Register{'dst}; spill.
   'rest[SpillRegister{'dst; 'spill}]}}

prim_rw spill_inst2 :
   Inst2[opcode:s]{'src1; 'src2; dst. 'rest['dst]}
   <-->
   Inst2[opcode:s]{'src1; 'src2; dst.
   Spill["set"]{Register{'dst}; spill.
   'rest[SpillRegister{'dst; 'spill}]}}

prim_rw spill_inst3_2 :
   Inst3[opcode:s]{'src1; 'src2; 'src3; dst2, dst3. 'rest['dst2; 'dst3]}
   <-->
   Inst3[opcode:s]{'src1; 'src2; 'src3; dst2, dst3.
   Spill["set"]{Register{'dst2}; spill.
   'rest[SpillRegister{'dst2; 'spill}; 'dst3]}}

prim_rw spill_inst3_3 :
   Inst3[opcode:s]{'src1; 'src2; 'src3; dst2, dst3. 'rest['dst2; 'dst3]}
   <-->
   Inst3[opcode:s]{'src1; 'src2; 'src3; dst2, dst3.
   Spill["set"]{Register{'dst3}; spill.
   'rest['dst2; SpillRegister{'dst2; 'spill}]}}

prim_rw spill_shift :
   Shift[opcode:s]{'src1; 'src2; dst. 'rest['dst]}
   <-->
   Shift[opcode:s]{'src1; 'src2; dst.
   Spill["set"]{Register{'dst}; spill.
   'rest[SpillRegister{'dst; 'spill}]}}

prim_rw spill_set :
   Set[opcode:s]{'cc; 'src; dst. 'rest['dst]}
   <-->
   Set[opcode:s]{'cc; 'src; dst.
   Spill["set"]{Register{'dst}; spill.
   'rest[SpillRegister{'dst; 'spill}]}}

doc <:doc<
   @begin[doc]
   We define a conversion (implemented in @OCaml, and not shown here) for
   the first phase that searches for the spill binding occurrences and
   applies the appropriate rewrites.
   @end[doc]
   @docoff
>>
let phase1C vars =
   let convC inst =
      match inst with
         Mov (_, v, _) when SymbolSet.mem vars v ->
            spill_mov
       | Inst1Reg (_, _, v, _) when SymbolSet.mem vars v ->
            spill_inst1
       | Inst2Reg (_, _, _, v, _) when SymbolSet.mem vars v ->
            spill_inst2
       | Inst3Reg (_, _, _, _, v, _, _) when SymbolSet.mem vars v ->
            spill_inst3_2
       | Inst3Reg (_, _, _, _, _, v, _) when SymbolSet.mem vars v ->
            spill_inst3_3
       | ShiftReg (_, _, _, v, _) when SymbolSet.mem vars v ->
            spill_shift
       | SetReg (_, _, _, v, _) when SymbolSet.mem vars v ->
            spill_set
       | _ ->
            idC
   in
   let convC e =
      let inst =
         try Some (dest_inst_term (env_term e)) with
            RefineError _ ->
               None
      in
         match inst with
            Some inst ->
               convC inst
          | None ->
               idC
   in
      funC convC

doc <:doc<
   @begin[doc]
   In the next part of @tt[phase1], we find all instructions that now have a
   << SpillRegister{'v; 'spill} >> operand, and copy the operand.  This
   splits the live range, but keeps the spill location.  Note that we use
   this rewrite in reverse (i.e., rewrite the contractum into the redex).
   @end[doc]
>>
prim_rw spill_split bind{v. 'e['v]} :
   Spill["copy"]{SpillRegister{'v1; 'spill}; v2. 'e[SpillRegister{'v2; 'spill}]} <--> 'e[SpillRegister{'v1; 'spill}]

doc <:doc<
   @begin[doc]
   We define a conversion (implemented in @OCaml, and not shown here) to
   actually split the live range.
   @end[doc]
>>
let rec splitC_aux vars =
   match vars with
      [] ->
         idC
    | (v, spill) :: vars ->
         let convC e =
            let t = env_term e in

            (* Abstract the term for the rewrite argument *)
            let s = Lm_symbol.add ".hide" in
            let op = mk_operand_term (SpillRegister (v, spill)) in
            let abs = var_subst t op s in
            let bind = mk_bind1_term s abs in

            (* Make redex *)
            let t' = mk_inst_term (Spill (SpillCopy, SpillRegister (v, spill), v, t)) in
               foldC t' (spill_split bind) thenC splitC_aux vars
         in
            funC convC

let splitTopC =
   let get_regs e =
      let t = env_term e in
      let regs, operands =
         match dest_inst_spill t with
            Mov (op, _, _)
          | Inst1Mem (_, op, _)
          | SetMem (_, _, op, _) ->
               [], [op]
          | IMov (op, _, _)
          | Inst1Reg (_, op, _, _)
          | SetReg (_, _, op, _, _) ->
               [op], []
          | Inst2Mem (_, op1, op2, _)
          | ShiftMem (_, op1, op2, _)
          | Cmp (_, op1, op2, _) ->
               [], [op1; op2]
          | Inst2Reg (_, op, v, _, _)
          | ShiftReg (_, op, v, _, _) ->
               [v], [op]
          | Inst3Reg (_, op, v1, v2, _, _, _) ->
               [v1; v2], [op]
          | Jmp (_, op, args) ->
               args, [op]
          | Reserve (_, params) ->
               params, []
          | Jcc _
          | Comment _
          | Init _ ->
               [], []
          | Spill _
          | LabelFun _
          | Compilable _
          | LabelAsm _
          | LabelRec _
          | LabelDef _
          | LabelEnd ->
               raise (RefineError ("splitTopC", StringTermError ("illegal instruction", t)))
      in
      let rec regs_operand regs op =
         match op with
            ImmediateNumber _
          | ImmediateLabel _
          | ImmediateCLabel _
          | SpillMemory _
          | SpillRegister _
          | ContextRegister _ ->
               regs
          | Register r
          | MemReg r
          | MemRegOff (r, _) ->
               r :: regs
          | MemRegRegOffMul (r1, r2, _, _) ->
               r1 :: r2 :: regs
      in

      (* Get all the spill operands *)
      let regs = List.fold_left regs_operand regs operands in

      (* Collect only the spill operands *)
      let regs =
         List.fold_left (fun regs reg ->
               match reg with
                  SpillRegRegister _ ->
                     regs
                | SpillRegSpill (v, spill) ->
                     SymbolTable.add regs v spill) SymbolTable.empty regs
      in
      let regs =
         SymbolTable.fold (fun regs v spill ->
               (v, spill) :: regs) [] regs
      in
         regs
   in
   let convC e =
      let regs =
         try get_regs e with
            RefineError _ ->
               []
      in
         splitC_aux regs
   in
      funC convC

let splitC = sweepUpFailC splitTopC

doc <:doc<
   @begin[doc]
   Once the splits have been added, we cleanup the remaining instructions
   by removing spill variables.
   @end[doc]
>>
prim_rw register_spill_register :
   Register{SpillRegister{'v; 'spill}}
   <-->
   Register{'v}

prim_rw mem_reg_spill_register :
   MemReg{SpillRegister{'v; 'spill}}
   <-->
   MemReg{'v}

prim_rw mem_reg_off_spill_register :
   MemRegOff[off:n]{SpillRegister{'v; 'spill}}
   <-->
   MemRegOff[off:n]{'v}

prim_rw mem_reg_reg_off_mul_spill_register_1 :
   MemRegRegOffMul[off:n, mul:n]{SpillRegister{'v1; 'spill}; 'a2}
   <-->
   MemRegRegOffMul[off:n, mul:n]{'v1; 'a2}

prim_rw mem_reg_reg_off_mul_spill_register_2 :
   MemRegRegOffMul[off:n, mul:n]{'a1; SpillRegister{'v2; 'spill}}
   <-->
   MemRegRegOffMul[off:n, mul:n]{'a1; 'v2}

let resource spill +=
    [<< Register{SpillRegister{'v; 'spill}} >>, register_spill_register;
     << MemReg{SpillRegister{'v; 'spill}} >>, mem_reg_spill_register;
     << MemRegOff[off:n]{SpillRegister{'v; 'spill}} >>, mem_reg_off_spill_register;
     << MemRegRegOffMul[off:n, mul:n]{SpillRegister{'v1; 'spill}; 'a2} >>, mem_reg_reg_off_mul_spill_register_1;
     << MemRegRegOffMul[off:n, mul:n]{'a1; SpillRegister{'v2; 'spill}} >>, mem_reg_reg_off_mul_spill_register_2]

let phase1T vars =
   rw (sweepUpFailC (phase1C vars)) 0
   thenT rw splitC 0
   thenT rw spillC 0

(************************************************************************
 * Phase 2.
 *)

doc <:doc<
   @begin[doc]
   @modsubsection{Phase 2}

   In this section, we define the @tt[phase2T] tactic.  We assume that the
   live range of a variable has already been split.  If the register
   allocator chooses to spill one of the variables, we eliminate the
   register associated with that variable, forcing the fetch from the spill.

   The @tt[phase2T] tactic takes as input the set of spilled variables and
   uses the following rewrite.  @OCaml code (not listed here) is used to guide
   the application of the rewrite.

   @end[doc]
>>
prim_rw spill_fetch :
   Spill["copy"]{SpillRegister{'v1; 'spill}; v2. 'e['v2]}
   <-->
   Spill["get"]{SpillMemory{'spill}; v2. 'e['v2]}

doc <:doc< @docoff >>

let phase2C vars =
   let convC inst =
      match inst with
         Spill (SpillCopy, SpillRegister (v, _), _, _)
         when SymbolSet.mem vars v ->
            spill_fetch
       | _ ->
            idC
   in
   let convC e =
      let inst =
         try Some (dest_inst_term (env_term e)) with
            RefineError _ ->
               None
      in
         match inst with
            Some inst ->
               convC inst
          | None ->
               idC
   in
      funC convC

let phase2T vars =
   rw (sweepUpFailC (phase2C vars)) 0

(**************************************************************************
 * The spillT tactic
 *)

doc <:doc<
   @begin[doc]
   @modsection{The @tt[spillT] tactic}

   The main spill code generator, i.e., the @tt[spillT] tactic, gets a set
   of variables to spill from the register allocator.  It first classifies
   every variable in the program.

   @begin[enumerate]

   @item{
      A variable is a @tt[phase1] variable if it is the destination of a
      non-spill instruction.}

   @item{
      A variable is a @tt[phase2] variable if it is the destination of a
      @tt[SpillCopy]instruction.}

   @end[enumerate]

   @noindent The main spiller then runs @tt[phase1T] on the @tt[phase1] vars,
   and @tt[phase2T] on the @tt[phase2] vars.

   @end[doc]
   @docoff
>>

(*
 * Classify the vars by waling the entire program.
 *)
let classify t =
   let rec collect vars1 vars2 (Inst inst) =
      match inst with
         Mov (_, v, rest)
       | IMov (_, v, rest)
       | Inst1Reg (_, _, v, rest)
       | Inst2Reg (_, _, _, v, rest)
       | ShiftReg (_, _, _, v, rest)
       | SetReg (_, _, _, v, rest) ->
            collect (SymbolSet.add vars1 v) vars2 rest
       | Inst3Reg (_, _, _, _, v1, v2, rest) ->
            collect (SymbolSet.add (SymbolSet.add vars1 v1) v2) vars2 rest
       | Spill (SpillSet, Register v, _, rest)
       | Spill (SpillGet, SpillRegister (v, _), _, rest)
       | Spill (SpillCopy, SpillRegister (v, _), _, rest) ->
            collect vars1 (SymbolSet.add vars2 v) rest
       | Spill (_, _, _, rest)
       | Inst1Mem (_, _, rest)
       | Inst2Mem (_, _, _, rest)
       | ShiftMem (_, _, _, rest)
       | Cmp (_, _, _, rest)
       | SetMem (_, _, _, rest)
       | Comment (_, rest)
       | LabelFun (_, rest)
       | Compilable rest ->
            collect vars1 vars2 rest
       | Jcc (_, _, rest1, rest2)
       | LabelRec (_, rest1, _, rest2)
       | LabelDef (_, rest1, rest2) ->
            let vars1, vars2 = collect vars1 vars2 rest1 in
               collect vars1 vars2 rest2
       | Jmp _
       | Reserve _
       | Init _
       | LabelAsm _
       | LabelEnd ->
            vars1, vars2
   in
      collect SymbolSet.empty SymbolSet.empty (dest_inst t)

let spillT_aux vars p =
   (* Classify all the vars *)
   let vars1, vars2 = classify (concl p) in
   let vars1 = SymbolSet.diff vars1 vars2 in

   (* Check that we know how to spill all the vars *)
(*
   let () =
      let vars_all = SymbolSet.union vars1 vars2 in
      let other_vars = SymbolSet.diff vars vars_all in
         if not (SymbolSet.is_empty other_vars) then
            let s = Lm_symbol.to_string (SymbolSet.choose other_vars) in
               raise (RefineError ("spillT", StringStringError ("don't know how to spill", s)))
   in
*)

   (* Limit to only those vars we know *)
   let vars1 = SymbolSet.inter vars1 vars in
   let vars2 = SymbolSet.inter vars2 vars in

   (* Apply only the phases that matter *)
   let tac =
      if SymbolSet.is_empty vars1 then
         if SymbolSet.is_empty vars2 then
            raise (RefineError ("spillT", StringError "no vars to spill"))
         else
            phase2T vars2
      else if SymbolSet.is_empty vars2 then
         phase1T vars1
      else
         phase1T vars1 thenT phase2T vars2
   in
      tac

let spillT vars =
   funT (spillT_aux vars)

(*
 * Debug version.
 *)
let spillST s =
   spillT (SymbolSet.singleton (Lm_symbol.add s))

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
