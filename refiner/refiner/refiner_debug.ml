(*
 * Run two refiners in parallel for debugging purposes.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 1998 Jason Hickey, Cornell University
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
 * Author: Aleksey Nogin <nogin@cs.caltech.edu>
 *)

open Term_sig
open Term_shape_sig
open Refiner_sig
open Termmod_sig
open Rewrite_sig

open Lm_symbol
open Lm_printf
open Lm_array_util
open Opname

module MakeRefinerDebug (Refiner1 : RefinerSig) (Refiner2 : RefinerSig) = struct
   module Type1 = Refiner1.TermType
   module Type2 = Refiner2.TermType
   module Term1 = Refiner1.Term
   module Term2 = Refiner2.Term
   module TermAddr1 = Refiner1.TermAddr
   module TermAddr2 = Refiner2.TermAddr
   module TermOp1 = Refiner1.TermOp
   module TermOp2 = Refiner2.TermOp
   module TermMan1 = Refiner1.TermMan
   module TermMan2 = Refiner2.TermMan
   module TermMeta1 = Refiner1.TermMeta
   module TermMeta2 = Refiner2.TermMeta
   module TermSubst1 = Refiner1.TermSubst
   module TermSubst2 = Refiner2.TermSubst
   module TermShape1 = Refiner1.TermShape
   module TermShape2 = Refiner2.TermShape
   module SeqHyp1 = Refiner1.Term.SeqHyp
   module SeqHyp2 = Refiner2.Term.SeqHyp
   module Err1 = Refiner1.RefineError
   module Err2 = Refiner2.RefineError
   module Rewrite1 = Refiner1.Rewrite
   module Rewrite2 = Refiner2.Rewrite

   module TermType = struct
      type term = Type1.term * Type2.term
      type bound_term = Type1.bound_term * Type2.bound_term
      type operator = Type1.operator * Type2.operator
      type param = Type1.param * Type2.param
      type address = TermAddr1.address * TermAddr2.address
      type level_exp_var = Type1.level_exp_var * Type2.level_exp_var
      type level_exp = Type1.level_exp * Type2.level_exp
      type seq_hyps = Type1.seq_hyps * Type2.seq_hyps
      type shape = TermShape1.shape * TermShape2.shape
      type rewrite_rule = Rewrite1.rewrite_rule * Rewrite2.rewrite_rule
      type rewrite_redex = Rewrite1.rewrite_redex * Rewrite2.rewrite_redex

      type level_exp_var' = { le_var : var; le_offset : int }
      type level_exp' = { le_const : int; le_vars : level_exp_var list }
      type operator' = { op_name : opname; op_params : param list }
      type term' = { term_op : operator; term_terms : bound_term list }
      type bound_term' = { bvars : var list; bterm : term }
      type object_id = param list
      type param' = (level_exp, param) poly_param
      type meta_term = term poly_meta_term
      type hypothesis = term poly_hypothesis
      type esequent = { sequent_args : term; sequent_hyps : seq_hyps; sequent_concl : term }

      type rewrite_item =
         RewriteTerm of term
       | RewriteFun of (term list -> term)
       | RewriteContext of (term -> term list -> term)
       | RewriteString of string rewrite_param
       | RewriteNum of Lm_num.num rewrite_param
       | RewriteLevel of level_exp

      type match_param =
         MatchNumber of Lm_num.num * int option
       | MatchString of string
       | MatchToken of string
       | MatchVar of var
       | MatchLevel of level_exp
       | MatchUnsupported

      type match_term =
         MatchTerm of string list * match_param list * bound_term' list
       | MatchSequent of string list * match_term list * hypothesis list * term

   end

   open TermType

   module RefineError = struct
      module ErrTypes = struct
         module Types = TermType
         type address = TermType.address
      end

      type match_type =
         ParamMatch of param
       | VarMatch of var
       | TermMatch of term
       | TermMatch2 of term * term
       | BTermMatch of bound_term
       | HypMatch of seq_hyps

      type refine_error =
         GenericError

       | ToploopIgnoreError

       | StringError of string
       | IntError of int
       | TermError of term
       | StringIntError of string * int
       | StringStringError of string * string
       | StringVarError of string * var
       | StringTermError of string * term
       | StringWrapError of string * refine_error
       | SubgoalError of int * string * refine_error
       | PairError of string * refine_error * string * refine_error

       | NodeError of string * term * (string * refine_error) list
       | AddressError of address * term

       | TermMatchError of term * string
       | TermPairError of term * term
       | MetaTermMatchError of meta_term

       | RewriteBoundSOVar of var
       | RewriteFreeSOVar of var
       | RewriteSOVarArity of var
       | RewriteBoundParamVar of var
       | RewriteFreeParamVar of var
       | RewriteBadRedexParam of param
       | RewriteNoRuleOperator
       | RewriteBadMatch of match_type
       | RewriteAllSOInstances of var
       | RewriteMissingContextArg of var
       | RewriteStringError of string
       | RewriteStringOpnameOpnameError of string * opname * opname
       | RewriteAddressError of address * string * refine_error
       | RewriteFreeContextVar of var * var

      exception RefineError of string * refine_error

      let generic_refiner_exn = RefineError("generic", GenericError)

   end

   open RefineError

   (* Helper functions *)
   let lev2_of_lev1 lev =
      let { Type1.le_var = v; Type1.le_offset = i } = Term1.dest_level_var lev in
         Term2.mk_level_var v i

   let levex2_of_levex1 levex =
      let { Type1.le_const = c; Type1.le_vars = vs } = Term1.dest_level levex in
      Term2.mk_level c (List.map lev2_of_lev1 vs)

   let rec param2_of_param1 p =
      let p =
         match Term1.dest_param p with
            (Number _ | String _ | Token _ | Var _ | MNumber _ | MString _ | MToken _ | Quote) as p -> p
          | MLevel l -> MLevel (levex2_of_levex1 l)
          | ObId pl -> ObId (List.map param2_of_param1 pl)
          | ParamList pl -> ParamList (List.map param2_of_param1 pl)
      in
         Term2.make_param p

   let op2_of_op1 op =
      let { Type1.op_name = name; Type1.op_params = pl } = Term1.dest_op op in
         Term2.mk_op name (List.map param2_of_param1 pl)

   let rec term2_of_term1 t =
      if Term1.is_var_term t then
         Term2.mk_var_term (Term1.dest_var t)
      else if TermMan1.is_so_var_term t then
         let v, vs, ts = TermMan1.dest_so_var t in
            TermMan2.mk_so_var_term v vs (List.map term2_of_term1 ts)
      else if TermMan1.is_sequent_term t then
         let { Type1.sequent_args = a; Type1.sequent_hyps = h; Type1.sequent_concl = c } = TermMan1.explode_sequent t in
            TermMan2.mk_sequent_term {
               Type2.sequent_args = term2_of_term1 a;
               Type2.sequent_hyps = hyps2_of_hyps1 h;
               Type2.sequent_concl = term2_of_term1 c
            }
      else
         let { Type1.term_op = op; Type1.term_terms = btl } = Term1.dest_term t in
            Term2.mk_term (op2_of_op1 op) (List.map bterm2_of_bterm1 btl)

   and bterm2_of_bterm1 bt =
      let { Type1.bvars = vs; Type1.bterm = bt } = Term1.dest_bterm bt in
         Term2.mk_bterm vs (term2_of_term1 bt)

   and hyp2_of_hyp1 = function
      Hypothesis (v, t) -> Hypothesis(v, term2_of_term1 t)
    | Context (v, vs, ts) -> Context (v, vs, List.map term2_of_term1 ts)

   and hyps2_of_hyps1 h =
      SeqHyp2.of_list (List.map hyp2_of_hyp1 (SeqHyp1.to_list h))

   let lev1_of_lev2 lev =
      let { Type2.le_var = v; Type2.le_offset = i } = Term2.dest_level_var lev in
         Term1.mk_level_var v i

   let levex1_of_levex2 levex =
      let { Type2.le_const = c; Type2.le_vars = vs } = Term2.dest_level levex in
      Term1.mk_level c (List.map lev1_of_lev2 vs)

   let rec param1_of_param2 p =
      let p =
         match Term2.dest_param p with
            (Number _ | String _ | Token _ | Var _ | MNumber _ | MString _ | MToken _ | Quote) as p -> p
          | MLevel l -> MLevel (levex1_of_levex2 l)
          | ObId pl -> ObId (List.map param1_of_param2 pl)
          | ParamList pl -> ParamList (List.map param1_of_param2 pl)
      in
         Term1.make_param p

   let op1_of_op2 op =
      let { Type2.op_name = name; Type2.op_params = pl } = Term2.dest_op op in
         Term1.mk_op name (List.map param1_of_param2 pl)

   let rec term1_of_term2 t =
      if Term2.is_var_term t then
         Term1.mk_var_term (Term2.dest_var t)
      else if TermMan2.is_so_var_term t then
         let v, vs, ts = TermMan2.dest_so_var t in
            TermMan1.mk_so_var_term v vs (List.map term1_of_term2 ts)
      else if TermMan2.is_sequent_term t then
         let { Type2.sequent_args = a; Type2.sequent_hyps = h; Type2.sequent_concl = c } = TermMan2.explode_sequent t in
            TermMan1.mk_sequent_term {
               Type1.sequent_args = term1_of_term2 a;
               Type1.sequent_hyps = hyps1_of_hyps2 h;
               Type1.sequent_concl = term1_of_term2 c
            }
      else
         let { Type2.term_op = op; Type2.term_terms = btl } = Term2.dest_term t in
            Term1.mk_term (op1_of_op2 op) (List.map bterm1_of_bterm2 btl)

   and bterm1_of_bterm2 bt =
      let { Type2.bvars = vs; Type2.bterm = bt } = Term2.dest_bterm bt in
         Term1.mk_bterm vs (term1_of_term2 bt)

   and hyp1_of_hyp2 = function
      Hypothesis (v, t) -> Hypothesis(v, term1_of_term2 t)
    | Context (v, vs, ts) -> Context (v, vs, List.map term1_of_term2 ts)

   and hyps1_of_hyps2 h =
      SeqHyp1.of_list (List.map hyp1_of_hyp2 (SeqHyp2.to_list h))

   let hyps_of_hyps1 h = h, (hyps2_of_hyps1 h)
   let param_of_param1 p = p, (param2_of_param1 p)
   let bterm_of_bterm1 bt = bt, (bterm2_of_bterm1 bt)

   let term_of_term1 t = t, (term2_of_term1 t)
   let term_of_term2 t = (term1_of_term2 t), t

   let rec mterm_of_mterm1 = function
      MetaTheorem t -> MetaTheorem (term_of_term1 t)
    | MetaImplies (mt1, mt2) -> MetaImplies (mterm_of_mterm1 mt1, mterm_of_mterm1 mt2)
    | MetaFunction (t, mt1, mt2) -> MetaFunction (term_of_term1 t, mterm_of_mterm1 mt1, mterm_of_mterm1 mt2)
    | MetaIff (mt1, mt2) -> MetaIff (mterm_of_mterm1 mt1, mterm_of_mterm1 mt2)
    | MetaLabeled (s, mt) -> MetaLabeled (s, mterm_of_mterm1 mt)

   let mtype_of_mtype1 = function
      Err1.ParamMatch p -> ParamMatch (param_of_param1 p)
    | Err1.VarMatch v -> VarMatch v
    | Err1.TermMatch t -> TermMatch (term_of_term1 t)
    | Err1.TermMatch2 (t1, t2) -> TermMatch2 (term_of_term1 t1, term_of_term1 t2)
    | Err1.BTermMatch bt -> BTermMatch (bterm_of_bterm1 bt)
    | Err1.HypMatch h -> HypMatch (hyps_of_hyps1 h)

   let addr_of_addr1 _ =
      (* XXX: HACK: this is fake *)
      TermAddr1.make_address [], TermAddr2.make_address []

   let rec re_of_re1 = function
    | Err1.GenericError -> GenericError
    | Err1.ToploopIgnoreError -> ToploopIgnoreError
    | Err1.StringError s -> StringError (s)
    | Err1.IntError i -> IntError (i)
    | Err1.TermError t -> TermError (term_of_term1 t)
    | Err1.StringIntError (s0, i1) -> StringIntError (s0, i1)
    | Err1.StringStringError (s0, s1) -> StringStringError (s0, s1)
    | Err1.StringVarError (s0, v1) -> StringVarError (s0, v1)
    | Err1.StringTermError (s0, t1) -> StringTermError (s0, term_of_term1 t1)
    | Err1.StringWrapError (s0, re1) -> StringWrapError (s0, re_of_re1 re1)
    | Err1.SubgoalError (i0, s1, re2) -> SubgoalError (i0, s1, re_of_re1 re2)
    | Err1.PairError (s0, re1, s2, re3) -> PairError (s0, re_of_re1 re1, s2, re_of_re1 re3)
    | Err1.NodeError (s0, t1, srel) -> NodeError (s0, term_of_term1 t1, List.map sre_of_sre1 srel)
    | Err1.AddressError (a0, t1) -> AddressError (addr_of_addr1 a0, term_of_term1 t1)
    | Err1.TermMatchError (t0, s1) -> TermMatchError (term_of_term1 t0, s1)
    | Err1.TermPairError (t0, t1) -> TermPairError (term_of_term1 t0, term_of_term1 t1)
    | Err1.MetaTermMatchError mt -> MetaTermMatchError (mterm_of_mterm1 mt)
    | Err1.RewriteBoundSOVar v -> RewriteBoundSOVar (v)
    | Err1.RewriteFreeSOVar v -> RewriteFreeSOVar (v)
    | Err1.RewriteSOVarArity v -> RewriteSOVarArity (v)
    | Err1.RewriteBoundParamVar v -> RewriteBoundParamVar (v)
    | Err1.RewriteFreeParamVar v -> RewriteFreeParamVar (v)
    | Err1.RewriteBadRedexParam p -> RewriteBadRedexParam (param_of_param1 p)
    | Err1.RewriteNoRuleOperator -> RewriteNoRuleOperator
    | Err1.RewriteBadMatch mt -> RewriteBadMatch (mtype_of_mtype1 mt)
    | Err1.RewriteAllSOInstances v -> RewriteAllSOInstances (v)
    | Err1.RewriteMissingContextArg v -> RewriteMissingContextArg (v)
    | Err1.RewriteStringError s -> RewriteStringError (s)
    | Err1.RewriteStringOpnameOpnameError (s0, o1, o2) -> RewriteStringOpnameOpnameError (s0, o1, o2)
    | Err1.RewriteAddressError (a0, s1, re2) -> RewriteAddressError (addr_of_addr1 a0, s1, re_of_re1 re2)
    | Err1.RewriteFreeContextVar (v0, v1) -> RewriteFreeContextVar (v0, v1)

   and sre_of_sre1 (s, re) =
      s, re_of_re1 re

   let print_term_ref = ref (fun _ _ -> raise (Failure "Refiner_debug.Term.print_term: printer not installed"))

   let print_term out (t: term) =
      !print_term_ref out t

   let rec print_term_list out = function
      [t] ->
         print_term out t
    | h::t ->
         print_term out h;
         output_string out ", ";
         print_term_list out t
    | [] ->
         ()

   type 'a wrap =
      Val of 'a
    | Err of exn

   let wrap1 f a =
      try Val (f a) with exn -> Err exn

   let wrap_plus f a =
      match f with
         Val f -> wrap1 f a
       | (Err _) as err -> err

   let wrap2 f a1 = wrap_plus (wrap1 f a1)
   let wrap3 f a1 a2 = wrap_plus (wrap2 f a1 a2)
   let wrap4 f a1 a2 a3 = wrap_plus (wrap3 f a1 a2 a3)
   let wrap5 f a1 a2 a3 a4 = wrap_plus (wrap4 f a1 a2 a3 a4)
   let wrap6 f a1 a2 a3 a4 a5 = wrap_plus (wrap5 f a1 a2 a3 a4 a5)
   let wrap7 f a1 a2 a3 a4 a5 a6 = wrap_plus (wrap6 f a1 a2 a3 a4 a5 a6)
   let wrap8 f a1 a2 a3 a4 a5 a6 a7 = wrap_plus (wrap7 f a1 a2 a3 a4 a5 a6 a7)
   let wrap9 f a1 a2 a3 a4 a5 a6 a7 a9 = wrap_plus (wrap8 f a1 a2 a3 a4 a5 a6 a7 a9)

   let split = List.split

   let split_opt = function
      None -> None, None
    | Some (a, b) -> Some a, Some b

   let split_pop (po, (p1, p2)) =
      let po1, po2 = split_opt po in ((po1, p1), (po2, p2))

   let split_popl l =
      split (List.map split_pop l)

   let split_term' { term_op = (op1, op2); term_terms = btl } =
      let btl1, btl2 = split btl in
         { Type1.term_op = op1; Type1.term_terms = btl1 },
         { Type2.term_op = op2; Type2.term_terms = btl2 }

   let split_bterm' { bvars = vs; bterm = bt1, bt2 } =
      { Type1.bvars = vs; Type1.bterm = bt1 },
      { Type2.bvars = vs; Type2.bterm = bt2 }

   let split_op' { op_name = name; op_params = pars } =
      let pl1, pl2 = split pars in
         { Type1.op_name = name; Type1.op_params = pl1 },
         { Type2.op_name = name; Type2.op_params = pl2 }

   let split_level_exp_var' { le_var = v; le_offset = i } =
      { Type1.le_var = v; Type1.le_offset = i },
      { Type2.le_var = v; Type2.le_offset = i }

   let split_level_exp' { le_const = c; le_vars = vs } =
      let vs1, vs2 = split vs in
         { Type1.le_const = c; Type1.le_vars = vs1 },
         { Type2.le_const = c; Type2.le_vars = vs2 }

   let split_param' = function
      (Number _ | String _ | Token _ | Var _ | MNumber _ | MString _ | MToken _ | Quote) as p -> p, p
    | MLevel (l1, l2) -> MLevel l1, MLevel l2
    | ObId pl -> let pl1, pl2 = split pl in ObId pl1, ObId pl2
    | ParamList pl -> let pl1, pl2 = split pl in ParamList pl1, ParamList pl2

   let split_hyp = function
      Hypothesis (v, (t1, t2)) ->
         Hypothesis (v, t1), Hypothesis (v, t2)
    | Context(v, vs, ts) ->
         let ts1, ts2 = split ts in
            Context (v, vs, ts1), Context(v, vs, ts2)

   let split_hyps hs =
      split (List.map split_hyp hs)

   let split_eseq { sequent_args = a1, a2; sequent_hyps = h1, h2; sequent_concl = c1, c2 } =
      { Type1.sequent_args = a1; Type1.sequent_hyps = h1; Type1.sequent_concl = c1 },
      { Type2.sequent_args = a2; Type2.sequent_hyps = h2; Type2.sequent_concl = c2 }

   let split_term_subst sub =
      let vars, terms = split sub in
      let ts1, ts2 = split terms in
         (List.combine vars ts1), (List.combine vars ts2)

   let rec split_meta_term = function
      MetaTheorem (t1, t2) ->
         MetaTheorem t1, MetaTheorem t2
    | MetaImplies (mta, mtb) ->
         let mta1, mta2 = split_meta_term mta in
         let mtb1, mtb2 = split_meta_term mtb in
            MetaImplies (mta1, mtb1), MetaImplies (mta2, mtb2)
    | MetaFunction ((t1, t2), mta, mtb) ->
         let mta1, mta2 = split_meta_term mta in
         let mtb1, mtb2 = split_meta_term mtb in
            MetaFunction (t1, mta1, mtb1), MetaFunction (t2, mta2, mtb2)
    | MetaIff (mta, mtb) ->
         let mta1, mta2 = split_meta_term mta in
         let mtb1, mtb2 = split_meta_term mtb in
            MetaIff (mta1, mtb1), MetaIff (mta2, mtb2)
    | MetaLabeled (s, mt) ->
         let mt1, mt2 = split_meta_term mt in MetaLabeled (s, mt1), MetaLabeled (s, mt2)

   let split_taf f =
      (fun t1 -> f (term_of_term1 t1)), (fun t2 -> f (term_of_term2 t2))

   let split_ttf f =
      (fun t1 -> fst (f (term_of_term1 t1))),
      (fun t2 -> snd (f (term_of_term2 t2)))

   let split_attf f =
      (fun a t1 -> fst (f a (term_of_term1 t1))),
      (fun a t2 -> snd (f a (term_of_term2 t2)))

   let split_atf f =
      (fun a -> fst (f a)), (fun a -> snd (f a))

   let split_ttaf f =
      (fun t1 -> let t, res = f (term_of_term1 t1) in fst t, res),
      (fun t2 -> let t, res = f (term_of_term2 t2) in snd t, res)

   let split_attaf f =
      (fun a t1 -> let t, res = f a (term_of_term1 t1) in fst t, res),
      (fun a t2 -> let t, res = f a (term_of_term2 t2) in snd t, res)

   (*
    * We use a separate error reporting function to have a single breakpoint
    * location that can be used to catch _all_ error in the debugger
    *)
   let report_error x msg =
      raise (Invalid_argument ("Found a mismatch in function " ^ x ^ ": " ^ msg))

   let merge merge_fun x v1 v2 =
      match v1, v2 with
         Val v1, Val v2 -> merge_fun x v1 v2
       | Err (Err1.RefineError (s1, err1)), Err (Err2.RefineError _) -> raise (RefineError (s1, re_of_re1 err1))
       | Err (RefineError _ as exn), Err (RefineError _) -> raise exn
       | Err (Err1.RefineError _), _
       | _, Err (Err2.RefineError _)
       | Err (RefineError _), _
       | _, Err (RefineError _) -> report_error x "One implementation raise RE, another did not"
       | Err exn1, Err exn2 when exn1 = exn2 -> raise exn1
       | Err (Failure s1), Err (Failure s2) -> raise (Failure ("Impl1: " ^ s1 ^ "; Impl2: " ^ s2))
       | Err (Invalid_argument s1), Err (Invalid_argument s2) -> raise (Invalid_argument ("Impl1: " ^ s1 ^ "; Impl2: " ^ s2))
       | Err exn, _
       | _, Err exn -> raise exn

   let merge_triv x v1 v2 =
      v1, v2

   let merge_poly x v1 v2 =
      if v1 <> v2 then
         report_error x "Polymorphic merge";
      v1

   let merge_bool x (b1:bool) b2 =
      if b1 <> b2 then
         report_error x "Booleans mismatch";
      b1

   let merge_int x (i1: int) i2 =
      if i1 <> i2 then
         report_error x "Integers mismatch";
      i1

   let merge_var x (v1:var) v2 =
      if v1 <> v2 then
         report_error x "Variable mismatch";
      v1

   let merge_string x s1 s2 =
      if s1 <> s2 then
         report_error x ("Strings mismatch: \"" ^s1^"\" vs \""^s2^"\"");
      s1

   let merge_num x n1 n2 =
      if not (Lm_num.eq_num n1 n2) then
          report_error x "nums mismatch";
      n1

   let merge_shape_param x (sp1 : shape_param) sp2 =
      if sp1 <> sp2 then
         report_error x "Shape_param mismatch";
      sp1

   let merge_unit x () () = ()

   let merge_list merge name x l1 l2 =
      if not (List.length l1 = List.length l2) then
         report_error x (name ^ " lists length mismatch");
      List.map2 (merge x) l1 l2

   let merge_array merge name x a1 a2 =
      if not (Array.length a1 = Array.length a2) then
         report_error x (name ^ " array length mismatch");
      Array.of_list (List.map2 (merge x) (Array.to_list a1) (Array.to_list a2))

   let merge_opt merge name x o1 o2 =
      match o1, o2 with
         None, None -> None
       | Some v1, Some v2 -> Some (merge x v1 v2)
       | _ -> report_error x (name ^ " option None/Some mismatch")

   let merge_ints = merge_list merge_int "integer"
   let merge_vars = merge_list merge_var "var"
   let merge_int_arr = merge_array merge_int "integer"
   let merge_var_arr = merge_array merge_var "var"
   let merge_strings = merge_list merge_string "string"
   let merge_var_lo = merge_opt merge_vars "var list"

   let merge_ss x (s1 : SymbolSet.t) s2 =
      if not (SymbolSet.equal s1 s2) then
         report_error x "Symbol sets mismatch";
      s1

   let merge_param x p1 p2 =
      (* XXX: TODO: need some consistency checks *)
      p1, p2

   let merge_level_exp_var x v1 v2 =
      (* XXX: TODO: need some consistency checks *)
      v1, v2

   let merge_level_exp x le1 le2 =
      (* XXX: TODO: need some consistency checks *)
      le1, le2

   let merge_address x a1 a2 =
      (* XXX: TODO: need some consistency checks *)
      a1, a2

   let merge_addresss = merge_list merge_address "address"
   let merge_params = merge_list merge_param "param"

   let merge_param' x p1 p2 =
      match p1, p2 with
         (Number _ | String _ | Token _ | Var _ | MNumber _ | MString _ | MToken _ | Quote as p1),
         (Number _ | String _ | Token _ | Var _ | MNumber _ | MString _ | MToken _ | Quote as p2)
         when p1 = p2 ->
            p1
       | MLevel l1, MLevel l2 -> MLevel (l1, l2)
       | ObId pl1, ObId pl2 -> ObId (merge_params x pl1 pl2)
       | ParamList pl1, ParamList pl2 -> ParamList (merge_params x pl1 pl2)
       | _ -> report_error x "incompatible param'"

   let merge_params' = merge_list merge_param' "param'"
   let merge_level_exp_vars = merge_list merge_level_exp_var "level_exp_var"

   let merge_level_exp_var' x { Type1.le_var = v1; Type1.le_offset = i1 } { Type2.le_var = v2; Type2.le_offset = i2 } =
      if not (v1 = v2) then
         report_error x "le_var field mismatch";
      if not (i1 = i2) then
         report_error x "le_offset field mismatch";
      { le_var = v1; le_offset = i1 }

   let merge_level_exp_vars' = merge_list merge_level_exp_var' "level_exp_var'"

   let merge_level_exp' x { Type1.le_const = c1; Type1.le_vars = vs1 } { Type2.le_const = c2; Type2.le_vars = vs2 } =
      if not (c1 = c2) then
         report_error x "le_const field mismatch";
      { le_const = c1; le_vars = merge_level_exp_vars x vs1 vs2 }

   let merge_op' x { Type1.op_name = name1; Type1.op_params = pl1 } { Type2.op_name = name2; Type2.op_params = pl2 } =
      if not (Opname.eq name1 name2) then
         report_error x "operator' opname mismatch";
      { op_name = name1; op_params = merge_params x pl1 pl2 }

   let merge_op x op1 op2 =
      (* XXX: TODO: need some consistency checks *)
      op1, op2

   let merge_opname x op1 op2 =
      if not (Opname.eq op1 op2) then
         report_error x "opnames mismatch";
      op1

   let merge_term x t1 t2 =
      if not (Opname.eq (Term1.opname_of_term t1) (Term2.opname_of_term t2)) then
         report_error x "term opname mismatch"
      else
         (t1, t2)

   let merge_ttf x f1 f2 =
      fun (t1, t2) -> merge_term x (f1 t1) (f2 t2)

   let rec merge_meta_term x mt1 mt2 =
      match mt1, mt2 with
         MetaTheorem t1, MetaTheorem t2 ->
            MetaTheorem (merge_term x t1 t2)
       | MetaImplies (mt1a, mt1b), MetaImplies (mt2a, mt2b) ->
            MetaImplies (merge_meta_term x mt1a mt2a, merge_meta_term x mt1b mt2b)
       | MetaFunction (t1, mt1a, mt1b), MetaFunction (t2, mt2a, mt2b) ->
            MetaFunction (merge_term x t1 t2, merge_meta_term x mt1a mt2a, merge_meta_term x mt1b mt2b)
       | MetaIff (mt1a, mt1b), MetaIff (mt2a, mt2b) ->
            MetaIff (merge_meta_term x mt1a mt2a, merge_meta_term x mt1b mt2b)
       | MetaLabeled (s1, mt1), MetaLabeled (s2, mt2) ->
            MetaLabeled (merge_string x s1 s2, merge_meta_term x mt1 mt2)
       | _ ->
            report_error x "meta term kind mismatch"

   let merge_shape x s1 s2 =
      if not (Opname.eq (TermShape1.opname_of_shape s1) (TermShape2.opname_of_shape s2)) then
         report_error x "term shape opname mismatch"
      else
         (s1, s2)

   let merge_tsub x (v1, t1) (v2, t2) =
      (merge_var x v1 v2), (merge_term x t1 t2)

   let merge_terms = merge_list merge_term "term"
   let merge_term_opt = merge_opt merge_term "term"
   let merge_term_subst = merge_list merge_tsub "term_subst"

   let merge_sltot x (sl1, to1, t1) (sl2, to2, t2) =
      (merge_strings x sl1 sl2), (merge_term_opt x to1 to2), (merge_term x t1 t2)

   let merge_bterm' x { Type1.bvars = bv1; Type1.bterm = t1 } { Type2.bvars = bv2; Type2.bterm = t2 } =
      if not (List.length bv1 = List.length bv2) then
         report_error x "bvar length mismatch";
      { bvars = bv1; bterm = merge_term x t1 (TermSubst2.subst t2 (List.rev bv2) (List.rev_map Term2.mk_var_term bv1)) }

   let merge_bterm x bt1 bt2 =
      (* XXX: TODO: need some consistency checks *)
      bt1, bt2

   let merge_bterms' = merge_list merge_bterm' "bound_term'"
   let merge_bterms = merge_list merge_bterm "bterm"

   let merge_term' x { Type1.term_op = op1; Type1.term_terms = btl1 } { Type2.term_op = op2; Type2.term_terms = btl2 } =
      { term_op = merge_op x op1 op2; term_terms = merge_bterms x btl1 btl2 }

   let merge_hyp x h1 h2 =
      match h1, h2 with
         Hypothesis (v1, t1), Hypothesis (v2, t2) ->
            if not (v1 = v2) then
               report_error x "Hyp variable mismatch";
            Hypothesis (v1, merge_term x t1 t2)
       | Context (v1, vs1, ts1), Context (v2, vs2, ts2) ->
            if not (v1 = v2) then
               report_error x "Context variable mismatch";
            if not (vs1 = vs2) then
               report_error x "Contexts of a context mismatch";
            Context (v1, vs1, merge_terms x ts1 ts2)
       | _ ->
            report_error x "hypothesis kind mismatch"

   let merge_hyps = merge_list merge_hyp "hyp"

   let merge_SeqHyp x hyps1 hyps2 =
      if not (SeqHyp1.length hyps1 = SeqHyp2.length hyps2) then
         report_error x "SeqHyp.length mismatch on merge";
      hyps1, hyps2

   let merge_esequent x { Type1.sequent_args = a1; Type1.sequent_hyps = h1; Type1.sequent_concl = c1 } { Type2.sequent_args = a2; Type2.sequent_hyps = h2; Type2.sequent_concl = c2 } =
      { sequent_args = merge_term x a1 a2; sequent_hyps = merge_SeqHyp x h1 h2; sequent_concl = merge_term x c1 c2 }

   let merge_match_param x p1 p2 =
      match p1, p2 with
         Type1.MatchNumber (n1, None), Type2.MatchNumber (n2, None) -> MatchNumber (merge_num x n1 n2, None)
       | Type1.MatchNumber (n1, Some i1), Type2.MatchNumber (n2, Some i2) -> MatchNumber (merge_num x n1 n2, Some (merge_int x i1 i2))
       | Type1.MatchString s1, Type2.MatchString s2 -> MatchString (merge_string x s1 s2)
       | Type1.MatchToken s1, Type2.MatchToken s2 -> MatchToken (merge_string x s1 s2)
       | Type1.MatchVar v1, Type2.MatchVar v2 -> MatchVar (merge_var x v1 v2)
       | Type1.MatchLevel l1, Type2.MatchLevel l2 -> MatchLevel (merge_level_exp x l1 l2)
       | Type1.MatchUnsupported, Type2.MatchUnsupported -> MatchUnsupported
       | _ -> report_error x "match_param kind mismatch"

   let merge_match_params = merge_list merge_match_param "match param"

   let rec merge_match_term x mt1 mt2 =
      match mt1, mt2 with
         Type1.MatchTerm (sl1, pl1, bl1), Type2.MatchTerm (sl2, pl2, bl2) ->
            MatchTerm (merge_strings x sl1 sl2, merge_match_params x pl1 pl2, merge_bterms' x bl1 bl2)
       | Type1.MatchSequent (sl1, mtl1, hl1, t1), Type2.MatchSequent (sl2, mtl2, hl2, t2) ->
            MatchSequent (merge_strings x sl1 sl2, merge_match_terms x mtl1 mtl2, merge_hyps x hl1 hl2, merge_term x t1 t2)
       | _ -> report_error x "match_term kind mismatch"

   and merge_match_terms x mtl1 mtl2 = merge_list merge_match_term "match term" x mtl1 mtl2

   let merge_rwspecs x (sp1: rewrite_args_spec) sp2 =
      merge_var_arr x sp1 sp2

   let merge_rwargs x (ia1, ss1) (ia2, ss2) =
      (merge_int_arr x ia1 ia2), (merge_ss x ss1 ss2)

   let merge_rwtyp x (rwt1: rewrite_type) rwt2 =
      if rwt1 <> rwt2 then
         report_error x "rewrite_type mismatch";
      rwt1

   let merge_rwtv x (rt1, v1) (rt2, v2) =
      (merge_rwtyp x rt1 rt2), (merge_var x v1 v2)

   let merge_rwtvl = merge_list merge_rwtv "rewrite_type * var"

   let merge_rwp merge x p1 p2 =
      match p1, p2 with
         RewriteParam p1, RewriteParam p2 -> RewriteParam (merge x p1 p2)
       | RewriteMetaParam v1, RewriteMetaParam v2 -> RewriteMetaParam (merge_var x v1 v2)
       | _ -> report_error x "rewrite_param kind mismatch"

   let merge_rewrite_item x i1 i2 =
      match i1, i2 with
         Rewrite1.RewriteTerm t1, Rewrite2.RewriteTerm t2 ->
             RewriteTerm (merge_term x t1 t2)
       | Rewrite1.RewriteFun f1, Rewrite2.RewriteFun f2 ->
            RewriteFun (fun tl -> let tl1, tl2 = split tl in merge merge_term x (wrap1 f1 tl1) (wrap1 f2 tl2))
       | Rewrite1.RewriteContext f1, Rewrite2.RewriteContext f2 ->
            RewriteContext (fun (t1, t2) tl -> let tl1, tl2 = split tl in merge merge_term x (wrap2 f1 t1 tl1) (wrap2 f2 t2 tl2))
       | Rewrite1.RewriteString s1, Rewrite2.RewriteString s2 ->
            RewriteString (merge_rwp merge_string x s1 s2)
       | Rewrite1.RewriteNum n1, Rewrite2.RewriteNum n2 ->
            RewriteNum (merge_rwp merge_num x n1 n2)
       | Rewrite1.RewriteLevel le1, Rewrite2.RewriteLevel le2 ->
            RewriteLevel (merge_level_exp x le1 le2)
       | _ ->
            report_error x "rewrite_item kind mismatch"

   let merge_ib x (i1, b1) (i2, b2) =
      (merge_int x i1 i2), (merge_bool x b1 b2)

   let merge_rewrite_items = merge_list merge_rewrite_item "rewrite_item"
   let merge_ibl = merge_list merge_ib "int * bool"

   module SeqHyp = struct
      type elt = hypothesis
      type t = seq_hyps
      type index = int

      let empty =
         merge_SeqHyp "SeqHyp.empty" SeqHyp1.empty SeqHyp2.empty

      let singleton h =
         let h1, h2 = split_hyp h in
            merge_SeqHyp "SeqHyp.singleton" (SeqHyp1.singleton h1) (SeqHyp2.singleton h2)

      let length (t1, t2) =
         merge_int "SeqHyp.length" (SeqHyp1.length t1) (SeqHyp2.length t2)

      let make i h =
         let h1, h2 = split_hyp h in
            merge_SeqHyp "SeqHyp.make" (SeqHyp1.make i h1) (SeqHyp2.make i h2)

      let create = make

      let get (t1, t2) i =
         merge_hyp "SeqHyp.get" (SeqHyp1.get t1 i) (SeqHyp2.get t2 i)

      let to_list (t1, t2) =
         merge_hyps "SeqHyp.to_list" (SeqHyp1.to_list t1) (SeqHyp2.to_list t2)

      let of_list hl =
         let hl1, hl2 = split_hyps hl in
            merge_SeqHyp "SeqHyp.of_list" (SeqHyp1.of_list hl1) (SeqHyp2.of_list hl2)

      let append (t1, t2) h (tt1, tt2) =
         let h1, h2 = split_hyp h in
            merge_SeqHyp "SeqHyp.append" (SeqHyp1.append t1 h1 tt1) (SeqHyp2.append t2 h2 tt2)

      let append_list (t1, t2) (hs : elt list) (tt1, tt2) =
         let hs1, hs2 = split_hyps hs in
            merge_SeqHyp "SeqHyp.append_list" (SeqHyp1.append_list t1 hs1 tt1) (SeqHyp2.append_list t2 hs2 tt2)

      let split (t1, t2) i =
         let l1, h1, r1 = SeqHyp1.split t1 i in
         let l2, h2, r2 = SeqHyp2.split t2 i in
            (merge_SeqHyp "SeqHyp.split - 1" l1 l2),
            (merge_hyp "SeqHyp.split - 2" h1 h2),
            (merge_SeqHyp "SeqHyp.split - 3" r1 r2)

      let init i f =
         merge_SeqHyp "SeqHyp.init" (SeqHyp1.init i (fun i -> fst (split_hyp (f i)))) (SeqHyp2.init i (fun i -> snd (split_hyp (f i))))

      (* XXX: TODO: we do not use the underlying implementation here, so it is not fully tested *)
      let iter f t = List.iter f (to_list t)
      let map f t = of_list (List.map f (to_list t))
      let lazy_apply = map
      let mapi f t = init (length t) (fun i -> f i (get t i))
      let lazy_sub_map f t i len = of_list (Array.to_list (Lm_array_util.sub_map f (Array.of_list (to_list t)) i len))
      let map_part = function
         ArrayElement a -> ArrayElement a
       | ArrayArray (t, i, j) -> ArrayArray (Array.of_list (to_list t), i, j)
      let collect ps = of_list (Array.to_list (Lm_array_util.collect (List.map map_part ps)))
   end

   module Term = struct
      module TermTypes = TermType
      module SeqHyp = SeqHyp

      let debug_print = print_term
      let print_term = print_term
      let print_term_list = print_term_list

      let install_debug_printer f =
         let print_term1 out t = f out (term_of_term1 t) in
         let print_term2 out t = f out (term_of_term2 t) in
         let print_both_terms out (t1, t2) =
            fprintf out "Implementation 1: %a\nImplementation 2: %a%t" print_term1 t1 print_term2 t2 eflush
         in
            Term1.install_debug_printer print_term1;
            Term2.install_debug_printer print_term2;
            print_term_ref := print_both_terms

      (* The rest of this module is auto-generated by the util/gen_refiner_debug.pl script *)

      let mk_term (p0 : operator) (p1 : bound_term list) =
         let p0_1, p0_2 = p0 in
         let p1_1, p1_2 = split p1 in
         merge merge_term "Term.mk_term" (wrap2 Term1.mk_term p0_1 p1_1) (wrap2 Term2.mk_term p0_2 p1_2)

      let make_term (p0 : term') =
         let p0_1, p0_2 = split_term' p0 in
         merge merge_term "Term.make_term" (wrap1 Term1.make_term p0_1) (wrap1 Term2.make_term p0_2)

      let dest_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_term' "Term.dest_term" (wrap1 Term1.dest_term p0_1) (wrap1 Term2.dest_term p0_2)

      let mk_op (p0 : opname) (p1 : param list) =
         let p1_1, p1_2 = split p1 in
         merge merge_op "Term.mk_op" (wrap2 Term1.mk_op p0 p1_1) (wrap2 Term2.mk_op p0 p1_2)

      let make_op (p0 : operator') =
         let p0_1, p0_2 = split_op' p0 in
         merge merge_op "Term.make_op" (wrap1 Term1.make_op p0_1) (wrap1 Term2.make_op p0_2)

      let dest_op (p0 : operator) =
         let p0_1, p0_2 = p0 in
         merge merge_op' "Term.dest_op" (wrap1 Term1.dest_op p0_1) (wrap1 Term2.dest_op p0_2)

      let ops_eq (p0 : operator) (p1 : operator) =
         let p0_1, p0_2 = p0 in
         let p1_1, p1_2 = p1 in
         merge merge_bool "Term.ops_eq" (wrap2 Term1.ops_eq p0_1 p1_1) (wrap2 Term2.ops_eq p0_2 p1_2)

      let mk_bterm (p0 : var list) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bterm "Term.mk_bterm" (wrap2 Term1.mk_bterm p0 p1_1) (wrap2 Term2.mk_bterm p0 p1_2)

      let make_bterm (p0 : bound_term') =
         let p0_1, p0_2 = split_bterm' p0 in
         merge merge_bterm "Term.make_bterm" (wrap1 Term1.make_bterm p0_1) (wrap1 Term2.make_bterm p0_2)

      let dest_bterm (p0 : bound_term) =
         let p0_1, p0_2 = p0 in
         merge merge_bterm' "Term.dest_bterm" (wrap1 Term1.dest_bterm p0_1) (wrap1 Term2.dest_bterm p0_2)

      let make_param (p0 : param') =
         let p0_1, p0_2 = split_param' p0 in
         merge merge_param "Term.make_param" (wrap1 Term1.make_param p0_1) (wrap1 Term2.make_param p0_2)

      let dest_param (p0 : param) =
         let p0_1, p0_2 = p0 in
         merge merge_param' "Term.dest_param" (wrap1 Term1.dest_param p0_1) (wrap1 Term2.dest_param p0_2)

      let dest_params (p0 : param list) =
         let p0_1, p0_2 = split p0 in
         merge merge_params' "Term.dest_params" (wrap1 Term1.dest_params p0_1) (wrap1 Term2.dest_params p0_2)

      let mk_level (p0 : int) (p1 : level_exp_var list) =
         let p1_1, p1_2 = split p1 in
         merge merge_level_exp "Term.mk_level" (wrap2 Term1.mk_level p0 p1_1) (wrap2 Term2.mk_level p0 p1_2)

      let make_level (p0 : level_exp') =
         let p0_1, p0_2 = split_level_exp' p0 in
         merge merge_level_exp "Term.make_level" (wrap1 Term1.make_level p0_1) (wrap1 Term2.make_level p0_2)

      let dest_level (p0 : level_exp) =
         let p0_1, p0_2 = p0 in
         merge merge_level_exp' "Term.dest_level" (wrap1 Term1.dest_level p0_1) (wrap1 Term2.dest_level p0_2)

      let mk_level_var (p0 : var) (p1 : int) =
         merge merge_level_exp_var "Term.mk_level_var" (wrap2 Term1.mk_level_var p0 p1) (wrap2 Term2.mk_level_var p0 p1)

      let make_level_var (p0 : level_exp_var') =
         let p0_1, p0_2 = split_level_exp_var' p0 in
         merge merge_level_exp_var "Term.make_level_var" (wrap1 Term1.make_level_var p0_1) (wrap1 Term2.make_level_var p0_2)

      let dest_level_var (p0 : level_exp_var) =
         let p0_1, p0_2 = p0 in
         merge merge_level_exp_var' "Term.dest_level_var" (wrap1 Term1.dest_level_var p0_1) (wrap1 Term2.dest_level_var p0_2)

      let make_object_id (p0 : param list) =
         let p0_1, p0_2 = split p0 in
         merge merge_params "Term.make_object_id" (wrap1 Term1.make_object_id p0_1) (wrap1 Term2.make_object_id p0_2)

      let dest_object_id (p0 : object_id) =
         let p0_1, p0_2 = split p0 in
         merge merge_params "Term.dest_object_id" (wrap1 Term1.dest_object_id p0_1) (wrap1 Term2.dest_object_id p0_2)

      let opname_of_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_opname "Term.opname_of_term" (wrap1 Term1.opname_of_term p0_1) (wrap1 Term2.opname_of_term p0_2)

      let subterms_of_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_terms "Term.subterms_of_term" (wrap1 Term1.subterms_of_term p0_1) (wrap1 Term2.subterms_of_term p0_2)

      let subterm_arities (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_ints "Term.subterm_arities" (wrap1 Term1.subterm_arities p0_1) (wrap1 Term2.subterm_arities p0_2)

      let is_var_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_bool "Term.is_var_term" (wrap1 Term1.is_var_term p0_1) (wrap1 Term2.is_var_term p0_2)

      let dest_var (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_var "Term.dest_var" (wrap1 Term1.dest_var p0_1) (wrap1 Term2.dest_var p0_2)

      let mk_var_term (p0 : var) =
         merge merge_term "Term.mk_var_term" (wrap1 Term1.mk_var_term p0) (wrap1 Term2.mk_var_term p0)

      let mk_any_term (p0 : operator) (p1 : term list) =
         let p0_1, p0_2 = p0 in
         let p1_1, p1_2 = split p1 in
         merge merge_term "Term.mk_any_term" (wrap2 Term1.mk_any_term p0_1 p1_1) (wrap2 Term2.mk_any_term p0_2 p1_2)

      let mk_simple_term (p0 : opname) (p1 : term list) =
         let p1_1, p1_2 = split p1 in
         merge merge_term "Term.mk_simple_term" (wrap2 Term1.mk_simple_term p0 p1_1) (wrap2 Term2.mk_simple_term p0 p1_2)

      let dest_simple_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         let res1 = wrap1 Term1.dest_simple_term p0_1 in
         let res2 = wrap1 Term2.dest_simple_term p0_2 in
         let (res0_1, res1_1), (res0_2, res1_2) = merge merge_triv "Term.dest_simple_term" res1 res2 in
         (merge_opname "Term.dest_simple_term - 0" res0_1 res0_2),
         (merge_terms "Term.dest_simple_term - 1" res1_1 res1_2)

      let is_simple_term_opname (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "Term.is_simple_term_opname" (wrap2 Term1.is_simple_term_opname p0 p1_1) (wrap2 Term2.is_simple_term_opname p0 p1_2)

      let dest_simple_term_opname (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_terms "Term.dest_simple_term_opname" (wrap2 Term1.dest_simple_term_opname p0 p1_1) (wrap2 Term2.dest_simple_term_opname p0 p1_2)

      let is_simple_bterm (p0 : bound_term) =
         let p0_1, p0_2 = p0 in
         merge merge_bool "Term.is_simple_bterm" (wrap1 Term1.is_simple_bterm p0_1) (wrap1 Term2.is_simple_bterm p0_2)

      let mk_simple_bterm (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_bterm "Term.mk_simple_bterm" (wrap1 Term1.mk_simple_bterm p0_1) (wrap1 Term2.mk_simple_bterm p0_2)

      let dest_simple_bterm (p0 : bound_term) =
         let p0_1, p0_2 = p0 in
         merge merge_term "Term.dest_simple_bterm" (wrap1 Term1.dest_simple_bterm p0_1) (wrap1 Term2.dest_simple_bterm p0_2)

   end

   module TermOp = struct
      module OpTypes = TermType

      (* The rest of this module is auto-generated by the util/gen_refiner_debug.pl script *)

      let map_down (p0 : (term -> term)) (p1 : term) =
         let p0_1, p0_2 = split_ttf p0 in
         let p1_1, p1_2 = p1 in
         merge merge_term "TermOp.map_down" (wrap2 TermOp1.map_down p0_1 p1_1) (wrap2 TermOp2.map_down p0_2 p1_2)

      let map_up (p0 : (term -> term)) (p1 : term) =
         let p0_1, p0_2 = split_ttf p0 in
         let p1_1, p1_2 = p1 in
         merge merge_term "TermOp.map_up" (wrap2 TermOp1.map_up p0_1 p1_1) (wrap2 TermOp2.map_up p0_2 p1_2)

      let is_quoted_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_bool "TermOp.is_quoted_term" (wrap1 TermOp1.is_quoted_term p0_1) (wrap1 TermOp2.is_quoted_term p0_2)

      let quote_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_term "TermOp.quote_term" (wrap1 TermOp1.quote_term p0_1) (wrap1 TermOp2.quote_term p0_2)

      let unquote_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_term "TermOp.unquote_term" (wrap1 TermOp1.unquote_term p0_1) (wrap1 TermOp2.unquote_term p0_2)

      let is_no_subterms_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_no_subterms_term" (wrap2 TermOp1.is_no_subterms_term p0 p1_1) (wrap2 TermOp2.is_no_subterms_term p0 p1_2)

      let is_dep0_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_dep0_term" (wrap2 TermOp1.is_dep0_term p0 p1_1) (wrap2 TermOp2.is_dep0_term p0 p1_2)

      let mk_dep0_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_term "TermOp.mk_dep0_term" (wrap2 TermOp1.mk_dep0_term p0 p1_1) (wrap2 TermOp2.mk_dep0_term p0 p1_2)

      let dest_dep0_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_term "TermOp.dest_dep0_term" (wrap2 TermOp1.dest_dep0_term p0 p1_1) (wrap2 TermOp2.dest_dep0_term p0 p1_2)

      let one_subterm (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_term "TermOp.one_subterm" (wrap1 TermOp1.one_subterm p0_1) (wrap1 TermOp2.one_subterm p0_2)

      let one_subterm_opname (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_term "TermOp.one_subterm_opname" (wrap2 TermOp1.one_subterm_opname p0 p1_1) (wrap2 TermOp2.one_subterm_opname p0 p1_2)

      let is_dep0_dep0_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_dep0_dep0_term" (wrap2 TermOp1.is_dep0_dep0_term p0 p1_1) (wrap2 TermOp2.is_dep0_dep0_term p0 p1_2)

      let mk_dep0_dep0_term (p0 : opname) (p1 : term) (p2 : term) =
         let p1_1, p1_2 = p1 in
         let p2_1, p2_2 = p2 in
         merge merge_term "TermOp.mk_dep0_dep0_term" (wrap3 TermOp1.mk_dep0_dep0_term p0 p1_1 p2_1) (wrap3 TermOp2.mk_dep0_dep0_term p0 p1_2 p2_2)

      let dest_dep0_dep0_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         let res1 = wrap2 TermOp1.dest_dep0_dep0_term p0 p1_1 in
         let res2 = wrap2 TermOp2.dest_dep0_dep0_term p0 p1_2 in
         let (res0_1, res1_1), (res0_2, res1_2) = merge merge_triv "TermOp.dest_dep0_dep0_term" res1 res2 in
         (merge_term "TermOp.dest_dep0_dep0_term - 0" res0_1 res0_2),
         (merge_term "TermOp.dest_dep0_dep0_term - 1" res1_1 res1_2)

      let two_subterms (p0 : term) =
         let p0_1, p0_2 = p0 in
         let res1 = wrap1 TermOp1.two_subterms p0_1 in
         let res2 = wrap1 TermOp2.two_subterms p0_2 in
         let (res0_1, res1_1), (res0_2, res1_2) = merge merge_triv "TermOp.two_subterms" res1 res2 in
         (merge_term "TermOp.two_subterms - 0" res0_1 res0_2),
         (merge_term "TermOp.two_subterms - 1" res1_1 res1_2)

      let two_subterms_opname (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         let res1 = wrap2 TermOp1.two_subterms_opname p0 p1_1 in
         let res2 = wrap2 TermOp2.two_subterms_opname p0 p1_2 in
         let (res0_1, res1_1), (res0_2, res1_2) = merge merge_triv "TermOp.two_subterms_opname" res1 res2 in
         (merge_term "TermOp.two_subterms_opname - 0" res0_1 res0_2),
         (merge_term "TermOp.two_subterms_opname - 1" res1_1 res1_2)

      let is_dep0_dep0_dep0_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_dep0_dep0_dep0_term" (wrap2 TermOp1.is_dep0_dep0_dep0_term p0 p1_1) (wrap2 TermOp2.is_dep0_dep0_dep0_term p0 p1_2)

      let mk_dep0_dep0_dep0_term (p0 : opname) (p1 : term) (p2 : term) (p3 : term) =
         let p1_1, p1_2 = p1 in
         let p2_1, p2_2 = p2 in
         let p3_1, p3_2 = p3 in
         merge merge_term "TermOp.mk_dep0_dep0_dep0_term" (wrap4 TermOp1.mk_dep0_dep0_dep0_term p0 p1_1 p2_1 p3_1) (wrap4 TermOp2.mk_dep0_dep0_dep0_term p0 p1_2 p2_2 p3_2)

      let dest_dep0_dep0_dep0_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         let res1 = wrap2 TermOp1.dest_dep0_dep0_dep0_term p0 p1_1 in
         let res2 = wrap2 TermOp2.dest_dep0_dep0_dep0_term p0 p1_2 in
         let (res0_1, res1_1, res2_1), (res0_2, res1_2, res2_2) = merge merge_triv "TermOp.dest_dep0_dep0_dep0_term" res1 res2 in
         (merge_term "TermOp.dest_dep0_dep0_dep0_term - 0" res0_1 res0_2),
         (merge_term "TermOp.dest_dep0_dep0_dep0_term - 1" res1_1 res1_2),
         (merge_term "TermOp.dest_dep0_dep0_dep0_term - 2" res2_1 res2_2)

      let is_dep0_dep0_dep0_dep0_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_dep0_dep0_dep0_dep0_term" (wrap2 TermOp1.is_dep0_dep0_dep0_dep0_term p0 p1_1) (wrap2 TermOp2.is_dep0_dep0_dep0_dep0_term p0 p1_2)

      let mk_dep0_dep0_dep0_dep0_term (p0 : opname) (p1 : term) (p2 : term) (p3 : term) (p4 : term) =
         let p1_1, p1_2 = p1 in
         let p2_1, p2_2 = p2 in
         let p3_1, p3_2 = p3 in
         let p4_1, p4_2 = p4 in
         merge merge_term "TermOp.mk_dep0_dep0_dep0_dep0_term" (wrap5 TermOp1.mk_dep0_dep0_dep0_dep0_term p0 p1_1 p2_1 p3_1 p4_1) (wrap5 TermOp2.mk_dep0_dep0_dep0_dep0_term p0 p1_2 p2_2 p3_2 p4_2)

      let dest_dep0_dep0_dep0_dep0_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         let res1 = wrap2 TermOp1.dest_dep0_dep0_dep0_dep0_term p0 p1_1 in
         let res2 = wrap2 TermOp2.dest_dep0_dep0_dep0_dep0_term p0 p1_2 in
         let (res0_1, res1_1, res2_1, res3_1), (res0_2, res1_2, res2_2, res3_2) = merge merge_triv "TermOp.dest_dep0_dep0_dep0_dep0_term" res1 res2 in
         (merge_term "TermOp.dest_dep0_dep0_dep0_dep0_term - 0" res0_1 res0_2),
         (merge_term "TermOp.dest_dep0_dep0_dep0_dep0_term - 1" res1_1 res1_2),
         (merge_term "TermOp.dest_dep0_dep0_dep0_dep0_term - 2" res2_1 res2_2),
         (merge_term "TermOp.dest_dep0_dep0_dep0_dep0_term - 3" res3_1 res3_2)

      let is_two_subterm (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_two_subterm" (wrap2 TermOp1.is_two_subterm p0 p1_1) (wrap2 TermOp2.is_two_subterm p0 p1_2)

      let is_three_subterm (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_three_subterm" (wrap2 TermOp1.is_three_subterm p0 p1_1) (wrap2 TermOp2.is_three_subterm p0 p1_2)

      let is_five_subterm (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_five_subterm" (wrap2 TermOp1.is_five_subterm p0 p1_1) (wrap2 TermOp2.is_five_subterm p0 p1_2)

      let three_subterms (p0 : term) =
         let p0_1, p0_2 = p0 in
         let res1 = wrap1 TermOp1.three_subterms p0_1 in
         let res2 = wrap1 TermOp2.three_subterms p0_2 in
         let (res0_1, res1_1, res2_1), (res0_2, res1_2, res2_2) = merge merge_triv "TermOp.three_subterms" res1 res2 in
         (merge_term "TermOp.three_subterms - 0" res0_1 res0_2),
         (merge_term "TermOp.three_subterms - 1" res1_1 res1_2),
         (merge_term "TermOp.three_subterms - 2" res2_1 res2_2)

      let four_subterms (p0 : term) =
         let p0_1, p0_2 = p0 in
         let res1 = wrap1 TermOp1.four_subterms p0_1 in
         let res2 = wrap1 TermOp2.four_subterms p0_2 in
         let (res0_1, res1_1, res2_1, res3_1), (res0_2, res1_2, res2_2, res3_2) = merge merge_triv "TermOp.four_subterms" res1 res2 in
         (merge_term "TermOp.four_subterms - 0" res0_1 res0_2),
         (merge_term "TermOp.four_subterms - 1" res1_1 res1_2),
         (merge_term "TermOp.four_subterms - 2" res2_1 res2_2),
         (merge_term "TermOp.four_subterms - 3" res3_1 res3_2)

      let five_subterms (p0 : term) =
         let p0_1, p0_2 = p0 in
         let res1 = wrap1 TermOp1.five_subterms p0_1 in
         let res2 = wrap1 TermOp2.five_subterms p0_2 in
         let (res0_1, res1_1, res2_1, res3_1, res4_1), (res0_2, res1_2, res2_2, res3_2, res4_2) = merge merge_triv "TermOp.five_subterms" res1 res2 in
         (merge_term "TermOp.five_subterms - 0" res0_1 res0_2),
         (merge_term "TermOp.five_subterms - 1" res1_1 res1_2),
         (merge_term "TermOp.five_subterms - 2" res2_1 res2_2),
         (merge_term "TermOp.five_subterms - 3" res3_1 res3_2),
         (merge_term "TermOp.five_subterms - 4" res4_1 res4_2)

      let six_subterms (p0 : term) =
         let p0_1, p0_2 = p0 in
         let res1 = wrap1 TermOp1.six_subterms p0_1 in
         let res2 = wrap1 TermOp2.six_subterms p0_2 in
         let (res0_1, res1_1, res2_1, res3_1, res4_1, res5_1), (res0_2, res1_2, res2_2, res3_2, res4_2, res5_2) = merge merge_triv "TermOp.six_subterms" res1 res2 in
         (merge_term "TermOp.six_subterms - 0" res0_1 res0_2),
         (merge_term "TermOp.six_subterms - 1" res1_1 res1_2),
         (merge_term "TermOp.six_subterms - 2" res2_1 res2_2),
         (merge_term "TermOp.six_subterms - 3" res3_1 res3_2),
         (merge_term "TermOp.six_subterms - 4" res4_1 res4_2),
         (merge_term "TermOp.six_subterms - 5" res5_1 res5_2)

      let is_dep1_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_dep1_term" (wrap2 TermOp1.is_dep1_term p0 p1_1) (wrap2 TermOp2.is_dep1_term p0 p1_2)

      let mk_dep1_term (p0 : opname) (p1 : var) (p2 : term) =
         let p2_1, p2_2 = p2 in
         merge merge_term "TermOp.mk_dep1_term" (wrap3 TermOp1.mk_dep1_term p0 p1 p2_1) (wrap3 TermOp2.mk_dep1_term p0 p1 p2_2)

      let dest_dep1_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         let res1 = wrap2 TermOp1.dest_dep1_term p0 p1_1 in
         let res2 = wrap2 TermOp2.dest_dep1_term p0 p1_2 in
         let (res0_1, res1_1), (res0_2, res1_2) = merge merge_triv "TermOp.dest_dep1_term" res1 res2 in
         (merge_var "TermOp.dest_dep1_term - 0" res0_1 res0_2),
         (merge_term "TermOp.dest_dep1_term - 1" res1_1 res1_2)

      let is_dep2_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_dep2_term" (wrap2 TermOp1.is_dep2_term p0 p1_1) (wrap2 TermOp2.is_dep2_term p0 p1_2)

      let mk_dep2_term (p0 : opname) (p1 : var) (p2 : var) (p3 : term) =
         let p3_1, p3_2 = p3 in
         merge merge_term "TermOp.mk_dep2_term" (wrap4 TermOp1.mk_dep2_term p0 p1 p2 p3_1) (wrap4 TermOp2.mk_dep2_term p0 p1 p2 p3_2)

      let dest_dep2_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         let res1 = wrap2 TermOp1.dest_dep2_term p0 p1_1 in
         let res2 = wrap2 TermOp2.dest_dep2_term p0 p1_2 in
         let (res0_1, res1_1, res2_1), (res0_2, res1_2, res2_2) = merge merge_triv "TermOp.dest_dep2_term" res1 res2 in
         (merge_var "TermOp.dest_dep2_term - 0" res0_1 res0_2),
         (merge_var "TermOp.dest_dep2_term - 1" res1_1 res1_2),
         (merge_term "TermOp.dest_dep2_term - 2" res2_1 res2_2)

      let is_dep1_dep1_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_dep1_dep1_term" (wrap2 TermOp1.is_dep1_dep1_term p0 p1_1) (wrap2 TermOp2.is_dep1_dep1_term p0 p1_2)

      let mk_dep1_dep1_term (p0 : opname) (p1 : var) (p2 : term) (p3 : var) (p4 : term) =
         let p2_1, p2_2 = p2 in
         let p4_1, p4_2 = p4 in
         merge merge_term "TermOp.mk_dep1_dep1_term" (wrap5 TermOp1.mk_dep1_dep1_term p0 p1 p2_1 p3 p4_1) (wrap5 TermOp2.mk_dep1_dep1_term p0 p1 p2_2 p3 p4_2)

      let dest_dep1_dep1_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         let res1 = wrap2 TermOp1.dest_dep1_dep1_term p0 p1_1 in
         let res2 = wrap2 TermOp2.dest_dep1_dep1_term p0 p1_2 in
         let (res0_1, res1_1, res2_1, res3_1), (res0_2, res1_2, res2_2, res3_2) = merge merge_triv "TermOp.dest_dep1_dep1_term" res1 res2 in
         (merge_var "TermOp.dest_dep1_dep1_term - 0" res0_1 res0_2),
         (merge_term "TermOp.dest_dep1_dep1_term - 1" res1_1 res1_2),
         (merge_var "TermOp.dest_dep1_dep1_term - 2" res2_1 res2_2),
         (merge_term "TermOp.dest_dep1_dep1_term - 3" res3_1 res3_2)

      let is_dep0_dep1_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_dep0_dep1_term" (wrap2 TermOp1.is_dep0_dep1_term p0 p1_1) (wrap2 TermOp2.is_dep0_dep1_term p0 p1_2)

      let is_dep0_dep1_any_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_bool "TermOp.is_dep0_dep1_any_term" (wrap1 TermOp1.is_dep0_dep1_any_term p0_1) (wrap1 TermOp2.is_dep0_dep1_any_term p0_2)

      let mk_dep0_dep1_term (p0 : opname) (p1 : var) (p2 : term) (p3 : term) =
         let p2_1, p2_2 = p2 in
         let p3_1, p3_2 = p3 in
         merge merge_term "TermOp.mk_dep0_dep1_term" (wrap4 TermOp1.mk_dep0_dep1_term p0 p1 p2_1 p3_1) (wrap4 TermOp2.mk_dep0_dep1_term p0 p1 p2_2 p3_2)

      let mk_dep0_dep1_any_term (p0 : operator) (p1 : var) (p2 : term) (p3 : term) =
         let p0_1, p0_2 = p0 in
         let p2_1, p2_2 = p2 in
         let p3_1, p3_2 = p3 in
         merge merge_term "TermOp.mk_dep0_dep1_any_term" (wrap4 TermOp1.mk_dep0_dep1_any_term p0_1 p1 p2_1 p3_1) (wrap4 TermOp2.mk_dep0_dep1_any_term p0_2 p1 p2_2 p3_2)

      let dest_dep0_dep1_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         let res1 = wrap2 TermOp1.dest_dep0_dep1_term p0 p1_1 in
         let res2 = wrap2 TermOp2.dest_dep0_dep1_term p0 p1_2 in
         let (res0_1, res1_1, res2_1), (res0_2, res1_2, res2_2) = merge merge_triv "TermOp.dest_dep0_dep1_term" res1 res2 in
         (merge_var "TermOp.dest_dep0_dep1_term - 0" res0_1 res0_2),
         (merge_term "TermOp.dest_dep0_dep1_term - 1" res1_1 res1_2),
         (merge_term "TermOp.dest_dep0_dep1_term - 2" res2_1 res2_2)

      let dest_dep0_dep1_any_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         let res1 = wrap1 TermOp1.dest_dep0_dep1_any_term p0_1 in
         let res2 = wrap1 TermOp2.dest_dep0_dep1_any_term p0_2 in
         let (res0_1, res1_1, res2_1), (res0_2, res1_2, res2_2) = merge merge_triv "TermOp.dest_dep0_dep1_any_term" res1 res2 in
         (merge_var "TermOp.dest_dep0_dep1_any_term - 0" res0_1 res0_2),
         (merge_term "TermOp.dest_dep0_dep1_any_term - 1" res1_1 res1_2),
         (merge_term "TermOp.dest_dep0_dep1_any_term - 2" res2_1 res2_2)

      let is_dep1_dep0_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_dep1_dep0_term" (wrap2 TermOp1.is_dep1_dep0_term p0 p1_1) (wrap2 TermOp2.is_dep1_dep0_term p0 p1_2)

      let mk_dep1_dep0_term (p0 : opname) (p1 : var) (p2 : term) (p3 : term) =
         let p2_1, p2_2 = p2 in
         let p3_1, p3_2 = p3 in
         merge merge_term "TermOp.mk_dep1_dep0_term" (wrap4 TermOp1.mk_dep1_dep0_term p0 p1 p2_1 p3_1) (wrap4 TermOp2.mk_dep1_dep0_term p0 p1 p2_2 p3_2)

      let dest_dep1_dep0_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         let res1 = wrap2 TermOp1.dest_dep1_dep0_term p0 p1_1 in
         let res2 = wrap2 TermOp2.dest_dep1_dep0_term p0 p1_2 in
         let (res0_1, res1_1, res2_1), (res0_2, res1_2, res2_2) = merge merge_triv "TermOp.dest_dep1_dep0_term" res1 res2 in
         (merge_var "TermOp.dest_dep1_dep0_term - 0" res0_1 res0_2),
         (merge_term "TermOp.dest_dep1_dep0_term - 1" res1_1 res1_2),
         (merge_term "TermOp.dest_dep1_dep0_term - 2" res2_1 res2_2)

      let is_dep0_dep2_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_dep0_dep2_term" (wrap2 TermOp1.is_dep0_dep2_term p0 p1_1) (wrap2 TermOp2.is_dep0_dep2_term p0 p1_2)

      let mk_dep0_dep2_term (p0 : opname) (p1 : var) (p2 : var) (p3 : term) (p4 : term) =
         let p3_1, p3_2 = p3 in
         let p4_1, p4_2 = p4 in
         merge merge_term "TermOp.mk_dep0_dep2_term" (wrap5 TermOp1.mk_dep0_dep2_term p0 p1 p2 p3_1 p4_1) (wrap5 TermOp2.mk_dep0_dep2_term p0 p1 p2 p3_2 p4_2)

      let dest_dep0_dep2_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         let res1 = wrap2 TermOp1.dest_dep0_dep2_term p0 p1_1 in
         let res2 = wrap2 TermOp2.dest_dep0_dep2_term p0 p1_2 in
         let (res0_1, res1_1, res2_1, res3_1), (res0_2, res1_2, res2_2, res3_2) = merge merge_triv "TermOp.dest_dep0_dep2_term" res1 res2 in
         (merge_var "TermOp.dest_dep0_dep2_term - 0" res0_1 res0_2),
         (merge_var "TermOp.dest_dep0_dep2_term - 1" res1_1 res1_2),
         (merge_term "TermOp.dest_dep0_dep2_term - 2" res2_1 res2_2),
         (merge_term "TermOp.dest_dep0_dep2_term - 3" res3_1 res3_2)

      let is_dep0_dep3_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_dep0_dep3_term" (wrap2 TermOp1.is_dep0_dep3_term p0 p1_1) (wrap2 TermOp2.is_dep0_dep3_term p0 p1_2)

      let mk_dep0_dep3_term (p0 : opname) (p1 : var) (p2 : var) (p3 : var) (p4 : term) (p5 : term) =
         let p4_1, p4_2 = p4 in
         let p5_1, p5_2 = p5 in
         merge merge_term "TermOp.mk_dep0_dep3_term" (wrap6 TermOp1.mk_dep0_dep3_term p0 p1 p2 p3 p4_1 p5_1) (wrap6 TermOp2.mk_dep0_dep3_term p0 p1 p2 p3 p4_2 p5_2)

      let dest_dep0_dep3_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         let res1 = wrap2 TermOp1.dest_dep0_dep3_term p0 p1_1 in
         let res2 = wrap2 TermOp2.dest_dep0_dep3_term p0 p1_2 in
         let (res0_1, res1_1, res2_1, res3_1, res4_1), (res0_2, res1_2, res2_2, res3_2, res4_2) = merge merge_triv "TermOp.dest_dep0_dep3_term" res1 res2 in
         (merge_var "TermOp.dest_dep0_dep3_term - 0" res0_1 res0_2),
         (merge_var "TermOp.dest_dep0_dep3_term - 1" res1_1 res1_2),
         (merge_var "TermOp.dest_dep0_dep3_term - 2" res2_1 res2_2),
         (merge_term "TermOp.dest_dep0_dep3_term - 3" res3_1 res3_2),
         (merge_term "TermOp.dest_dep0_dep3_term - 4" res4_1 res4_2)

      let is_dep2_dep0_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_dep2_dep0_term" (wrap2 TermOp1.is_dep2_dep0_term p0 p1_1) (wrap2 TermOp2.is_dep2_dep0_term p0 p1_2)

      let mk_dep2_dep0_term (p0 : opname) (p1 : var) (p2 : var) (p3 : term) (p4 : term) =
         let p3_1, p3_2 = p3 in
         let p4_1, p4_2 = p4 in
         merge merge_term "TermOp.mk_dep2_dep0_term" (wrap5 TermOp1.mk_dep2_dep0_term p0 p1 p2 p3_1 p4_1) (wrap5 TermOp2.mk_dep2_dep0_term p0 p1 p2 p3_2 p4_2)

      let dest_dep2_dep0_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         let res1 = wrap2 TermOp1.dest_dep2_dep0_term p0 p1_1 in
         let res2 = wrap2 TermOp2.dest_dep2_dep0_term p0 p1_2 in
         let (res0_1, res1_1, res2_1, res3_1), (res0_2, res1_2, res2_2, res3_2) = merge merge_triv "TermOp.dest_dep2_dep0_term" res1 res2 in
         (merge_var "TermOp.dest_dep2_dep0_term - 0" res0_1 res0_2),
         (merge_var "TermOp.dest_dep2_dep0_term - 1" res1_1 res1_2),
         (merge_term "TermOp.dest_dep2_dep0_term - 2" res2_1 res2_2),
         (merge_term "TermOp.dest_dep2_dep0_term - 3" res3_1 res3_2)

      let is_dep0_dep0_dep1_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_dep0_dep0_dep1_term" (wrap2 TermOp1.is_dep0_dep0_dep1_term p0 p1_1) (wrap2 TermOp2.is_dep0_dep0_dep1_term p0 p1_2)

      let mk_dep0_dep0_dep1_term (p0 : opname) (p1 : term) (p2 : term) (p3 : var) (p4 : term) =
         let p1_1, p1_2 = p1 in
         let p2_1, p2_2 = p2 in
         let p4_1, p4_2 = p4 in
         merge merge_term "TermOp.mk_dep0_dep0_dep1_term" (wrap5 TermOp1.mk_dep0_dep0_dep1_term p0 p1_1 p2_1 p3 p4_1) (wrap5 TermOp2.mk_dep0_dep0_dep1_term p0 p1_2 p2_2 p3 p4_2)

      let dest_dep0_dep0_dep1_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         let res1 = wrap2 TermOp1.dest_dep0_dep0_dep1_term p0 p1_1 in
         let res2 = wrap2 TermOp2.dest_dep0_dep0_dep1_term p0 p1_2 in
         let (res0_1, res1_1, res2_1, res3_1), (res0_2, res1_2, res2_2, res3_2) = merge merge_triv "TermOp.dest_dep0_dep0_dep1_term" res1 res2 in
         (merge_term "TermOp.dest_dep0_dep0_dep1_term - 0" res0_1 res0_2),
         (merge_term "TermOp.dest_dep0_dep0_dep1_term - 1" res1_1 res1_2),
         (merge_var "TermOp.dest_dep0_dep0_dep1_term - 2" res2_1 res2_2),
         (merge_term "TermOp.dest_dep0_dep0_dep1_term - 3" res3_1 res3_2)

      let is_dep0_dep0_dep2_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_dep0_dep0_dep2_term" (wrap2 TermOp1.is_dep0_dep0_dep2_term p0 p1_1) (wrap2 TermOp2.is_dep0_dep0_dep2_term p0 p1_2)

      let mk_dep0_dep0_dep2_term (p0 : opname) (p1 : term) (p2 : term) (p3 : var) (p4 : var) (p5 : term) =
         let p1_1, p1_2 = p1 in
         let p2_1, p2_2 = p2 in
         let p5_1, p5_2 = p5 in
         merge merge_term "TermOp.mk_dep0_dep0_dep2_term" (wrap6 TermOp1.mk_dep0_dep0_dep2_term p0 p1_1 p2_1 p3 p4 p5_1) (wrap6 TermOp2.mk_dep0_dep0_dep2_term p0 p1_2 p2_2 p3 p4 p5_2)

      let dest_dep0_dep0_dep2_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         let res1 = wrap2 TermOp1.dest_dep0_dep0_dep2_term p0 p1_1 in
         let res2 = wrap2 TermOp2.dest_dep0_dep0_dep2_term p0 p1_2 in
         let (res0_1, res1_1, res2_1, res3_1, res4_1), (res0_2, res1_2, res2_2, res3_2, res4_2) = merge merge_triv "TermOp.dest_dep0_dep0_dep2_term" res1 res2 in
         (merge_term "TermOp.dest_dep0_dep0_dep2_term - 0" res0_1 res0_2),
         (merge_term "TermOp.dest_dep0_dep0_dep2_term - 1" res1_1 res1_2),
         (merge_var "TermOp.dest_dep0_dep0_dep2_term - 2" res2_1 res2_2),
         (merge_var "TermOp.dest_dep0_dep0_dep2_term - 3" res3_1 res3_2),
         (merge_term "TermOp.dest_dep0_dep0_dep2_term - 4" res4_1 res4_2)

      let is_dep0_dep0_dep1_any_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_bool "TermOp.is_dep0_dep0_dep1_any_term" (wrap1 TermOp1.is_dep0_dep0_dep1_any_term p0_1) (wrap1 TermOp2.is_dep0_dep0_dep1_any_term p0_2)

      let mk_dep0_dep0_dep1_any_term (p0 : operator) (p1 : term) (p2 : term) (p3 : var) (p4 : term) =
         let p0_1, p0_2 = p0 in
         let p1_1, p1_2 = p1 in
         let p2_1, p2_2 = p2 in
         let p4_1, p4_2 = p4 in
         merge merge_term "TermOp.mk_dep0_dep0_dep1_any_term" (wrap5 TermOp1.mk_dep0_dep0_dep1_any_term p0_1 p1_1 p2_1 p3 p4_1) (wrap5 TermOp2.mk_dep0_dep0_dep1_any_term p0_2 p1_2 p2_2 p3 p4_2)

      let dest_dep0_dep0_dep1_any_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         let res1 = wrap1 TermOp1.dest_dep0_dep0_dep1_any_term p0_1 in
         let res2 = wrap1 TermOp2.dest_dep0_dep0_dep1_any_term p0_2 in
         let (res0_1, res1_1, res2_1, res3_1), (res0_2, res1_2, res2_2, res3_2) = merge merge_triv "TermOp.dest_dep0_dep0_dep1_any_term" res1 res2 in
         (merge_term "TermOp.dest_dep0_dep0_dep1_any_term - 0" res0_1 res0_2),
         (merge_term "TermOp.dest_dep0_dep0_dep1_any_term - 1" res1_1 res1_2),
         (merge_var "TermOp.dest_dep0_dep0_dep1_any_term - 2" res2_1 res2_2),
         (merge_term "TermOp.dest_dep0_dep0_dep1_any_term - 3" res3_1 res3_2)

      let is_dep0_dep1_dep1_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_dep0_dep1_dep1_term" (wrap2 TermOp1.is_dep0_dep1_dep1_term p0 p1_1) (wrap2 TermOp2.is_dep0_dep1_dep1_term p0 p1_2)

      let mk_dep0_dep1_dep1_term (p0 : opname) (p1 : term) (p2 : var) (p3 : term) (p4 : var) (p5 : term) =
         let p1_1, p1_2 = p1 in
         let p3_1, p3_2 = p3 in
         let p5_1, p5_2 = p5 in
         merge merge_term "TermOp.mk_dep0_dep1_dep1_term" (wrap6 TermOp1.mk_dep0_dep1_dep1_term p0 p1_1 p2 p3_1 p4 p5_1) (wrap6 TermOp2.mk_dep0_dep1_dep1_term p0 p1_2 p2 p3_2 p4 p5_2)

      let dest_dep0_dep1_dep1_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         let res1 = wrap2 TermOp1.dest_dep0_dep1_dep1_term p0 p1_1 in
         let res2 = wrap2 TermOp2.dest_dep0_dep1_dep1_term p0 p1_2 in
         let (res0_1, res1_1, res2_1, res3_1, res4_1), (res0_2, res1_2, res2_2, res3_2, res4_2) = merge merge_triv "TermOp.dest_dep0_dep1_dep1_term" res1 res2 in
         (merge_term "TermOp.dest_dep0_dep1_dep1_term - 0" res0_1 res0_2),
         (merge_var "TermOp.dest_dep0_dep1_dep1_term - 1" res1_1 res1_2),
         (merge_term "TermOp.dest_dep0_dep1_dep1_term - 2" res2_1 res2_2),
         (merge_var "TermOp.dest_dep0_dep1_dep1_term - 3" res3_1 res3_2),
         (merge_term "TermOp.dest_dep0_dep1_dep1_term - 4" res4_1 res4_2)

      let is_dep0_dep2_dep0_dep2_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_dep0_dep2_dep0_dep2_term" (wrap2 TermOp1.is_dep0_dep2_dep0_dep2_term p0 p1_1) (wrap2 TermOp2.is_dep0_dep2_dep0_dep2_term p0 p1_2)

      let mk_dep0_dep2_dep0_dep2_term (p0 : opname) (p1 : term) (p2 : var) (p3 : var) (p4 : term) (p5 : term) (p6 : var) (p7 : var) (p8 : term) =
         let p1_1, p1_2 = p1 in
         let p4_1, p4_2 = p4 in
         let p5_1, p5_2 = p5 in
         let p8_1, p8_2 = p8 in
         merge merge_term "TermOp.mk_dep0_dep2_dep0_dep2_term" (wrap9 TermOp1.mk_dep0_dep2_dep0_dep2_term p0 p1_1 p2 p3 p4_1 p5_1 p6 p7 p8_1) (wrap9 TermOp2.mk_dep0_dep2_dep0_dep2_term p0 p1_2 p2 p3 p4_2 p5_2 p6 p7 p8_2)

      let dest_dep0_dep2_dep0_dep2_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         let res1 = wrap2 TermOp1.dest_dep0_dep2_dep0_dep2_term p0 p1_1 in
         let res2 = wrap2 TermOp2.dest_dep0_dep2_dep0_dep2_term p0 p1_2 in
         let (res0_1, res1_1, res2_1, res3_1, res4_1, res5_1, res6_1, res7_1), (res0_2, res1_2, res2_2, res3_2, res4_2, res5_2, res6_2, res7_2) = merge merge_triv "TermOp.dest_dep0_dep2_dep0_dep2_term" res1 res2 in
         (merge_term "TermOp.dest_dep0_dep2_dep0_dep2_term - 0" res0_1 res0_2),
         (merge_var "TermOp.dest_dep0_dep2_dep0_dep2_term - 1" res1_1 res1_2),
         (merge_var "TermOp.dest_dep0_dep2_dep0_dep2_term - 2" res2_1 res2_2),
         (merge_term "TermOp.dest_dep0_dep2_dep0_dep2_term - 3" res3_1 res3_2),
         (merge_term "TermOp.dest_dep0_dep2_dep0_dep2_term - 4" res4_1 res4_2),
         (merge_var "TermOp.dest_dep0_dep2_dep0_dep2_term - 5" res5_1 res5_2),
         (merge_var "TermOp.dest_dep0_dep2_dep0_dep2_term - 6" res6_1 res6_2),
         (merge_term "TermOp.dest_dep0_dep2_dep0_dep2_term - 7" res7_1 res7_2)

      let is_dep0_dep0_dep3_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_dep0_dep0_dep3_term" (wrap2 TermOp1.is_dep0_dep0_dep3_term p0 p1_1) (wrap2 TermOp2.is_dep0_dep0_dep3_term p0 p1_2)

      let mk_dep0_dep0_dep3_term (p0 : opname) (p1 : term) (p2 : term) (p3 : var) (p4 : var) (p5 : var) (p6 : term) =
         let p1_1, p1_2 = p1 in
         let p2_1, p2_2 = p2 in
         let p6_1, p6_2 = p6 in
         merge merge_term "TermOp.mk_dep0_dep0_dep3_term" (wrap7 TermOp1.mk_dep0_dep0_dep3_term p0 p1_1 p2_1 p3 p4 p5 p6_1) (wrap7 TermOp2.mk_dep0_dep0_dep3_term p0 p1_2 p2_2 p3 p4 p5 p6_2)

      let dest_dep0_dep0_dep3_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         let res1 = wrap2 TermOp1.dest_dep0_dep0_dep3_term p0 p1_1 in
         let res2 = wrap2 TermOp2.dest_dep0_dep0_dep3_term p0 p1_2 in
         let (res0_1, res1_1, res2_1, res3_1, res4_1, res5_1), (res0_2, res1_2, res2_2, res3_2, res4_2, res5_2) = merge merge_triv "TermOp.dest_dep0_dep0_dep3_term" res1 res2 in
         (merge_term "TermOp.dest_dep0_dep0_dep3_term - 0" res0_1 res0_2),
         (merge_term "TermOp.dest_dep0_dep0_dep3_term - 1" res1_1 res1_2),
         (merge_var "TermOp.dest_dep0_dep0_dep3_term - 2" res2_1 res2_2),
         (merge_var "TermOp.dest_dep0_dep0_dep3_term - 3" res3_1 res3_2),
         (merge_var "TermOp.dest_dep0_dep0_dep3_term - 4" res4_1 res4_2),
         (merge_term "TermOp.dest_dep0_dep0_dep3_term - 5" res5_1 res5_2)

      let is_dep2_dep2_dep0_dep0_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_dep2_dep2_dep0_dep0_term" (wrap2 TermOp1.is_dep2_dep2_dep0_dep0_term p0 p1_1) (wrap2 TermOp2.is_dep2_dep2_dep0_dep0_term p0 p1_2)

      let mk_dep2_dep2_dep0_dep0_term (p0 : opname) (p1 : var) (p2 : var) (p3 : term) (p4 : var) (p5 : var) (p6 : term) (p7 : term) (p8 : term) =
         let p3_1, p3_2 = p3 in
         let p6_1, p6_2 = p6 in
         let p7_1, p7_2 = p7 in
         let p8_1, p8_2 = p8 in
         merge merge_term "TermOp.mk_dep2_dep2_dep0_dep0_term" (wrap9 TermOp1.mk_dep2_dep2_dep0_dep0_term p0 p1 p2 p3_1 p4 p5 p6_1 p7_1 p8_1) (wrap9 TermOp2.mk_dep2_dep2_dep0_dep0_term p0 p1 p2 p3_2 p4 p5 p6_2 p7_2 p8_2)

      let dest_dep2_dep2_dep0_dep0_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         let res1 = wrap2 TermOp1.dest_dep2_dep2_dep0_dep0_term p0 p1_1 in
         let res2 = wrap2 TermOp2.dest_dep2_dep2_dep0_dep0_term p0 p1_2 in
         let (res0_1, res1_1, res2_1, res3_1, res4_1, res5_1, res6_1, res7_1), (res0_2, res1_2, res2_2, res3_2, res4_2, res5_2, res6_2, res7_2) = merge merge_triv "TermOp.dest_dep2_dep2_dep0_dep0_term" res1 res2 in
         (merge_var "TermOp.dest_dep2_dep2_dep0_dep0_term - 0" res0_1 res0_2),
         (merge_var "TermOp.dest_dep2_dep2_dep0_dep0_term - 1" res1_1 res1_2),
         (merge_term "TermOp.dest_dep2_dep2_dep0_dep0_term - 2" res2_1 res2_2),
         (merge_var "TermOp.dest_dep2_dep2_dep0_dep0_term - 3" res3_1 res3_2),
         (merge_var "TermOp.dest_dep2_dep2_dep0_dep0_term - 4" res4_1 res4_2),
         (merge_term "TermOp.dest_dep2_dep2_dep0_dep0_term - 5" res5_1 res5_2),
         (merge_term "TermOp.dest_dep2_dep2_dep0_dep0_term - 6" res6_1 res6_2),
         (merge_term "TermOp.dest_dep2_dep2_dep0_dep0_term - 7" res7_1 res7_2)

      let is_string_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_string_term" (wrap2 TermOp1.is_string_term p0 p1_1) (wrap2 TermOp2.is_string_term p0 p1_2)

      let mk_string_term (p0 : opname) (p1 : string) =
         merge merge_term "TermOp.mk_string_term" (wrap2 TermOp1.mk_string_term p0 p1) (wrap2 TermOp2.mk_string_term p0 p1)

      let dest_string_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_string "TermOp.dest_string_term" (wrap2 TermOp1.dest_string_term p0 p1_1) (wrap2 TermOp2.dest_string_term p0 p1_2)

      let dest_string_param (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_string "TermOp.dest_string_param" (wrap1 TermOp1.dest_string_param p0_1) (wrap1 TermOp2.dest_string_param p0_2)

      let is_string_dep0_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_string_dep0_term" (wrap2 TermOp1.is_string_dep0_term p0 p1_1) (wrap2 TermOp2.is_string_dep0_term p0 p1_2)

      let mk_string_dep0_term (p0 : opname) (p1 : string) (p2 : term) =
         let p2_1, p2_2 = p2 in
         merge merge_term "TermOp.mk_string_dep0_term" (wrap3 TermOp1.mk_string_dep0_term p0 p1 p2_1) (wrap3 TermOp2.mk_string_dep0_term p0 p1 p2_2)

      let dest_string_dep0_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         let res1 = wrap2 TermOp1.dest_string_dep0_term p0 p1_1 in
         let res2 = wrap2 TermOp2.dest_string_dep0_term p0 p1_2 in
         let (res0_1, res1_1), (res0_2, res1_2) = merge merge_triv "TermOp.dest_string_dep0_term" res1 res2 in
         (merge_string "TermOp.dest_string_dep0_term - 0" res0_1 res0_2),
         (merge_term "TermOp.dest_string_dep0_term - 1" res1_1 res1_2)

      let is_string_string_dep0_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_string_string_dep0_term" (wrap2 TermOp1.is_string_string_dep0_term p0 p1_1) (wrap2 TermOp2.is_string_string_dep0_term p0 p1_2)

      let mk_string_string_dep0_term (p0 : opname) (p1 : string) (p2 : string) (p3 : term) =
         let p3_1, p3_2 = p3 in
         merge merge_term "TermOp.mk_string_string_dep0_term" (wrap4 TermOp1.mk_string_string_dep0_term p0 p1 p2 p3_1) (wrap4 TermOp2.mk_string_string_dep0_term p0 p1 p2 p3_2)

      let dest_string_string_dep0_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         let res1 = wrap2 TermOp1.dest_string_string_dep0_term p0 p1_1 in
         let res2 = wrap2 TermOp2.dest_string_string_dep0_term p0 p1_2 in
         let (res0_1, res1_1, res2_1), (res0_2, res1_2, res2_2) = merge merge_triv "TermOp.dest_string_string_dep0_term" res1 res2 in
         (merge_string "TermOp.dest_string_string_dep0_term - 0" res0_1 res0_2),
         (merge_string "TermOp.dest_string_string_dep0_term - 1" res1_1 res1_2),
         (merge_term "TermOp.dest_string_string_dep0_term - 2" res2_1 res2_2)

      let dest_string_string_dep0_any_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         let res1 = wrap1 TermOp1.dest_string_string_dep0_any_term p0_1 in
         let res2 = wrap1 TermOp2.dest_string_string_dep0_any_term p0_2 in
         let (res0_1, res1_1, res2_1), (res0_2, res1_2, res2_2) = merge merge_triv "TermOp.dest_string_string_dep0_any_term" res1 res2 in
         (merge_string "TermOp.dest_string_string_dep0_any_term - 0" res0_1 res0_2),
         (merge_string "TermOp.dest_string_string_dep0_any_term - 1" res1_1 res1_2),
         (merge_term "TermOp.dest_string_string_dep0_any_term - 2" res2_1 res2_2)

      let is_number_dep0_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_number_dep0_term" (wrap2 TermOp1.is_number_dep0_term p0 p1_1) (wrap2 TermOp2.is_number_dep0_term p0 p1_2)

      let mk_number_dep0_term (p0 : opname) (p1 : Lm_num.num) (p2 : term) =
         let p2_1, p2_2 = p2 in
         merge merge_term "TermOp.mk_number_dep0_term" (wrap3 TermOp1.mk_number_dep0_term p0 p1 p2_1) (wrap3 TermOp2.mk_number_dep0_term p0 p1 p2_2)

      let dest_number_dep0_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         let res1 = wrap2 TermOp1.dest_number_dep0_term p0 p1_1 in
         let res2 = wrap2 TermOp2.dest_number_dep0_term p0 p1_2 in
         let (res0_1, res1_1), (res0_2, res1_2) = merge merge_triv "TermOp.dest_number_dep0_term" res1 res2 in
         (merge_num "TermOp.dest_number_dep0_term - 0" res0_1 res0_2),
         (merge_term "TermOp.dest_number_dep0_term - 1" res1_1 res1_2)

      let dest_number_dep0_any_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         let res1 = wrap1 TermOp1.dest_number_dep0_any_term p0_1 in
         let res2 = wrap1 TermOp2.dest_number_dep0_any_term p0_2 in
         let (res0_1, res1_1), (res0_2, res1_2) = merge merge_triv "TermOp.dest_number_dep0_any_term" res1 res2 in
         (merge_num "TermOp.dest_number_dep0_any_term - 0" res0_1 res0_2),
         (merge_term "TermOp.dest_number_dep0_any_term - 1" res1_1 res1_2)

      let is_number_dep1_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_number_dep1_term" (wrap2 TermOp1.is_number_dep1_term p0 p1_1) (wrap2 TermOp2.is_number_dep1_term p0 p1_2)

      let mk_number_dep1_term (p0 : opname) (p1 : Lm_num.num) (p2 : var) (p3 : term) =
         let p3_1, p3_2 = p3 in
         merge merge_term "TermOp.mk_number_dep1_term" (wrap4 TermOp1.mk_number_dep1_term p0 p1 p2 p3_1) (wrap4 TermOp2.mk_number_dep1_term p0 p1 p2 p3_2)

      let dest_number_dep1_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         let res1 = wrap2 TermOp1.dest_number_dep1_term p0 p1_1 in
         let res2 = wrap2 TermOp2.dest_number_dep1_term p0 p1_2 in
         let (res0_1, res1_1, res2_1), (res0_2, res1_2, res2_2) = merge merge_triv "TermOp.dest_number_dep1_term" res1 res2 in
         (merge_num "TermOp.dest_number_dep1_term - 0" res0_1 res0_2),
         (merge_var "TermOp.dest_number_dep1_term - 1" res1_1 res1_2),
         (merge_term "TermOp.dest_number_dep1_term - 2" res2_1 res2_2)

      let dest_number_dep1_any_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         let res1 = wrap1 TermOp1.dest_number_dep1_any_term p0_1 in
         let res2 = wrap1 TermOp2.dest_number_dep1_any_term p0_2 in
         let (res0_1, res1_1, res2_1), (res0_2, res1_2, res2_2) = merge merge_triv "TermOp.dest_number_dep1_any_term" res1 res2 in
         (merge_num "TermOp.dest_number_dep1_any_term - 0" res0_1 res0_2),
         (merge_var "TermOp.dest_number_dep1_any_term - 1" res1_1 res1_2),
         (merge_term "TermOp.dest_number_dep1_any_term - 2" res2_1 res2_2)

      let is_number_number_dep0_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_number_number_dep0_term" (wrap2 TermOp1.is_number_number_dep0_term p0 p1_1) (wrap2 TermOp2.is_number_number_dep0_term p0 p1_2)

      let mk_number_number_dep0_term (p0 : opname) (p1 : Lm_num.num) (p2 : Lm_num.num) (p3 : term) =
         let p3_1, p3_2 = p3 in
         merge merge_term "TermOp.mk_number_number_dep0_term" (wrap4 TermOp1.mk_number_number_dep0_term p0 p1 p2 p3_1) (wrap4 TermOp2.mk_number_number_dep0_term p0 p1 p2 p3_2)

      let dest_number_number_dep0_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         let res1 = wrap2 TermOp1.dest_number_number_dep0_term p0 p1_1 in
         let res2 = wrap2 TermOp2.dest_number_number_dep0_term p0 p1_2 in
         let (res0_1, res1_1, res2_1), (res0_2, res1_2, res2_2) = merge merge_triv "TermOp.dest_number_number_dep0_term" res1 res2 in
         (merge_num "TermOp.dest_number_number_dep0_term - 0" res0_1 res0_2),
         (merge_num "TermOp.dest_number_number_dep0_term - 1" res1_1 res1_2),
         (merge_term "TermOp.dest_number_number_dep0_term - 2" res2_1 res2_2)

      let dest_number_number_dep0_any_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         let res1 = wrap1 TermOp1.dest_number_number_dep0_any_term p0_1 in
         let res2 = wrap1 TermOp2.dest_number_number_dep0_any_term p0_2 in
         let (res0_1, res1_1, res2_1), (res0_2, res1_2, res2_2) = merge merge_triv "TermOp.dest_number_number_dep0_any_term" res1 res2 in
         (merge_num "TermOp.dest_number_number_dep0_any_term - 0" res0_1 res0_2),
         (merge_num "TermOp.dest_number_number_dep0_any_term - 1" res1_1 res1_2),
         (merge_term "TermOp.dest_number_number_dep0_any_term - 2" res2_1 res2_2)

      let is_number_number_string_dep0_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_number_number_string_dep0_term" (wrap2 TermOp1.is_number_number_string_dep0_term p0 p1_1) (wrap2 TermOp2.is_number_number_string_dep0_term p0 p1_2)

      let mk_number_number_string_dep0_term (p0 : opname) (p1 : Lm_num.num) (p2 : Lm_num.num) (p3 : string) (p4 : term) =
         let p4_1, p4_2 = p4 in
         merge merge_term "TermOp.mk_number_number_string_dep0_term" (wrap5 TermOp1.mk_number_number_string_dep0_term p0 p1 p2 p3 p4_1) (wrap5 TermOp2.mk_number_number_string_dep0_term p0 p1 p2 p3 p4_2)

      let dest_number_number_string_dep0_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         let res1 = wrap2 TermOp1.dest_number_number_string_dep0_term p0 p1_1 in
         let res2 = wrap2 TermOp2.dest_number_number_string_dep0_term p0 p1_2 in
         let (res0_1, res1_1, res2_1, res3_1), (res0_2, res1_2, res2_2, res3_2) = merge merge_triv "TermOp.dest_number_number_string_dep0_term" res1 res2 in
         (merge_num "TermOp.dest_number_number_string_dep0_term - 0" res0_1 res0_2),
         (merge_num "TermOp.dest_number_number_string_dep0_term - 1" res1_1 res1_2),
         (merge_string "TermOp.dest_number_number_string_dep0_term - 2" res2_1 res2_2),
         (merge_term "TermOp.dest_number_number_string_dep0_term - 3" res3_1 res3_2)

      let dest_number_number_string_dep0_any_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         let res1 = wrap1 TermOp1.dest_number_number_string_dep0_any_term p0_1 in
         let res2 = wrap1 TermOp2.dest_number_number_string_dep0_any_term p0_2 in
         let (res0_1, res1_1, res2_1, res3_1), (res0_2, res1_2, res2_2, res3_2) = merge merge_triv "TermOp.dest_number_number_string_dep0_any_term" res1 res2 in
         (merge_num "TermOp.dest_number_number_string_dep0_any_term - 0" res0_1 res0_2),
         (merge_num "TermOp.dest_number_number_string_dep0_any_term - 1" res1_1 res1_2),
         (merge_string "TermOp.dest_number_number_string_dep0_any_term - 2" res2_1 res2_2),
         (merge_term "TermOp.dest_number_number_string_dep0_any_term - 3" res3_1 res3_2)

      let is_string_string_dep0_dep0_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_string_string_dep0_dep0_term" (wrap2 TermOp1.is_string_string_dep0_dep0_term p0 p1_1) (wrap2 TermOp2.is_string_string_dep0_dep0_term p0 p1_2)

      let mk_string_string_dep0_dep0_term (p0 : opname) (p1 : string) (p2 : string) (p3 : term) (p4 : term) =
         let p3_1, p3_2 = p3 in
         let p4_1, p4_2 = p4 in
         merge merge_term "TermOp.mk_string_string_dep0_dep0_term" (wrap5 TermOp1.mk_string_string_dep0_dep0_term p0 p1 p2 p3_1 p4_1) (wrap5 TermOp2.mk_string_string_dep0_dep0_term p0 p1 p2 p3_2 p4_2)

      let dest_string_string_dep0_dep0_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         let res1 = wrap2 TermOp1.dest_string_string_dep0_dep0_term p0 p1_1 in
         let res2 = wrap2 TermOp2.dest_string_string_dep0_dep0_term p0 p1_2 in
         let (res0_1, res1_1, res2_1, res3_1), (res0_2, res1_2, res2_2, res3_2) = merge merge_triv "TermOp.dest_string_string_dep0_dep0_term" res1 res2 in
         (merge_string "TermOp.dest_string_string_dep0_dep0_term - 0" res0_1 res0_2),
         (merge_string "TermOp.dest_string_string_dep0_dep0_term - 1" res1_1 res1_2),
         (merge_term "TermOp.dest_string_string_dep0_dep0_term - 2" res2_1 res2_2),
         (merge_term "TermOp.dest_string_string_dep0_dep0_term - 3" res3_1 res3_2)

      let dest_string_string_dep0_dep0_any_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         let res1 = wrap1 TermOp1.dest_string_string_dep0_dep0_any_term p0_1 in
         let res2 = wrap1 TermOp2.dest_string_string_dep0_dep0_any_term p0_2 in
         let (res0_1, res1_1, res2_1, res3_1), (res0_2, res1_2, res2_2, res3_2) = merge merge_triv "TermOp.dest_string_string_dep0_dep0_any_term" res1 res2 in
         (merge_string "TermOp.dest_string_string_dep0_dep0_any_term - 0" res0_1 res0_2),
         (merge_string "TermOp.dest_string_string_dep0_dep0_any_term - 1" res1_1 res1_2),
         (merge_term "TermOp.dest_string_string_dep0_dep0_any_term - 2" res2_1 res2_2),
         (merge_term "TermOp.dest_string_string_dep0_dep0_any_term - 3" res3_1 res3_2)

      let is_number_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_number_term" (wrap2 TermOp1.is_number_term p0 p1_1) (wrap2 TermOp2.is_number_term p0 p1_2)

      let mk_number_term (p0 : opname) (p1 : Lm_num.num) =
         merge merge_term "TermOp.mk_number_term" (wrap2 TermOp1.mk_number_term p0 p1) (wrap2 TermOp2.mk_number_term p0 p1)

      let dest_number_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_num "TermOp.dest_number_term" (wrap2 TermOp1.dest_number_term p0 p1_1) (wrap2 TermOp2.dest_number_term p0 p1_2)

      let dest_number_any_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_num "TermOp.dest_number_any_term" (wrap1 TermOp1.dest_number_any_term p0_1) (wrap1 TermOp2.dest_number_any_term p0_2)

      let is_univ_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_univ_term" (wrap2 TermOp1.is_univ_term p0 p1_1) (wrap2 TermOp2.is_univ_term p0 p1_2)

      let mk_univ_term (p0 : opname) (p1 : level_exp) =
         let p1_1, p1_2 = p1 in
         merge merge_term "TermOp.mk_univ_term" (wrap2 TermOp1.mk_univ_term p0 p1_1) (wrap2 TermOp2.mk_univ_term p0 p1_2)

      let dest_univ_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_level_exp "TermOp.dest_univ_term" (wrap2 TermOp1.dest_univ_term p0 p1_1) (wrap2 TermOp2.dest_univ_term p0 p1_2)

      let is_token_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_token_term" (wrap2 TermOp1.is_token_term p0 p1_1) (wrap2 TermOp2.is_token_term p0 p1_2)

      let mk_token_term (p0 : opname) (p1 : string) =
         merge merge_term "TermOp.mk_token_term" (wrap2 TermOp1.mk_token_term p0 p1) (wrap2 TermOp2.mk_token_term p0 p1)

      let dest_token_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_string "TermOp.dest_token_term" (wrap2 TermOp1.dest_token_term p0 p1_1) (wrap2 TermOp2.dest_token_term p0 p1_2)

      let is_token_simple_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermOp.is_token_simple_term" (wrap2 TermOp1.is_token_simple_term p0 p1_1) (wrap2 TermOp2.is_token_simple_term p0 p1_2)

      let mk_token_simple_term (p0 : opname) (p1 : string) (p2 : term list) =
         let p2_1, p2_2 = split p2 in
         merge merge_term "TermOp.mk_token_simple_term" (wrap3 TermOp1.mk_token_simple_term p0 p1 p2_1) (wrap3 TermOp2.mk_token_simple_term p0 p1 p2_2)

      let dest_token_simple_term (p0 : opname) (p1 : term) =
         let p1_1, p1_2 = p1 in
         let res1 = wrap2 TermOp1.dest_token_simple_term p0 p1_1 in
         let res2 = wrap2 TermOp2.dest_token_simple_term p0 p1_2 in
         let (res0_1, res1_1), (res0_2, res1_2) = merge merge_triv "TermOp.dest_token_simple_term" res1 res2 in
         (merge_string "TermOp.dest_token_simple_term - 0" res0_1 res0_2),
         (merge_terms "TermOp.dest_token_simple_term - 1" res1_1 res1_2)

   end

   module TermAddr = struct
      module AddrTypes = TermType
      type address = TermType.address

      let string_of_address (a1, a2) =
         sprintf "Impl1 addr: %s; Impl2 addr: %s" (TermAddr1.string_of_address a1) (TermAddr2.string_of_address a2)

      (* The rest of this module is auto-generated by the util/gen_refiner_debug.pl script *)

      let make_address (p0 : int list) =
         merge merge_address "TermAddr.make_address" (wrap1 TermAddr1.make_address p0) (wrap1 TermAddr2.make_address p0)

      let compose_address (p0 : address) (p1 : address) =
         let p0_1, p0_2 = p0 in
         let p1_1, p1_2 = p1 in
         merge merge_address "TermAddr.compose_address" (wrap2 TermAddr1.compose_address p0_1 p1_1) (wrap2 TermAddr2.compose_address p0_2 p1_2)

      let split_clause_address (p0 : address) =
         let p0_1, p0_2 = p0 in
         let res1 = wrap1 TermAddr1.split_clause_address p0_1 in
         let res2 = wrap1 TermAddr2.split_clause_address p0_2 in
         let (res0_1, res1_1), (res0_2, res1_2) = merge merge_triv "TermAddr.split_clause_address" res1 res2 in
         (merge_address "TermAddr.split_clause_address - 0" res0_1 res0_2),
         (merge_address "TermAddr.split_clause_address - 1" res1_1 res1_2)

      let find_subterm (p0 : term) (p1 : term) =
         let p0_1, p0_2 = p0 in
         let p1_1, p1_2 = p1 in
         merge merge_address "TermAddr.find_subterm" (wrap2 TermAddr1.find_subterm p0_1 p1_1) (wrap2 TermAddr2.find_subterm p0_2 p1_2)

      let term_subterm (p0 : term) (p1 : address) =
         let p0_1, p0_2 = p0 in
         let p1_1, p1_2 = p1 in
         merge merge_term "TermAddr.term_subterm" (wrap2 TermAddr1.term_subterm p0_1 p1_1) (wrap2 TermAddr2.term_subterm p0_2 p1_2)

      let replace_subterm (p0 : term) (p1 : address) (p2 : term) =
         let p0_1, p0_2 = p0 in
         let p1_1, p1_2 = p1 in
         let p2_1, p2_2 = p2 in
         merge merge_term "TermAddr.replace_subterm" (wrap3 TermAddr1.replace_subterm p0_1 p1_1 p2_1) (wrap3 TermAddr2.replace_subterm p0_2 p1_2 p2_2)

      let replace_bound_subterm (p0 : term) (p1 : address) (p2 : SymbolSet.t) (p3 : (SymbolSet.t -> term)) =
         let p0_1, p0_2 = p0 in
         let p1_1, p1_2 = p1 in
         let p3_1, p3_2 = split_atf p3 in
         merge merge_term "TermAddr.replace_bound_subterm" (wrap4 TermAddr1.replace_bound_subterm p0_1 p1_1 p2 p3_1) (wrap4 TermAddr2.replace_bound_subterm p0_2 p1_2 p2 p3_2)

      let apply_fun_at_addr (p0 : (term -> term)) (p1 : address) (p2 : term) =
         let p0_1, p0_2 = split_ttf p0 in
         let p1_1, p1_2 = p1 in
         let p2_1, p2_2 = p2 in
         merge merge_term "TermAddr.apply_fun_at_addr" (wrap3 TermAddr1.apply_fun_at_addr p0_1 p1_1 p2_1) (wrap3 TermAddr2.apply_fun_at_addr p0_2 p1_2 p2_2)

      let apply_fun_arg_at_addr (p0 : (term -> term * 'a)) (p1 : address) (p2 : term) =
         let p0_1, p0_2 = split_ttaf p0 in
         let p1_1, p1_2 = p1 in
         let p2_1, p2_2 = p2 in
         let res1 = wrap3 TermAddr1.apply_fun_arg_at_addr p0_1 p1_1 p2_1 in
         let res2 = wrap3 TermAddr2.apply_fun_arg_at_addr p0_2 p1_2 p2_2 in
         let (res0_1, res1_1), (res0_2, res1_2) = merge merge_triv "TermAddr.apply_fun_arg_at_addr" res1 res2 in
         (merge_term "TermAddr.apply_fun_arg_at_addr - 0" res0_1 res0_2),
         (merge_poly "TermAddr.apply_fun_arg_at_addr - 1" res1_1 res1_2)

      let apply_var_fun_at_addr (p0 : (SymbolSet.t -> term -> term)) (p1 : address) (p2 : SymbolSet.t) (p3 : term) =
         let p0_1, p0_2 = split_attf p0 in
         let p1_1, p1_2 = p1 in
         let p3_1, p3_2 = p3 in
         merge merge_term "TermAddr.apply_var_fun_at_addr" (wrap4 TermAddr1.apply_var_fun_at_addr p0_1 p1_1 p2 p3_1) (wrap4 TermAddr2.apply_var_fun_at_addr p0_2 p1_2 p2 p3_2)

      let apply_var_fun_arg_at_addr (p0 : (SymbolSet.t -> term -> term * 'a)) (p1 : address) (p2 : SymbolSet.t) (p3 : term) =
         let p0_1, p0_2 = split_attaf p0 in
         let p1_1, p1_2 = p1 in
         let p3_1, p3_2 = p3 in
         let res1 = wrap4 TermAddr1.apply_var_fun_arg_at_addr p0_1 p1_1 p2 p3_1 in
         let res2 = wrap4 TermAddr2.apply_var_fun_arg_at_addr p0_2 p1_2 p2 p3_2 in
         let (res0_1, res1_1), (res0_2, res1_2) = merge merge_triv "TermAddr.apply_var_fun_arg_at_addr" res1 res2 in
         (merge_term "TermAddr.apply_var_fun_arg_at_addr - 0" res0_1 res0_2),
         (merge_poly "TermAddr.apply_var_fun_arg_at_addr - 1" res1_1 res1_2)

      let subterm_addresses (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_addresss "TermAddr.subterm_addresses" (wrap1 TermAddr1.subterm_addresses p0_1) (wrap1 TermAddr2.subterm_addresses p0_2)

      let apply_fun_higher (p0 : (term -> term * 'a)) (p1 : term) =
         let p0_1, p0_2 = split_ttaf p0 in
         let p1_1, p1_2 = p1 in
         let res1 = wrap2 TermAddr1.apply_fun_higher p0_1 p1_1 in
         let res2 = wrap2 TermAddr2.apply_fun_higher p0_2 p1_2 in
         let (res0_1, res1_1), (res0_2, res1_2) = merge merge_triv "TermAddr.apply_fun_higher" res1 res2 in
         (merge_term "TermAddr.apply_fun_higher - 0" res0_1 res0_2),
         (merge_poly "TermAddr.apply_fun_higher - 1" res1_1 res1_2)

      let apply_var_fun_higher (p0 : (SymbolSet.t -> term -> term * 'a)) (p1 : SymbolSet.t) (p2 : term) =
         let p0_1, p0_2 = split_attaf p0 in
         let p2_1, p2_2 = p2 in
         let res1 = wrap3 TermAddr1.apply_var_fun_higher p0_1 p1 p2_1 in
         let res2 = wrap3 TermAddr2.apply_var_fun_higher p0_2 p1 p2_2 in
         let (res0_1, res1_1), (res0_2, res1_2) = merge merge_triv "TermAddr.apply_var_fun_higher" res1 res2 in
         (merge_term "TermAddr.apply_var_fun_higher - 0" res0_1 res0_2),
         (merge_poly "TermAddr.apply_var_fun_higher - 1" res1_1 res1_2)

      let nth_hyp_addr (p0 : term) (p1 : int) =
         let p0_1, p0_2 = p0 in
         merge merge_address "TermAddr.nth_hyp_addr" (wrap2 TermAddr1.nth_hyp_addr p0_1 p1) (wrap2 TermAddr2.nth_hyp_addr p0_2 p1)

      let concl_addr (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_address "TermAddr.concl_addr" (wrap1 TermAddr1.concl_addr p0_1) (wrap1 TermAddr2.concl_addr p0_2)

      let nth_clause_addr (p0 : term) (p1 : int) =
         let p0_1, p0_2 = p0 in
         merge merge_address "TermAddr.nth_clause_addr" (wrap2 TermAddr1.nth_clause_addr p0_1 p1) (wrap2 TermAddr2.nth_clause_addr p0_2 p1)

   end

   module TermMan = struct
      module ManTypes = TermType

      (* The rest of this module is auto-generated by the util/gen_refiner_debug.pl script *)

      let mk_const_level_exp (p0 : int) =
         merge merge_level_exp "TermMan.mk_const_level_exp" (wrap1 TermMan1.mk_const_level_exp p0) (wrap1 TermMan2.mk_const_level_exp p0)

      let mk_var_level_exp (p0 : var) =
         merge merge_level_exp "TermMan.mk_var_level_exp" (wrap1 TermMan1.mk_var_level_exp p0) (wrap1 TermMan2.mk_var_level_exp p0)

      let max_level_exp (p0 : level_exp) (p1 : level_exp) (p2 : int) =
         let p0_1, p0_2 = p0 in
         let p1_1, p1_2 = p1 in
         merge merge_level_exp "TermMan.max_level_exp" (wrap3 TermMan1.max_level_exp p0_1 p1_1 p2) (wrap3 TermMan2.max_level_exp p0_2 p1_2 p2)

      let incr_level_exp (p0 : level_exp) =
         let p0_1, p0_2 = p0 in
         merge merge_level_exp "TermMan.incr_level_exp" (wrap1 TermMan1.incr_level_exp p0_1) (wrap1 TermMan2.incr_level_exp p0_2)

      let level_le (p0 : level_exp) (p1 : level_exp) =
         let p0_1, p0_2 = p0 in
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermMan.level_le" (wrap2 TermMan1.level_le p0_1 p1_1) (wrap2 TermMan2.level_le p0_2 p1_2)

      let level_lt (p0 : level_exp) (p1 : level_exp) =
         let p0_1, p0_2 = p0 in
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermMan.level_lt" (wrap2 TermMan1.level_lt p0_1 p1_1) (wrap2 TermMan2.level_lt p0_2 p1_2)

      let is_so_var_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_bool "TermMan.is_so_var_term" (wrap1 TermMan1.is_so_var_term p0_1) (wrap1 TermMan2.is_so_var_term p0_2)

      let dest_so_var (p0 : term) =
         let p0_1, p0_2 = p0 in
         let res1 = wrap1 TermMan1.dest_so_var p0_1 in
         let res2 = wrap1 TermMan2.dest_so_var p0_2 in
         let (res0_1, res1_1, res2_1), (res0_2, res1_2, res2_2) = merge merge_triv "TermMan.dest_so_var" res1 res2 in
         (merge_var "TermMan.dest_so_var - 0" res0_1 res0_2),
         (merge_vars "TermMan.dest_so_var - 1" res1_1 res1_2),
         (merge_terms "TermMan.dest_so_var - 2" res2_1 res2_2)

      let mk_so_var_term (p0 : var) (p1 : var list) (p2 : term list) =
         let p2_1, p2_2 = split p2 in
         merge merge_term "TermMan.mk_so_var_term" (wrap3 TermMan1.mk_so_var_term p0 p1 p2_1) (wrap3 TermMan2.mk_so_var_term p0 p1 p2_2)

      let is_fso_var_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_bool "TermMan.is_fso_var_term" (wrap1 TermMan1.is_fso_var_term p0_1) (wrap1 TermMan2.is_fso_var_term p0_2)

      let dest_fso_var (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_var "TermMan.dest_fso_var" (wrap1 TermMan1.dest_fso_var p0_1) (wrap1 TermMan2.dest_fso_var p0_2)

      let is_context_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_bool "TermMan.is_context_term" (wrap1 TermMan1.is_context_term p0_1) (wrap1 TermMan2.is_context_term p0_2)

      let dest_context (p0 : term) =
         let p0_1, p0_2 = p0 in
         let res1 = wrap1 TermMan1.dest_context p0_1 in
         let res2 = wrap1 TermMan2.dest_context p0_2 in
         let (res0_1, res1_1, res2_1, res3_1), (res0_2, res1_2, res2_2, res3_2) = merge merge_triv "TermMan.dest_context" res1 res2 in
         (merge_var "TermMan.dest_context - 0" res0_1 res0_2),
         (merge_term "TermMan.dest_context - 1" res1_1 res1_2),
         (merge_vars "TermMan.dest_context - 2" res2_1 res2_2),
         (merge_terms "TermMan.dest_context - 3" res3_1 res3_2)

      let mk_context_term (p0 : var) (p1 : term) (p2 : var list) (p3 : term list) =
         let p1_1, p1_2 = p1 in
         let p3_1, p3_2 = split p3 in
         merge merge_term "TermMan.mk_context_term" (wrap4 TermMan1.mk_context_term p0 p1_1 p2 p3_1) (wrap4 TermMan2.mk_context_term p0 p1_2 p2 p3_2)

      let free_meta_variables (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_ss "TermMan.free_meta_variables" (wrap1 TermMan1.free_meta_variables p0_1) (wrap1 TermMan2.free_meta_variables p0_2)

      let explode_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_match_term "TermMan.explode_term" (wrap1 TermMan1.explode_term p0_1) (wrap1 TermMan2.explode_term p0_2)

      let is_sequent_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_bool "TermMan.is_sequent_term" (wrap1 TermMan1.is_sequent_term p0_1) (wrap1 TermMan2.is_sequent_term p0_2)

      let mk_sequent_term (p0 : esequent) =
         let p0_1, p0_2 = split_eseq p0 in
         merge merge_term "TermMan.mk_sequent_term" (wrap1 TermMan1.mk_sequent_term p0_1) (wrap1 TermMan2.mk_sequent_term p0_2)

      let explode_sequent (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_esequent "TermMan.explode_sequent" (wrap1 TermMan1.explode_sequent p0_1) (wrap1 TermMan2.explode_sequent p0_2)

      let explode_sequent_and_rename (p0 : term) (p1 : SymbolSet.t) =
         let p0_1, p0_2 = p0 in
         merge merge_esequent "TermMan.explode_sequent_and_rename" (wrap2 TermMan1.explode_sequent_and_rename p0_1 p1) (wrap2 TermMan2.explode_sequent_and_rename p0_2 p1)

      let nth_hyp (p0 : term) (p1 : int) =
         let p0_1, p0_2 = p0 in
         merge merge_term "TermMan.nth_hyp" (wrap2 TermMan1.nth_hyp p0_1 p1) (wrap2 TermMan2.nth_hyp p0_2 p1)

      let nth_binding (p0 : term) (p1 : int) =
         let p0_1, p0_2 = p0 in
         merge merge_var "TermMan.nth_binding" (wrap2 TermMan1.nth_binding p0_1 p1) (wrap2 TermMan2.nth_binding p0_2 p1)

      let concl (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_term "TermMan.concl" (wrap1 TermMan1.concl p0_1) (wrap1 TermMan2.concl p0_2)

      let num_hyps (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_int "TermMan.num_hyps" (wrap1 TermMan1.num_hyps p0_1) (wrap1 TermMan2.num_hyps p0_2)

      let declared_vars (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_vars "TermMan.declared_vars" (wrap1 TermMan1.declared_vars p0_1) (wrap1 TermMan2.declared_vars p0_2)

      let get_decl_number (p0 : term) (p1 : var) =
         let p0_1, p0_2 = p0 in
         merge merge_int "TermMan.get_decl_number" (wrap2 TermMan1.get_decl_number p0_1 p1) (wrap2 TermMan2.get_decl_number p0_2 p1)

      let get_hyp_number (p0 : term) (p1 : term) =
         let p0_1, p0_2 = p0 in
         let p1_1, p1_2 = p1 in
         merge merge_int "TermMan.get_hyp_number" (wrap2 TermMan1.get_hyp_number p0_1 p1_1) (wrap2 TermMan2.get_hyp_number p0_2 p1_2)

      let replace_concl (p0 : term) (p1 : term) =
         let p0_1, p0_2 = p0 in
         let p1_1, p1_2 = p1 in
         merge merge_term "TermMan.replace_concl" (wrap2 TermMan1.replace_concl p0_1 p1_1) (wrap2 TermMan2.replace_concl p0_2 p1_2)

      let is_xrewrite_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_bool "TermMan.is_xrewrite_term" (wrap1 TermMan1.is_xrewrite_term p0_1) (wrap1 TermMan2.is_xrewrite_term p0_2)

      let mk_xrewrite_term (p0 : term) (p1 : term) =
         let p0_1, p0_2 = p0 in
         let p1_1, p1_2 = p1 in
         merge merge_term "TermMan.mk_xrewrite_term" (wrap2 TermMan1.mk_xrewrite_term p0_1 p1_1) (wrap2 TermMan2.mk_xrewrite_term p0_2 p1_2)

      let dest_xrewrite (p0 : term) =
         let p0_1, p0_2 = p0 in
         let res1 = wrap1 TermMan1.dest_xrewrite p0_1 in
         let res2 = wrap1 TermMan2.dest_xrewrite p0_2 in
         let (res0_1, res1_1), (res0_2, res1_2) = merge merge_triv "TermMan.dest_xrewrite" res1 res2 in
         (merge_term "TermMan.dest_xrewrite - 0" res0_1 res0_2),
         (merge_term "TermMan.dest_xrewrite - 1" res1_1 res1_2)

      let is_xnil_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_bool "TermMan.is_xnil_term" (wrap1 TermMan1.is_xnil_term p0_1) (wrap1 TermMan2.is_xnil_term p0_2)

      let xnil_term =
         merge_term "TermMan.xnil_term" (TermMan1.xnil_term) (TermMan2.xnil_term)

      let is_xcons_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_bool "TermMan.is_xcons_term" (wrap1 TermMan1.is_xcons_term p0_1) (wrap1 TermMan2.is_xcons_term p0_2)

      let mk_xcons_term (p0 : term) (p1 : term) =
         let p0_1, p0_2 = p0 in
         let p1_1, p1_2 = p1 in
         merge merge_term "TermMan.mk_xcons_term" (wrap2 TermMan1.mk_xcons_term p0_1 p1_1) (wrap2 TermMan2.mk_xcons_term p0_2 p1_2)

      let dest_xcons (p0 : term) =
         let p0_1, p0_2 = p0 in
         let res1 = wrap1 TermMan1.dest_xcons p0_1 in
         let res2 = wrap1 TermMan2.dest_xcons p0_2 in
         let (res0_1, res1_1), (res0_2, res1_2) = merge merge_triv "TermMan.dest_xcons" res1 res2 in
         (merge_term "TermMan.dest_xcons - 0" res0_1 res0_2),
         (merge_term "TermMan.dest_xcons - 1" res1_1 res1_2)

      let is_xlist_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_bool "TermMan.is_xlist_term" (wrap1 TermMan1.is_xlist_term p0_1) (wrap1 TermMan2.is_xlist_term p0_2)

      let dest_xlist (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_terms "TermMan.dest_xlist" (wrap1 TermMan1.dest_xlist p0_1) (wrap1 TermMan2.dest_xlist p0_2)

      let mk_xlist_term (p0 : term list) =
         let p0_1, p0_2 = split p0 in
         merge merge_term "TermMan.mk_xlist_term" (wrap1 TermMan1.mk_xlist_term p0_1) (wrap1 TermMan2.mk_xlist_term p0_2)

      let is_xstring_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_bool "TermMan.is_xstring_term" (wrap1 TermMan1.is_xstring_term p0_1) (wrap1 TermMan2.is_xstring_term p0_2)

      let mk_xstring_term (p0 : string) =
         merge merge_term "TermMan.mk_xstring_term" (wrap1 TermMan1.mk_xstring_term p0) (wrap1 TermMan2.mk_xstring_term p0)

      let dest_xstring (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_string "TermMan.dest_xstring" (wrap1 TermMan1.dest_xstring p0_1) (wrap1 TermMan2.dest_xstring p0_2)

      let is_xstring_dep0_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_bool "TermMan.is_xstring_dep0_term" (wrap1 TermMan1.is_xstring_dep0_term p0_1) (wrap1 TermMan2.is_xstring_dep0_term p0_2)

      let mk_xstring_dep0_term (p0 : string) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_term "TermMan.mk_xstring_dep0_term" (wrap2 TermMan1.mk_xstring_dep0_term p0 p1_1) (wrap2 TermMan2.mk_xstring_dep0_term p0 p1_2)

      let dest_xstring_dep0_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         let res1 = wrap1 TermMan1.dest_xstring_dep0_term p0_1 in
         let res2 = wrap1 TermMan2.dest_xstring_dep0_term p0_2 in
         let (res0_1, res1_1), (res0_2, res1_2) = merge merge_triv "TermMan.dest_xstring_dep0_term" res1 res2 in
         (merge_string "TermMan.dest_xstring_dep0_term - 0" res0_1 res0_2),
         (merge_term "TermMan.dest_xstring_dep0_term - 1" res1_1 res1_2)

      let is_xbind_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_bool "TermMan.is_xbind_term" (wrap1 TermMan1.is_xbind_term p0_1) (wrap1 TermMan2.is_xbind_term p0_2)

      let mk_xbind_term (p0 : var) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_term "TermMan.mk_xbind_term" (wrap2 TermMan1.mk_xbind_term p0 p1_1) (wrap2 TermMan2.mk_xbind_term p0 p1_2)

      let construct_redex (p0 : var array) (p1 : term list) (p2 : term list) =
         let p1_1, p1_2 = split p1 in
         let p2_1, p2_2 = split p2 in
         merge merge_term "TermMan.construct_redex" (wrap3 TermMan1.construct_redex p0 p1_1 p2_1) (wrap3 TermMan2.construct_redex p0 p1_2 p2_2)

   end

   module TermSubst = struct
      module SubstTypes = TermType
      type term_subst = (var * term) list

      (* The rest of this module is auto-generated by the util/gen_refiner_debug.pl script *)

      let subst (p0 : term) (p1 : var list) (p2 : term list) =
         let p0_1, p0_2 = p0 in
         let p2_1, p2_2 = split p2 in
         merge merge_term "TermSubst.subst" (wrap3 TermSubst1.subst p0_1 p1 p2_1) (wrap3 TermSubst2.subst p0_2 p1 p2_2)

      let subst1 (p0 : term) (p1 : var) (p2 : term) =
         let p0_1, p0_2 = p0 in
         let p2_1, p2_2 = p2 in
         merge merge_term "TermSubst.subst1" (wrap3 TermSubst1.subst1 p0_1 p1 p2_1) (wrap3 TermSubst2.subst1 p0_2 p1 p2_2)

      let apply_subst (p0 : term_subst) (p1 : term) =
         let p0_1, p0_2 = split_term_subst p0 in
         let p1_1, p1_2 = p1 in
         merge merge_term "TermSubst.apply_subst" (wrap2 TermSubst1.apply_subst p0_1 p1_1) (wrap2 TermSubst2.apply_subst p0_2 p1_2)

      let dest_bterm_and_rename (p0 : bound_term) (p1 : SymbolSet.t) =
         let p0_1, p0_2 = p0 in
         merge merge_bterm' "TermSubst.dest_bterm_and_rename" (wrap2 TermSubst1.dest_bterm_and_rename p0_1 p1) (wrap2 TermSubst2.dest_bterm_and_rename p0_2 p1)

      let var_subst (p0 : term) (p1 : term) (p2 : var) =
         let p0_1, p0_2 = p0 in
         let p1_1, p1_2 = p1 in
         merge merge_term "TermSubst.var_subst" (wrap3 TermSubst1.var_subst p0_1 p1_1 p2) (wrap3 TermSubst2.var_subst p0_2 p1_2 p2)

      let equal_params (p0 : param) (p1 : param) =
         let p0_1, p0_2 = p0 in
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermSubst.equal_params" (wrap2 TermSubst1.equal_params p0_1 p1_1) (wrap2 TermSubst2.equal_params p0_2 p1_2)

      let alpha_equal (p0 : term) (p1 : term) =
         let p0_1, p0_2 = p0 in
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermSubst.alpha_equal" (wrap2 TermSubst1.alpha_equal p0_1 p1_1) (wrap2 TermSubst2.alpha_equal p0_2 p1_2)

      let alpha_equal_vars (p0 : term) (p1 : var list) (p2 : term) (p3 : var list) =
         let p0_1, p0_2 = p0 in
         let p2_1, p2_2 = p2 in
         merge merge_bool "TermSubst.alpha_equal_vars" (wrap4 TermSubst1.alpha_equal_vars p0_1 p1 p2_1 p3) (wrap4 TermSubst2.alpha_equal_vars p0_2 p1 p2_2 p3)

      let alpha_equal_fun (p0 : ( term -> 'a -> bool )) (p1 : term) (p2 : var list) (p3 : term) (p4 : 'a list) =
         let p0_1, p0_2 = split_taf p0 in
         let p1_1, p1_2 = p1 in
         let p3_1, p3_2 = p3 in
         merge merge_bool "TermSubst.alpha_equal_fun" (wrap5 TermSubst1.alpha_equal_fun p0_1 p1_1 p2 p3_1 p4) (wrap5 TermSubst2.alpha_equal_fun p0_2 p1_2 p2 p3_2 p4)

      let standardize (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_term "TermSubst.standardize" (wrap1 TermSubst1.standardize p0_1) (wrap1 TermSubst2.standardize p0_2)

      let is_closed_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_bool "TermSubst.is_closed_term" (wrap1 TermSubst1.is_closed_term p0_1) (wrap1 TermSubst2.is_closed_term p0_2)

      let is_var_free (p0 : var) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermSubst.is_var_free" (wrap2 TermSubst1.is_var_free p0 p1_1) (wrap2 TermSubst2.is_var_free p0 p1_2)

      let is_some_var_free (p0 : var list) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermSubst.is_some_var_free" (wrap2 TermSubst1.is_some_var_free p0 p1_1) (wrap2 TermSubst2.is_some_var_free p0 p1_2)

      let is_some_var_free_list (p0 : var list) (p1 : term list) =
         let p1_1, p1_2 = split p1 in
         merge merge_bool "TermSubst.is_some_var_free_list" (wrap2 TermSubst1.is_some_var_free_list p0 p1_1) (wrap2 TermSubst2.is_some_var_free_list p0 p1_2)

      let free_vars_list (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_vars "TermSubst.free_vars_list" (wrap1 TermSubst1.free_vars_list p0_1) (wrap1 TermSubst2.free_vars_list p0_2)

      let free_vars_set (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_ss "TermSubst.free_vars_set" (wrap1 TermSubst1.free_vars_set p0_1) (wrap1 TermSubst2.free_vars_set p0_2)

      let free_vars_terms (p0 : term list) =
         let p0_1, p0_2 = split p0 in
         merge merge_ss "TermSubst.free_vars_terms" (wrap1 TermSubst1.free_vars_terms p0_1) (wrap1 TermSubst2.free_vars_terms p0_2)

      let context_vars (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_vars "TermSubst.context_vars" (wrap1 TermSubst1.context_vars p0_1) (wrap1 TermSubst2.context_vars p0_2)

      let match_terms (p0 : term_subst) (p1 : term) (p2 : term) =
         let p0_1, p0_2 = split_term_subst p0 in
         let p1_1, p1_2 = p1 in
         let p2_1, p2_2 = p2 in
         merge merge_term_subst "TermSubst.match_terms" (wrap3 TermSubst1.match_terms p0_1 p1_1 p2_1) (wrap3 TermSubst2.match_terms p0_2 p1_2 p2_2)

   end

   module TermShape = struct
      include TermType

      let string_of_shape (s1, s2) =
         sprintf "Impl1 shape: %s; Impl2 shape: %s" (TermShape1.string_of_shape s1) (TermShape2.string_of_shape s2)

      (* The rest of this module is auto-generated by the util/gen_refiner_debug.pl script *)

      let shape_of_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_shape "TermShape.shape_of_term" (wrap1 TermShape1.shape_of_term p0_1) (wrap1 TermShape2.shape_of_term p0_2)

      let eq (p0 : shape) (p1 : shape) =
         let p0_1, p0_2 = p0 in
         let p1_1, p1_2 = p1 in
         merge merge_bool "TermShape.eq" (wrap2 TermShape1.eq p0_1 p1_1) (wrap2 TermShape2.eq p0_2 p1_2)

      let param_type (p0 : param) =
         let p0_1, p0_2 = p0 in
         merge merge_shape_param "TermShape.param_type" (wrap1 TermShape1.param_type p0_1) (wrap1 TermShape2.param_type p0_2)

      let opname_of_shape (p0 : shape) =
         let p0_1, p0_2 = p0 in
         merge merge_opname "TermShape.opname_of_shape" (wrap1 TermShape1.opname_of_shape p0_1) (wrap1 TermShape2.opname_of_shape p0_2)

      let sequent_shape =
         merge_shape "TermShape.sequent_shape" (TermShape1.sequent_shape) (TermShape2.sequent_shape)

      let var_shape =
         merge_shape "TermShape.var_shape" (TermShape1.var_shape) (TermShape2.var_shape)

      let print_shape (p0 : out_channel) (p1 : shape) =
         let p1_1, p1_2 = p1 in
         merge merge_unit "TermShape.print_shape" (wrap2 TermShape1.print_shape p0 p1_1) (wrap2 TermShape2.print_shape p0 p1_2)

      let pp_print_shape (p0 : formatter) (p1 : shape) =
         let p1_1, p1_2 = p1 in
         merge merge_unit "TermShape.pp_print_shape" (wrap2 TermShape1.pp_print_shape p0 p1_1) (wrap2 TermShape2.pp_print_shape p0 p1_2)

   end

   module TermMeta = struct
      module MetaTypes = TermType

      let unzip_mfunction mt =
         let mt1, mt2 = split_meta_term mt in
         let l1, t1 = TermMeta1.unzip_mfunction mt1 in
         let l2, t2 = TermMeta2.unzip_mfunction mt2 in
         let x = "TermMeta.unzip_mfunction" in
            (merge_list merge_sltot "meta_func" x l1 l2), (merge_term x t1 t2)

      (* The rest of this module is auto-generated by the util/gen_refiner_debug.pl script *)

      let context_vars (p0 : meta_term) =
         let p0_1, p0_2 = split_meta_term p0 in
         merge merge_vars "TermMeta.context_vars" (wrap1 TermMeta1.context_vars p0_1) (wrap1 TermMeta2.context_vars p0_2)

      let meta_alpha_equal (p0 : meta_term) (p1 : meta_term) =
         let p0_1, p0_2 = split_meta_term p0 in
         let p1_1, p1_2 = split_meta_term p1 in
         merge merge_bool "TermMeta.meta_alpha_equal" (wrap2 TermMeta1.meta_alpha_equal p0_1 p1_1) (wrap2 TermMeta2.meta_alpha_equal p0_2 p1_2)

      let unfold_mlabeled (p0 : string) (p1 : meta_term) =
         let p1_1, p1_2 = split_meta_term p1 in
         merge merge_term "TermMeta.unfold_mlabeled" (wrap2 TermMeta1.unfold_mlabeled p0 p1_1) (wrap2 TermMeta2.unfold_mlabeled p0 p1_2)

      let unzip_mimplies (p0 : meta_term) =
         let p0_1, p0_2 = split_meta_term p0 in
         let res1 = wrap1 TermMeta1.unzip_mimplies p0_1 in
         let res2 = wrap1 TermMeta2.unzip_mimplies p0_2 in
         let (res0_1, res1_1), (res0_2, res1_2) = merge merge_triv "TermMeta.unzip_mimplies" res1 res2 in
         (merge_terms "TermMeta.unzip_mimplies - 0" res0_1 res0_2),
         (merge_term "TermMeta.unzip_mimplies - 1" res1_1 res1_2)

      let zip_mimplies (p0 : term list) (p1 : term) =
         let p0_1, p0_2 = split p0 in
         let p1_1, p1_2 = p1 in
         merge merge_meta_term "TermMeta.zip_mimplies" (wrap2 TermMeta1.zip_mimplies p0_1 p1_1) (wrap2 TermMeta2.zip_mimplies p0_2 p1_2)

      let zip_mfunction (p0 : (term option * term) list) (p1 : term) =
         let p0_1, p0_2 = split_popl p0 in
         let p1_1, p1_2 = p1 in
         merge merge_meta_term "TermMeta.zip_mfunction" (wrap2 TermMeta1.zip_mfunction p0_1 p1_1) (wrap2 TermMeta2.zip_mfunction p0_2 p1_2)

      let strip_mfunction (p0 : meta_term) =
         let p0_1, p0_2 = split_meta_term p0 in
         merge merge_meta_term "TermMeta.strip_mfunction" (wrap1 TermMeta1.strip_mfunction p0_1) (wrap1 TermMeta2.strip_mfunction p0_2)

      let term_of_parsed_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_term "TermMeta.term_of_parsed_term" (wrap1 TermMeta1.term_of_parsed_term p0_1) (wrap1 TermMeta2.term_of_parsed_term p0_2)

      let term_of_parsed_term_with_vars (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_term "TermMeta.term_of_parsed_term_with_vars" (wrap1 TermMeta1.term_of_parsed_term_with_vars p0_1) (wrap1 TermMeta2.term_of_parsed_term_with_vars p0_2)

      let display_term_of_term (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_term "TermMeta.display_term_of_term" (wrap1 TermMeta1.display_term_of_term p0_1) (wrap1 TermMeta2.display_term_of_term p0_2)

      let create_term_parser (p0 : unit) (p1 : term) =
         let p1_1, p1_2 = p1 in
         merge merge_term "TermMeta.create_term_parser" (wrap2 TermMeta1.create_term_parser p0 p1_1) (wrap2 TermMeta2.create_term_parser p0 p1_2)

      let mterm_of_parsed_mterm (p0 : meta_term) =
         let p0_1, p0_2 = split_meta_term p0 in
         merge merge_meta_term "TermMeta.mterm_of_parsed_mterm" (wrap1 TermMeta1.mterm_of_parsed_mterm p0_1) (wrap1 TermMeta2.mterm_of_parsed_mterm p0_2)

      let mterms_of_parsed_mterms (p0 : meta_term) (p1 : term list) =
         let p0_1, p0_2 = split_meta_term p0 in
         let p1_1, p1_2 = split p1 in
         let res1 = wrap2 TermMeta1.mterms_of_parsed_mterms p0_1 p1_1 in
         let res2 = wrap2 TermMeta2.mterms_of_parsed_mterms p0_2 p1_2 in
         let (res0_1, res1_1, res2_1), (res0_2, res1_2, res2_2) = merge merge_triv "TermMeta.mterms_of_parsed_mterms" res1 res2 in
         (merge_meta_term "TermMeta.mterms_of_parsed_mterms - 0" res0_1 res0_2),
         (merge_terms "TermMeta.mterms_of_parsed_mterms - 1" res1_1 res1_2),
         (merge_ttf "TermMeta.mterms_of_parsed_mterms - 2" res2_1 res2_2)

      let context_subst_of_terms (p0 : term list) (p1 : var) (p2 : int) =
         let p0_1, p0_2 = split p0 in
         merge merge_var_lo "TermMeta.context_subst_of_terms" (wrap3 TermMeta1.context_subst_of_terms p0_1 p1 p2) (wrap3 TermMeta2.context_subst_of_terms p0_2 p1 p2)

      let encode_free_var (p0 : var) =
         merge merge_term "TermMeta.encode_free_var" (wrap1 TermMeta1.encode_free_var p0) (wrap1 TermMeta2.encode_free_var p0)

      let is_encoded_free_var (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_bool "TermMeta.is_encoded_free_var" (wrap1 TermMeta1.is_encoded_free_var p0_1) (wrap1 TermMeta2.is_encoded_free_var p0_2)

      let decode_free_var (p0 : term) =
         let p0_1, p0_2 = p0 in
         merge merge_var "TermMeta.decode_free_var" (wrap1 TermMeta1.decode_free_var p0_1) (wrap1 TermMeta2.decode_free_var p0_2)

   end

   module Rewrite = struct
      include TermType

      (* The rest of this module is auto-generated by the util/gen_refiner_debug.pl script *)

      let empty_args_spec =
         merge_rwspecs "Rewrite.empty_args_spec" (Rewrite1.empty_args_spec) (Rewrite2.empty_args_spec)

      let empty_args =
         merge_rwargs "Rewrite.empty_args" (Rewrite1.empty_args) (Rewrite2.empty_args)

      let compile_redex (p0 : strict) (p1 : rewrite_args_spec) (p2 : term) =
         let p2_1, p2_2 = p2 in
         merge merge_triv "Rewrite.compile_redex" (wrap3 Rewrite1.compile_redex p0 p1 p2_1) (wrap3 Rewrite2.compile_redex p0 p1 p2_2)

      let compile_redices (p0 : strict) (p1 : rewrite_args_spec) (p2 : term list) =
         let p2_1, p2_2 = split p2 in
         merge merge_triv "Rewrite.compile_redices" (wrap3 Rewrite1.compile_redices p0 p1 p2_1) (wrap3 Rewrite2.compile_redices p0 p1 p2_2)

      let extract_redex_types (p0 : rewrite_redex) =
         let p0_1, p0_2 = p0 in
         merge merge_rwtvl "Rewrite.extract_redex_types" (wrap1 Rewrite1.extract_redex_types p0_1) (wrap1 Rewrite2.extract_redex_types p0_2)

      let test_redex_applicability (p0 : rewrite_redex) (p1 : int array) (p2 : term) (p3 : term list) =
         let p0_1, p0_2 = p0 in
         let p2_1, p2_2 = p2 in
         let p3_1, p3_2 = split p3 in
         merge merge_unit "Rewrite.test_redex_applicability" (wrap4 Rewrite1.test_redex_applicability p0_1 p1 p2_1 p3_1) (wrap4 Rewrite2.test_redex_applicability p0_2 p1 p2_2 p3_2)

      let apply_redex (p0 : rewrite_redex) (p1 : int array) (p2 : term) (p3 : term list) =
         let p0_1, p0_2 = p0 in
         let p2_1, p2_2 = p2 in
         let p3_1, p3_2 = split p3 in
         merge merge_rewrite_items "Rewrite.apply_redex" (wrap4 Rewrite1.apply_redex p0_1 p1 p2_1 p3_1) (wrap4 Rewrite2.apply_redex p0_2 p1 p2_2 p3_2)

      let term_rewrite (p0 : strict) (p1 : rewrite_args_spec) (p2 : term list) (p3 : term list) =
         let p2_1, p2_2 = split p2 in
         let p3_1, p3_2 = split p3 in
         merge merge_triv "Rewrite.term_rewrite" (wrap4 Rewrite1.term_rewrite p0 p1 p2_1 p3_1) (wrap4 Rewrite2.term_rewrite p0 p1 p2_2 p3_2)

      let fun_rewrite (p0 : strict) (p1 : term) (p2 : (term -> term)) =
         let p1_1, p1_2 = p1 in
         let p2_1, p2_2 = split_ttf p2 in
         merge merge_triv "Rewrite.fun_rewrite" (wrap3 Rewrite1.fun_rewrite p0 p1_1 p2_1) (wrap3 Rewrite2.fun_rewrite p0 p1_2 p2_2)

      let apply_rewrite (p0 : rewrite_rule) (p1 : rewrite_args) (p2 : term) (p3 : term list) =
         let p0_1, p0_2 = p0 in
         let p2_1, p2_2 = p2 in
         let p3_1, p3_2 = split p3 in
         merge merge_terms "Rewrite.apply_rewrite" (wrap4 Rewrite1.apply_rewrite p0_1 p1 p2_1 p3_1) (wrap4 Rewrite2.apply_rewrite p0_2 p1 p2_2 p3_2)

      let relevant_rule (p0 : operator) (p1 : int list) (p2 : rewrite_rule) =
         let p0_1, p0_2 = p0 in
         let p2_1, p2_2 = p2 in
         merge merge_bool "Rewrite.relevant_rule" (wrap3 Rewrite1.relevant_rule p0_1 p1 p2_1) (wrap3 Rewrite2.relevant_rule p0_2 p1 p2_2)

      let rewrite_operator (p0 : rewrite_rule) =
         let p0_1, p0_2 = p0 in
         merge merge_op "Rewrite.rewrite_operator" (wrap1 Rewrite1.rewrite_operator p0_1) (wrap1 Rewrite2.rewrite_operator p0_2)

      let rewrite_eval_flags (p0 : rewrite_rule) =
         let p0_1, p0_2 = p0 in
         merge merge_ibl "Rewrite.rewrite_eval_flags" (wrap1 Rewrite1.rewrite_eval_flags p0_1) (wrap1 Rewrite2.rewrite_eval_flags p0_2)

      let print_rewrite_redex (p0 : out_channel) (p1 : rewrite_redex) =
         let p1_1, p1_2 = p1 in
         merge merge_unit "Rewrite.print_rewrite_redex" (wrap2 Rewrite1.print_rewrite_redex p0 p1_1) (wrap2 Rewrite2.print_rewrite_redex p0 p1_2)

      let print_rewrite_rule (p0 : out_channel) (p1 : rewrite_rule) =
         let p1_1, p1_2 = p1 in
         merge merge_unit "Rewrite.print_rewrite_rule" (wrap2 Rewrite1.print_rewrite_rule p0 p1_1) (wrap2 Rewrite2.print_rewrite_rule p0 p1_2)

   end

   module Refine = struct
      include TermType
   end

   module TermHash = struct
      include TermType
   end

   module TermNorm = struct
      include TermType
   end

   module TermHeaderConstr (FromTerm : TermModuleSig) = struct

   end


end

