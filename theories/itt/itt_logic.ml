(*
 * Regular logic connectives.
 *
 *)

include Itt_equal
include Itt_dprod
include Itt_union
include Itt_void
include Itt_unit
include Itt_soft

open Printf
open Debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineErrors
open Resource

open Itt_equal
open Itt_soft

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_logic%t" eflush

(* debug_string DebugLoad "Loading itt_logic..." *)

(************************************************************************
 * REWRITES								*
 ************************************************************************)

declare "prop"[@i:l]

declare "true"
declare "false"
declare "not"{'a}
declare "implies"{'a; 'b}
declare "and"{'a; 'b}
declare "or"{'a; 'b}
declare "all"{'A; x. 'B['x]}
declare "exists"{'A; x. 'B['x]}

primrw unfoldProp : "prop"[@i:l] <--> "univ"[@i:l]

primrw unfoldTrue : "true" <--> unit
primrw unfoldFalse : "false" <--> void
primrw unfoldNot : not{'a} <--> 'a -> void
primrw unfoldImplies : 'a => 'b <--> 'a -> 'b
primrw unfoldAnd : 'a & 'b <--> 'a * 'b
primrw unfoldOr : 'a or 'b <--> 'a + 'b
primrw unfoldAll : all x: 'A. 'B['x] <--> x:'A -> 'B['x]
primrw unfoldExists : exst x: 'A. 'B['x] <--> x:'A * 'B['x]

primrw reducePropTrue : "prop"["true":t] <--> "true"
primrw reducePropFalse : "prop"["false":t] <--> "false"

(************************************************************************
 * DISPLAY FORMS							*
 ************************************************************************)

prec prec_implies
prec prec_and
prec prec_or
prec prec_quant

prec prec_implies < prec_and
prec prec_implies < prec_or
prec prec_or < prec_and
prec prec_quant < prec_implies

dform true_df1 : mode[src] :: "true" = `"True"

dform false_df1 : mode[src] :: "false" = `"False"

dform not_df1 : mode[src] :: parens :: "prec"[prec_implies] :: "not"{'a} =
   `"not " slot[le]{'a}

dform implies_df1 : mode[src] :: parens :: "prec"[prec_implies] :: implies{'a; 'b} =
   slot[le]{'a} `" => " slot[lt]{'b}

dform and_df1 : mode[src] :: parens :: "prec"[prec_and] :: "and"{'a; 'b} =
   slot[le]{'a} `" /\\ " slot[lt]{'b}

dform or_df1 : mode[src] :: parens :: "prec"[prec_or] :: "or"{'a; 'b} =
   slot[le]{'a} `" \\/ " slot[lt]{'b}

dform all_df1 : mode[src] :: parens :: "prec"[prec_quant] :: "all"{'A; x. 'B} =
   `"all " slot{'x} `": " slot{'A}`"." slot{'B}

dform exists_df1 : mode[src] :: parens :: "prec"[prec_quant] :: "exists"{'A; x. 'B} =
  `"exists " slot{'x} `": " slot{'A} `"." slot{'B}

dform not_df2 : mode[prl] :: parens :: "prec"[prec_implies] :: "not"{'a} =
   Nuprl_font!tneg slot[le]{'a}

dform implies_df1 : mode[prl] :: parens :: "prec"[prec_implies] :: implies{'a; 'b} =
   slot[le]{'a} Nuprl_font!Rightarrow " " slot[lt]{'b}

dform and_df1 : mode[prl] :: parens :: "prec"[prec_and] :: "and"{'a; 'b} =
   slot[le]{'a} Nuprl_font!wedge " " slot[lt]{'b}

dform or_df2 : mode[prl] :: parens :: "prec"[prec_or] :: "or"{'a; 'b} =
   slot[le]{'a} Nuprl_font!vee " " slot[lt]{'b}

dform all_df2 : mode[prl] :: parens :: "prec"[prec_quant] :: "all"{'A; x. 'B} =
   pushm[3] Nuprl_font!forall slot{'x} `":" slot{'A} sbreak["",". "] slot{'B} popm

dform exists_df2 : mode[prl] :: parens :: "prec"[prec_quant] :: "exists"{'A; x. 'B} =
   pushm[3] Nuprl_font!"exists" slot{'x} `":" slot{'A} sbreak["",". "] slot{'B}

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let true_term = << "true" >>
let is_true_term t = t = true_term

let false_term = << "false" >>
let is_false_term t = t = false_term

let all_term = << all x: 'A. 'B['x] >>
let all_opname = opname_of_term all_term
let is_all_term = is_dep0_dep1_term all_opname
let dest_all = dest_dep0_dep1_term all_opname
let mk_all_term = mk_dep0_dep1_term all_opname

let exists_term = << exst x: 'A. 'B['x] >>
let exists_opname = opname_of_term exists_term
let is_exists_term = is_dep0_dep1_term exists_opname
let dest_exists = dest_dep0_dep1_term exists_opname
let mk_exists_term = mk_dep0_dep1_term exists_opname

let or_term = << 'A or 'B >>
let or_opname = opname_of_term or_term
let is_or_term = is_dep0_dep0_term or_opname
let dest_or = dest_dep0_dep0_term or_opname
let mk_or_term = mk_dep0_dep0_term or_opname

let and_term = << 'A and 'B >>
let and_opname = opname_of_term and_term
let is_and_term = is_dep0_dep0_term and_opname
let dest_and = dest_dep0_dep0_term and_opname
let mk_and_term = mk_dep0_dep0_term and_opname

let implies_term = << 'A => 'B >>
let implies_opname = opname_of_term implies_term
let is_implies_term = is_dep0_dep0_term implies_opname
let dest_implies = dest_dep0_dep0_term implies_opname
let mk_implies_term = mk_dep0_dep0_term implies_opname

let not_term = << 'A => 'B >>
let not_opname = opname_of_term not_term
let is_not_term = is_dep0_term not_opname
let dest_not = dest_dep0_term not_opname
let mk_not_term = mk_dep0_term not_opname

(*
 * D
 *)
let terms =
   [true_term,    unfoldTrue;
    false_term,   unfoldFalse;
    all_term,     unfoldAll;
    exists_term,  unfoldExists;
    or_term,      unfoldOr;
    and_term,     unfoldAnd;
    implies_term, unfoldImplies;
    not_term,     unfoldNot]

let add arg =
   let rec aux (dr, er) = function
      (t, rw)::tl ->
         aux (add_soft_abs dr er t rw) tl
    | [] ->
         (dr, er)
   in
      aux arg

let d_resource, eqcd_resource = add (d_resource, eqcd_resource) terms

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of true, false.
 *)
let inf_univ1 _ decl _ = decl, univ1_term

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (true_term, inf_univ1)
let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (false_term, inf_univ1)

(*
 * Type of quantifiers.
 *)
let inf_d dest f decl t =
   let v, a, b = dest t in
   let decl', a' = f decl a in
   let decl'', b' = f ((v, a)::decl') b in
   let le1, le2 =
      try dest_univ a', dest_univ b' with
         Term.TermMatch _ -> raise (RefineError ("typeinf", StringTermError ("can't infer type for", t)))
   in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2)

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (all_term, inf_d dest_all)
let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (exists_term, inf_d dest_exists)

(*
 * Type of propositions.
 *)
let inf_nd dest f decl t =
   let a, b = dest t in
   let decl', a' = f decl a in
   let decl'', b' = f decl' b in
   let le1, le2 =
      try dest_univ a', dest_univ b' with
         Term.TermMatch _ -> raise (RefineError ("typeinf", StringTermError ("can't infer type for", t)))
   in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2)

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (or_term, inf_nd dest_or)
let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (and_term, inf_nd dest_and)
let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (implies_term, inf_nd dest_implies)

(*
 * Type of all.
 *)
let inf_not f decl t =
   let a = dest_not t in
      f decl a

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (not_term, inf_not)

(*
 * $Log$
 * Revision 1.12  1998/07/01 04:37:43  nogin
 * Moved Refiner exceptions into a separate module RefineErrors
 *
 * Revision 1.11  1998/06/23 22:12:33  jyh
 * Improved rewriter speed with conversion tree and flist.
 *
 * Revision 1.10  1998/06/22 19:46:20  jyh
 * Rewriting in contexts.  This required a change in addressing,
 * and the body of the context is the _last_ subterm, not the first.
 *
 * Revision 1.9  1998/06/15 22:33:26  jyh
 * Added CZF.
 *
 * Revision 1.8  1998/06/12 13:47:33  jyh
 * D tactic works, added itt_bool.
 *
 * Revision 1.7  1998/06/01 13:56:01  jyh
 * Proving twice one is two.
 *
 * Revision 1.6  1998/05/28 13:47:46  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.5  1998/04/24 02:43:35  jyh
 * Added more extensive debugging capabilities.
 *
 * Revision 1.4  1998/04/22 22:44:56  jyh
 * *** empty log message ***
 *
 * Revision 1.3  1997/09/08 15:02:35  jyh
 * This version compiles Ensemble.
 *
 * Revision 1.2  1997/08/06 16:18:34  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:17  jyh
 * This is the initial checkin of Nuprl-Light.
 * I am porting the editor, so it is not included
 * in this checkin.
 *
 * Directories:
 *     refiner: logic engine
 *     filter: front end to the Ocaml compiler
 *     editor: Emacs proof editor
 *     util: utilities
 *     mk: Makefile templates
 *
 * Revision 1.4  1996/10/23 15:18:09  jyh
 * First working version of dT tactic.
 *
 * Revision 1.3  1996/09/25 22:52:13  jyh
 * Initial "tactical" commit.
 *
 * Revision 1.2  1996/09/02 19:37:30  jyh
 * Semi working package management.
 * All _univ version removed.
 *
 * Revision 1.1  1996/06/11 18:38:38  jyh
 * Demo version 0.0
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
