(*
 * A type of finite sets.
 * The sets are represented as lists of elements,
 * quotiented over all permutations.
 *
 * Each set must have a computable equality.
 * We provide an enumeration function.
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
 * Author: Jason Hickey
 * jyh@cs.cornell.edu
 *
 *)

include Itt_bool
include Itt_fun
include Itt_quotient
include Itt_list
include Itt_list2

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.RefineError
open Mp_resource
open Mp_debug
open Printf

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Var

open Base_dtactic
open Base_auto_tactic
open Typeinf

open Itt_equal
open Itt_bool
open Itt_rfun
open Itt_list
open Itt_struct
open Itt_logic
open Itt_quotient

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

define unfold_fcompare : fcompare{'eq; 'x; 'y} <--> ('eq 'x 'y)

define unfold_fmember : fmember{'eq; 'x; 's1} <-->
   list_ind{'s1; bfalse; h, t, g. bor{.fcompare{'eq; 'x; 'h}; 'g}}

define unfold_fsubseteq : fsubseteq{'eq; 's1; 's2} <-->
   list_ind{'s1; btrue; h, t, g. band{fmember{'eq; 'h; 's2}; 'g}}

define unfold_fequal : fequal{'eq; 's1; 's2} <-->
   band{fsubseteq{'eq; 's1; 's2}; fsubseteq{'eq; 's2; 's1}}

define unfold_fequalp : fequalp{'eq; 'T} <-->
   ((((('eq IN ('T -> 'T -> bool))
      & (all x: 'T. "assert"{.fcompare{'eq; 'x; 'x}}))
      & (all x: 'T. all y: 'T. ("assert"{fcompare{'eq; 'x; 'y}} => "assert"{fcompare{'eq; 'y; 'x}})))
      & (all x: 'T. all y: 'T. all z: 'T. ("assert"{fcompare{'eq; 'x; 'y}} => ("assert"{fcompare{'eq; 'y; 'z}} => "assert"{fcompare{'eq; 'x; 'z}})))))

define unfold_fset : fset{'eq; 'T} <--> (quot x, y : list{'T} // "assert"{fequal{'eq; 'x; 'y}})

define unfold_fempty : fempty <--> nil

define unfold_fsingleton : fsingleton{'x} <--> cons{'x; nil}

define unfold_funion : funion{'eq; 's1; 's2} <--> append{'s1; 's2}

define unfold_fisect : fisect{'eq; 's1; 's2} <-->
   list_ind{'s1; nil; h, t, g. ifthenelse{fmember{'eq; 'h; 's2}; cons{'h; 'g}; 'g}}

define unfold_fsub : fsub{'eq; 's1; 's2} <-->
   list_ind{'s1; nil; h, t, g. ifthenelse{fmember{'eq; 'h; 's2}; 'g; cons{'h; 'g}}}

define unfold_fisempty : fisempty{'s} <-->
   list_ind{'s; btrue; h, t, g. bfalse}

define unfold_fsquash : fsquash{'eq; 's} <-->
   list_ind{'s; nil; h, t, g. ifthenelse{fmember{'eq; 'h; 't}; 'g; cons{it; 'g}}}

define unfold_fball : fball{'s; x. 'b['x]} <-->
   list_ind{'s; btrue; x, t, g. band{'b['x]; 'g}}

define unfold_fbexists : fbexists{'s; x. 'b['x]} <-->
   list_ind{'s; bfalse; x, t, g. bor{'b['x]; 'g}}

define unfold_fall : fall{'eq; 'T; 's; x. 'b['x]} <-->
   (all x: { y: 'T | "assert"{fmember{'eq; 'y; 's}} }. 'b['x])

define unfold_fexists : fexists{'eq; 'T; 's; x. 'b['x]} <-->
   (exst x: { y: 'T | "assert"{fmember{'eq; 'y; 's}} }. 'b['x])

define unfold_feset : feset{'eq; 'T} <--> (quot x, y: 'T // "assert"{fcompare{'eq; 'x; 'y}})

define unfold_foflist : foflist{'l} <--> 'l

let fold_fequalp = makeFoldC << fequalp{'eq; 'T} >> unfold_fequalp
let fold_fset = makeFoldC << fset{'eq; 'T} >> unfold_fset
let fold_fempty = makeFoldC << fempty >> unfold_fempty
let fold_fsingleton = makeFoldC << fsingleton{'x} >> unfold_fsingleton
let fold_fisect = makeFoldC << fisect{'eq; 's1; 's2} >> unfold_fisect
let fold_fsub = makeFoldC << fsub{'eq; 's1; 's2} >> unfold_fsub
let fold_fmember = makeFoldC << fmember{'eq; 'x; 's1} >> unfold_fmember
let fold_fisempty = makeFoldC << fisempty{'s1} >> unfold_fisempty
let fold_fsubseteq = makeFoldC << fsubseteq{'e1; 's1; 's2} >> unfold_fsubseteq
let fold_fequal = makeFoldC << fequal{'eq; 's1; 's2} >> unfold_fequal
let fold_fsquash = makeFoldC << fsquash{'eq; 's1} >> unfold_fsquash
let fold_fball = makeFoldC << fball{'s; x. 'b['x]} >> unfold_fball
let fold_fbexists = makeFoldC << fbexists{'s; x. 'b['x]} >> unfold_fbexists
let fold_fall = makeFoldC << fall{'eq; 'T; 's; x. 'b['x]} >> unfold_fall
let fold_fexists = makeFoldC << fexists{'eq; 'T; 's; x. 'b['x]} >> unfold_fexists
let fold_feset = makeFoldC << feset{'eq; 'T} >> unfold_feset
let fold_foflist = makeFoldC << foflist{'l} >> unfold_foflist

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

let fempty_term = << fempty >>
let fsingleton_term = << fsingleton{'x} >>
let funion_term = << funion{'eq; 's1; 's2} >>
let fisect_term = << fisect{'eq; 's1; 's2} >>
let fsub_term = << fsub{'eq; 's1; 's2} >>
let fisempty_term = << fisempty{'s1} >>
let fmember_term = << fmember{'eq; 'x; 's1} >>
let fsubseteq_term = << fsubseteq{'eq; 's1; 's2} >>
let fequal_term = << fequal{'eq; 's1; 's2} >>
let fcompare_term = << fcompare{'eq; 'x1; 'x2} >>
let fequalp_term = << fequalp{'eq; 'T} >>
let fset_term = << fset{'eq; 'T} >>

let fempty_opname = opname_of_term fempty_term
let fsingleton_opname = opname_of_term fsingleton_term
let funion_opname = opname_of_term funion_term
let fisect_opname = opname_of_term fisect_term
let fsub_opname = opname_of_term fsub_term
let fisempty_opname = opname_of_term fisempty_term
let fmember_opname = opname_of_term fmember_term
let fsubseteq_opname = opname_of_term fsubseteq_term
let fequal_opname = opname_of_term fequal_term
let fcompare_opname = opname_of_term fcompare_term
let fequalp_opname = opname_of_term fequalp_term
let fset_opname = opname_of_term fset_term

let dest_fsingleton = dest_dep0_term fsingleton_opname
let dest_funion = dest_dep0_dep0_dep0_term funion_opname
let dest_fisect = dest_dep0_dep0_dep0_term fisect_opname
let dest_fsub = dest_dep0_dep0_dep0_term fsub_opname
let dest_fisempty = dest_dep0_term fisempty_opname
let dest_fmember = dest_dep0_dep0_dep0_term fmember_opname
let dest_fsubseteq = dest_dep0_dep0_dep0_term fsubseteq_opname
let dest_fequal = dest_dep0_dep0_dep0_term fequal_opname
let dest_fcompare = dest_dep0_dep0_dep0_term fcompare_opname
let dest_fequalp = dest_dep0_dep0_term fequalp_opname
let dest_fset = dest_dep0_dep0_term fset_opname

let is_fset_term = is_dep0_dep0_term fset_opname

let mk_fset_term = mk_dep0_dep0_term fset_opname

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_fsubseteq
prec prec_fmember
prec prec_funion
prec prec_fisect
prec prec_fexists
prec prec_fall
prec prec_feset
prec prec_foflist

(*
 * fall < fexists < funion < fisect < fmember
 *      fsubseteq <
 *)
prec prec_fsubseteq < prec_funion
prec prec_fall < prec_fexists
prec prec_fexists < prec_funion
prec prec_funion < prec_fisect
prec prec_fisect < prec_fmember
prec prec_fmember < prec_foflist
prec prec_foflist < prec_bimplies

dform fequalp_df : except_mode[src] :: fequalp{'eq; 'T} =
   `"fequalp(" slot{'eq} `"; " slot{'T} `")"

dform fcompare_df : parens :: "prec"[prec_fsubseteq] :: except_mode[src] :: fcompare{'eq; 'x1; 'x2} =
   slot{'x1} `" =" slot{'eq} space slot{'x2}

dform fsubseteq_df1 : parens :: "prec"[prec_fsubseteq] :: except_mode[src] :: fsubseteq{'eq; 'A; 'B} =
   slot{'A} `" " subseteq slot{'eq} space slot{'B}

dform fequal_df1 : parens :: "prec"[prec_fsubseteq] :: except_mode[src] :: fequal{'eq; 'A; 'B} =
   slot{'A} `" =" slot{'eq} space slot{'B}

dform fmember_df : parens :: "prec"[prec_fmember] :: except_mode[src] :: fmember{'eq; 'x; 's} =
   slot{'x} space Nuprl_font!member slot{'eq} space slot{'s}

dform fset_df : except_mode[src] :: fset{'eq; 'T} =
   `"FSet(" slot{'eq} `"; " slot{'T} `")"

dform fempty_df : except_mode[src] :: fempty =
   `"{}"

dform fsingleton_df : except_mode[src] :: fsingleton{'x} =
   `"{" slot{'x} `"}"

dform funion_df : parens :: "prec"[prec_funion] :: except_mode[src] :: funion{'eq; 's1; 's2} =
   slot{'s1} space cup slot{'eq} space slot{'s2}

dform fisect_df : parens :: "prec"[prec_fisect] :: except_mode[src] :: fisect{'eq; 's1; 's2} =
   slot["le"]{'s1} space cap slot{'eq} space slot{'s2}

dform fsub_df : parens :: "prec"[prec_fisect] :: except_mode[src] :: fsub{'eq; 's1; 's2} =
   slot["le"]{'s1} space `"-" slot{'eq} space slot{'s2}

dform fsquash_df : fsquash{'eq; 's1} =
   `"|" slot{'s1} `"|" slot{'eq}

dform fball_df : parens :: "prec"[prec_fall] :: except_mode[src] :: fball{'s; x. 'b} =
   pushm[3] Nuprl_font!"forall" subb slot{'x} space Nuprl_font!member space slot{'s} sbreak["",". "]
      slot{'b} popm

dform fbexists_df : parens :: "prec"[prec_fexists] :: except_mode[src] :: fbexists{'s; x. 'b} =
   pushm[3] Nuprl_font!"exists" subb slot{'x} space Nuprl_font!member space slot{'s} sbreak["",". "]
      slot{'b} popm

dform fall_df : parens :: "prec"[prec_fall] :: except_mode[src] :: fall{'eq; 'T; 's; x. 'b} =
   pushm[3] Nuprl_font!"forall" slot{'x} space Nuprl_font!member slot{'eq} space slot{'s}
   Nuprl_font!member space slot{'T} sbreak["",". "]
      slot{'b} popm

dform fexists_df : parens :: "prec"[prec_fexists] :: except_mode[src] :: fexists{'eq; 'T; 's; x. 'b} =
   pushm[3] Nuprl_font!"exists" slot{'x} space Nuprl_font!member slot{'eq} space slot{'s}
   Nuprl_font!member space slot{'T} sbreak["",". "]
      slot{'b} popm

dform feset_df : parens :: "prec"[prec_feset] :: except_mode[src] :: feset{'eq; 'T} =
   slot{'T} `"//" slot{'eq}

dform foflist_df : parens :: "prec"[prec_foflist] :: except_mode[src] :: foflist{'l} =
   `"of_list " slot{'l}

(************************************************************************
 * REDUCTIONS                                                           *
 ************************************************************************)

(*
 * Fmember on lists.
 *)
interactive_rw reduce_fmember_nil : fmember{'eq; 'x; nil} <--> bfalse

interactive_rw reduce_fmember_cons : fmember{'eq; 'x; cons{'h; 't}} <-->
   bor{.fcompare{'eq; 'x; 'h}; fmember{'eq; 'x; 't}}

let resource reduce +=
   [<< fmember{'eq; 'x; nil} >>, reduce_fmember_nil;
    << fmember{'eq; 'x; cons{'h; 't}} >>, reduce_fmember_cons]

(*
 * Singleton.
 *)
interactive_rw reduce_fmember_fsingleton : fmember{'eq; 'x; fsingleton{'y}} <-->
   bor{fcompare{'eq; 'x; 'y}; bfalse}

let resource reduce +=
   << fmember{'eq; 'x; fsingleton{'y}} >>, reduce_fmember_fsingleton

(*
 * Subset.
 *)
interactive_rw reduce_fsubseteq_nil : fsubseteq{'eq; nil; 's} <--> btrue

interactive_rw reduce_fsubseteq_cons :
   fsubseteq{'eq; cons{'h; 't}; 's} <-->
   band{fmember{'eq; 'h; 's}; fsubseteq{'eq; 't; 's}}

let resource reduce +=
   [<< fsubseteq{'eq; nil; 'l} >>, reduce_fsubseteq_nil;
    << fsubseteq{'eq; cons{'h; 't}; 'l} >>, reduce_fsubseteq_cons]

(*
 * Union.
 *)
interactive_rw reduce_funion_nil :
   funion{'eq; nil; 's} <--> 's

interactive_rw reduce_funion_cons :
   funion{'eq; cons{'h; 't}; 's} <--> cons{'h; funion{'eq; 't; 's}}

let resource reduce +=
   [<< funion{'eq; nil; 's} >>, reduce_funion_nil;
    << funion{'eq; cons{'h; 't}; 's} >>, reduce_funion_cons]

(*
 * Intersection.
 *)
interactive_rw reduce_fisect_nil :
   fisect{'eq; nil; 's2} <--> nil

interactive_rw reduce_fisect_cons :
   fisect{'eq; cons{'h; 't}; 's} <-->
      ifthenelse{fmember{'eq; 'h; 's}; cons{'h; fisect{'eq; 't; 's}}; fisect{'eq; 't; 's}}

let resource reduce +=
   [<< fisect{'eq; nil; 's} >>, reduce_fisect_nil;
    << fisect{'eq; cons{'h; 't}; 's} >>, reduce_fisect_cons]

(*
 * Set subtraction.
 *)
interactive_rw reduce_fsub_nil :
   fsub{'eq; nil; 's2} <--> nil

interactive_rw reduce_fsub_cons :
   fsub{'eq; cons{'h; 't}; 's} <-->
      ifthenelse{fmember{'eq; 'h; 's}; fsub{'eq; 't; 's}; cons{'h; fsub{'eq; 't; 's}}}

let resource reduce +=
   [<< fsub{'eq; nil; 's} >>, reduce_fsub_nil;
    << fsub{'eq; cons{'h; 't}; 's} >>, reduce_fsub_cons]

(*
 * Membership squashing.
 *)
interactive_rw reduce_fsquash_nil1 :
   fsquash{'eq; nil} <--> nil

interactive_rw reduce_fsquash_cons1 :
   fsquash{'eq; cons{'h; 't}} <-->
      ifthenelse{fmember{'eq; 'h; 't}; fsquash{'eq; 't}; cons{it; fsquash{'eq; 't}}}

let resource reduce +=
   [<< fsquash{'eq; nil} >>, reduce_fsquash_nil1;
    << fsquash{'eq; cons{'h; 't}} >>, reduce_fsquash_cons1]

(*
 * Universal quantification.
 *)
interactive_rw reduce_fball_nil :
   fball{nil; x. 'b['x]} <--> btrue

interactive_rw reduce_fball_cons :
   fball{cons{'h; 't}; x. 'b['x]} <-->
      band{'b['h]; fball{'t; x. 'b['x]}}

let resource reduce +=
   [<< fball{nil; x. 'b['x]} >>, reduce_fball_nil;
    << fball{cons{'h; 't}; x. 'b['x]} >>, reduce_fball_cons]

(*
 * Existential quantification.
 *)
interactive_rw reduce_fbexists_nil :
   fbexists{nil; x. 'b['x]} <--> bfalse

interactive_rw reduce_fbexists_cons :
   fbexists{cons{'h; 't}; x. 'b['x]} <-->
      bor{'b['h]; fbexists{'t; x. 'b['x]}}

let resource reduce +=
   [<< fbexists{nil; x. 'b['x]} >>, reduce_fbexists_nil;
    << fbexists{cons{'h; 't}; x. 'b['x]} >>, reduce_fbexists_cons]

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Fequalp gives more info.
 *)
let infer_fequalp subst (so, t) =
   let eq, t = dest_fequalp t in
      if is_var_term eq then
         (dest_var eq, mk_fun_term t (mk_fun_term t bool_term)) :: subst
      else
         subst

let resource typeinf_subst += (fequalp_term, infer_fequalp)

(*
 * Type of pair.
 *)
let inf_eq3 inf consts decls eqs opt_eqs defs t =
   let eq, s1, s2 = three_subterms t in
   let eqs', opt_eqs', defs', s1' = inf consts decls eqs opt_eqs defs s1 in
   let eqs'', opt_eqs'', defs'', s2' = inf consts decls eqs' opt_eqs' defs' s2 in
      eqs'', ((s1', s2') :: opt_eqs''), defs'', s1'

let map_singleton t =
   mk_cons_term (one_subterm t) nil_term

let resource typeinf += [
   << funion{'eq; 's1; 's2} >>, inf_eq3;
   << fisect{'eq; 's1; 's2} >>, inf_eq3;
   << fsub{'eq; 's1; 's2} >>, inf_eq3;
   << fisempty{'x} >>, Typeinf.infer_const bool_term;
   << fmember{'eq; 'x; 's1} >>, Typeinf.infer_const bool_term;
   << fsubseteq{'eq; 's1; 's2} >>, Typeinf.infer_const bool_term;
   << fequal{'eq; 's1; 's2} >>, Typeinf.infer_const bool_term;
   << fcompare{'eq; 'x1; 'x2} >>, Typeinf.infer_const bool_term;
   << fsingleton{'x} >>, Typeinf.infer_map map_singleton;
]

let dest_fset_type t =
   if !(load_debug "auto") then eprintf "\ttype is %a%t" print_term t eflush;
   if is_list_term t then
      dest_list t
   else if is_fset_term t then
      snd (dest_fset t)
   else (* if is_quotient_term t then *)
      let _, _, tlist, _ = dest_quotient t in
      dest_list tlist

let typeinf_fset_arg p t =
   let t =
      try get_with_arg p with
         RefineError _ ->
            if !(load_debug "auto") then eprintf "Type of: %a%t" print_term t eflush;
            dest_fset_type (infer_type p t)
   in
      [t]

let typeinf_plusone_arg p t =
   match get_with_args p with
      [u] ->
         [infer_type p t;u]
    | l -> l

let typeinf_plusone_fset_arg p t =
   match get_with_args p with
      [u] ->
         [dest_fset_type (infer_type p t);u]
    | l -> l

let intro_typeinf_fset t = IntroArgsOption (typeinf_fset_arg, Some t)
let elim_typeinf_fset t = ElimArgsOption (typeinf_fset_arg, Some t)
let intro_typeinf_plusone t = IntroArgsOption (typeinf_plusone_arg, Some t)
let elim_typeinf_plusone t = ElimArgsOption (typeinf_plusone_arg, Some t)
let elim_typeinf_plusone_fset t = ElimArgsOption (typeinf_plusone_fset_arg, Some t)

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

interactive fcompare_wf {| intro [intro_typeinf <<'x>>] |} 'H 'T :
   sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- 'x IN 'T } -->
   sequent [squash] { 'H >- 'y IN 'T } -->
   sequent ['ext] { 'H >- fcompare{'eq; 'x; 'y} IN bool }

interactive fcompare_ref {| intro [intro_typeinf <<'x>>] |} 'H 'T :
   sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- 'x IN 'T } -->
   sequent ['ext] { 'H >- "assert"{fcompare{'eq; 'x; 'x}} }

interactive fcompare_sym 'H 'T :
   sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- 'x IN 'T } -->
   sequent [squash] { 'H >- 'y IN 'T } -->
   sequent [squash] { 'H >- "assert"{fcompare{'eq; 'y; 'x}} } -->
   sequent ['ext] { 'H >- "assert"{fcompare{'eq; 'x; 'y}} }

interactive fcompare_trans 'H 'T 'z :
   sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- 'x IN 'T } -->
   sequent [squash] { 'H >- 'y IN 'T } -->
   sequent [squash] { 'H >- 'z IN 'T } -->
   sequent [squash] { 'H >- "assert"{fcompare{'eq; 'x; 'z}} } -->
   sequent [squash] { 'H >- "assert"{fcompare{'eq; 'z; 'y}} } -->
   sequent ['ext] { 'H >- "assert"{fcompare{'eq; 'x; 'y}} }

interactive fmember_wf1 {| intro [intro_typeinf << 'x >>] |} 'H 'T :
   sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- 'x IN 'T } -->
   sequent [squash] { 'H >- 's IN list{'T} } -->
   sequent ['ext] { 'H >- fmember{'eq; 'x; 's} IN bool }

interactive fmember_fun 'H 'T 'y :
   ["wf"] sequent [squash] { 'H >- 'x IN 'T } -->
   ["wf"] sequent [squash] { 'H >- 'y IN 'T } -->
   ["wf"] sequent [squash] { 'H >- 'l IN list{'T} } -->
   ["wf"] sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- "assert"{fcompare{'eq; 'x; 'y}} } -->
   sequent [squash] { 'H >- "assert"{fmember{'eq; 'y; 'l}} } -->
   sequent ['ext] { 'H >- "assert"{fmember{'eq; 'x; 'l}} }

interactive fsubseteq_wf1 {| intro [intro_typeinf_fset <<'s2>>] |} 'H 'T :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- 's1 IN list{'T} } -->
   sequent [squash] { 'H >- 's2 IN list{'T} } -->
   sequent ['ext] { 'H >- fsubseteq{'eq; 's1; 's2} IN bool }

interactive fsubseteq_elim2 {| elim [elim_typeinf_plusone_fset <<'l1>>] |} 'H 'J 'T 'a 'y :
   ["wf"] sequent [squash] { 'H; x: "assert"{fsubseteq{'eq; 'l1; 'l2}}; 'J['x] >- fequalp{'eq; 'T} } -->
   ["wf"] sequent [squash] { 'H; x: "assert"{fsubseteq{'eq; 'l1; 'l2}}; 'J['x] >- 'a IN 'T } -->
   ["wf"] sequent [squash] { 'H; x: "assert"{fsubseteq{'eq; 'l1; 'l2}}; 'J['x] >- 'l1 IN list{'T} } -->
   ["wf"] sequent [squash] { 'H; x: "assert"{fsubseteq{'eq; 'l1; 'l2}}; 'J['x] >- 'l2 IN list{'T} } -->
   sequent [squash] { 'H; x: "assert"{fsubseteq{'eq; 'l1; 'l2}}; 'J['x] >- "assert"{fmember{'eq; 'a; 'l1}} } -->
   sequent ['ext] { 'H; x: "assert"{fsubseteq{'eq; 'l1; 'l2}}; 'J['x]; y: "assert"{fmember{'eq; 'a; 'l2}} >- 'C['x] } -->
   sequent ['ext] { 'H; x: "assert"{fsubseteq{'eq; 'l1; 'l2}}; 'J['x] >- 'C['x] }

interactive fsubseteq_intro1 {| intro [AutoMustComplete; intro_typeinf_fset <<'s2>>] |} 'H 'T 'x 'y :
   ["wf"] sequent [squash] { 'H >- "type"{'T} } -->
   ["wf"] sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   ["wf"] sequent [squash] { 'H >- 's1 IN list{'T} } -->
   ["wf"] sequent [squash] { 'H >- 's2 IN list{'T} } -->
   sequent [squash] { 'H; x: 'T; y: "assert"{fmember{'eq; 'x; 's1}} >- "assert"{fmember{'eq; 'x; 's2}} } -->
   sequent ['ext] { 'H >- "assert"{fsubseteq{'eq; 's1; 's2}} }

interactive fsubseteq_cons2 {| intro [intro_typeinf <<'u>>] |} 'H 'T :
   ["wf"] sequent [squash] { 'H >- 'l1 IN list{'T} } -->
   ["wf"] sequent [squash] { 'H >- 'l2 IN list{'T} } -->
   ["wf"] sequent [squash] { 'H >- 'u IN 'T } -->
   ["wf"] sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- "assert"{fsubseteq{'eq; 'l1; 'l2}} } -->
   sequent ['ext] { 'H >- "assert"{fsubseteq{'eq; 'l1; cons{'u; 'l2}}} }

interactive fsubseteq_ref {| intro [intro_typeinf_fset <<'l>>] |} 'H 'T :
   ["wf"] sequent [squash] { 'H >- "type"{'T} } -->
   ["wf"] sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   ["wf"] sequent [squash] { 'H >- 'l IN list{'T} } -->
   sequent ['ext] { 'H >- "assert"{fsubseteq{'eq; 'l; 'l}} }

interactive fsubseteq_trans 'H 'T 'l2 :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- 'l1 IN list{'T} } -->
   sequent [squash] { 'H >- 'l2 IN list{'T} } -->
   sequent [squash] { 'H >- 'l3 IN list{'T} } -->
   sequent [squash] { 'H >- "assert"{fsubseteq{'eq; 'l1; 'l2}} } -->
   sequent [squash] { 'H >- "assert"{fsubseteq{'eq; 'l2; 'l3}} } -->
   sequent ['ext] { 'H >- "assert"{fsubseteq{'eq; 'l1; 'l3}} }

interactive fequal_wf1 {| intro [intro_typeinf_fset <<'s1>>] |} 'H 'T :
   [wf] sequent [squash] { 'H >- "type"{'T} } -->
   [wf] sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H >- 's1 IN list{'T} } -->
   [wf] sequent [squash] { 'H >- 's2 IN list{'T} } -->
   sequent ['ext] { 'H >- fequal{'eq; 's1; 's2} IN bool }

interactive fequal_elim1 {| elim [elim_typeinf_plusone_fset <<'s1>>] |} 'H 'J 'T 'a 'y :
   [wf] sequent [squash] { 'H; x: "assert"{fequal{'eq; 's1; 's2}}; 'J['x] >- 'a IN 'T } -->
   [wf] sequent [squash] { 'H; x: "assert"{fequal{'eq; 's1; 's2}}; 'J['x] >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H; x: "assert"{fequal{'eq; 's1; 's2}}; 'J['x] >- 's1 IN list{'T} } -->
   [wf] sequent [squash] { 'H; x: "assert"{fequal{'eq; 's1; 's2}}; 'J['x] >- 's2 IN list{'T} } -->
   sequent [squash] { 'H; x: "assert"{fequal{'eq; 's1; 's2}}; 'J['x] >- "assert"{fmember{'eq; 'a; 's1}} } -->
   sequent ['ext] { 'H; x: "assert"{fequal{'eq; 's1; 's2}}; 'J['x]; y: "assert"{fmember{'eq; 'a; 's2}} >- 'C['x] } -->
   sequent ['ext] { 'H; x: "assert"{fequal{'eq; 's1; 's2}}; 'J['x] >- 'C['x] }

interactive fequal_intro1 {| intro [intro_typeinf_fset <<'s1>>] |} 'H 'T 'x 'y :
   [wf] sequent [squash] { 'H >- "type"{'T} } -->
   [wf] sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H >- 's1 IN list{'T} } -->
   [wf] sequent [squash] { 'H >- 's2 IN list{'T} } -->
   sequent [squash] { 'H; x: 'T; y: "assert"{fmember{'eq; 'x; 's1}} >- "assert"{fmember{'eq; 'x; 's2}} } -->
   sequent [squash] { 'H; x: 'T; y: "assert"{fmember{'eq; 'x; 's2}} >- "assert"{fmember{'eq; 'x; 's1}} } -->
   sequent ['ext] { 'H >- "assert"{fequal{'eq; 's1; 's2}} }

interactive fset_type {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'T} } -->
   [wf] sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent ['ext] { 'H >- "type"{fset{'eq; 'T}} }

interactive fset_list {| intro [AutoMustComplete] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'T} } -->
   [wf] sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H >- 'x IN list{'T} } -->
   sequent ['ext] { 'H >- 'x IN fset{'eq; 'T} }

(*
 * Membership.
 *)
interactive fmember_wf2 {| intro [intro_typeinf <<'x>>] |} 'H 'T :
   sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- 'x IN 'T } -->
   sequent [squash] { 'H >- 's IN fset{'eq; 'T} } -->
   sequent ['ext] { 'H >- fmember{'eq; 'x; 's} IN bool }

(*
 * Subset.
 *)
interactive fsubseteq_wf2 {| intro [intro_typeinf_fset <<'s2>>] |} 'H 'T :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- 's1 IN fset{'eq; 'T} } -->
   sequent [squash] { 'H >- 's2 IN fset{'eq; 'T} } -->
   sequent ['ext] { 'H >- fsubseteq{'eq; 's1; 's2} IN bool }

(*
 * Equality.
 *)
interactive fequal_wf2 {| intro [intro_typeinf_fset <<'s1>>] |} 'H 'T :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- 's1 IN fset{'eq; 'T} } -->
   sequent [squash] { 'H >- 's2 IN fset{'eq; 'T} } -->
   sequent ['ext] { 'H >- fequal{'eq; 's1; 's2} IN bool }

interactive fequal_intro2 {| intro [intro_typeinf_fset <<'s1>>] |} 'H 'T 'x 'y :
   [wf] sequent [squash] { 'H >- "type"{'T} } -->
   [wf] sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H >- 's1 IN fset{'eq; 'T} } -->
   [wf] sequent [squash] { 'H >- 's2 IN fset{'eq; 'T} } -->
   sequent [squash] { 'H; x: 'T; y: "assert"{fmember{'eq; 'x; 's1}} >- "assert"{fmember{'eq; 'x; 's2}} } -->
   sequent [squash] { 'H; x: 'T; y: "assert"{fmember{'eq; 'x; 's2}} >- "assert"{fmember{'eq; 'x; 's1}} } -->
   sequent ['ext] { 'H >- "assert"{fequal{'eq; 's1; 's2}} }

interactive fempty_wf {| intro [] |} 'H :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent [squash] { 'H >- "type"{fset{'eq; 'T}} } -->
   sequent ['ext] { 'H >- fempty IN fset{'eq; 'T} }

interactive fsingleton_wf {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'x IN 'T } -->
   [wf] sequent [squash] { 'H >- "type"{fset{'eq; 'T}} } -->
   sequent ['ext] { 'H >- fsingleton{'x} IN fset{'eq; 'T} }

(*
 * Union.
 *)
interactive funion_wf1 {| intro [] |} 'H :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- 's1 IN list{'T} } -->
   sequent [squash] { 'H >- 's2 IN list{'T} } -->
   sequent ['ext] { 'H >- funion{'eq; 's1; 's2} IN list{'T} }

interactive funion_member_intro_left2 {| intro [SelectOption 1; intro_typeinf <<'x>>] |} 'H 'T :
   [wf] sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H >- 'x IN 'T } -->
   [wf] sequent [squash] { 'H >- 's1 IN list{'T} } -->
   [wf] sequent [squash] { 'H >- 's2 IN list{'T} } -->
   sequent [squash] { 'H >- "assert"{fmember{'eq; 'x; 's1}} } -->
   sequent ['ext] { 'H >- "assert"{fmember{'eq; 'x; funion{'eq; 's1; 's2}}} }

interactive funion_member_intro_right2 {| intro [SelectOption 2; intro_typeinf <<'x>>] |} 'H 'T :
   [wf] sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H >- 'x IN 'T } -->
   [wf] sequent [squash] { 'H >- 's1 IN list{'T} } -->
   [wf] sequent [squash] { 'H >- 's2 IN list{'T} } -->
   sequent [squash] { 'H >- "assert"{fmember{'eq; 'x; 's2}} } -->
   sequent ['ext] { 'H >- "assert"{fmember{'eq; 'x; funion{'eq; 's1; 's2}}} }

interactive funion_member_elim2 {| elim [elim_typeinf <<'x>>] |} 'H 'J 'T :
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; funion{'eq; 's1; 's2}}}; 'J[it] >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; funion{'eq; 's1; 's2}}}; 'J[it] >- 'x IN 'T } -->
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; funion{'eq; 's1; 's2}}}; 'J[it] >- 's1 IN list{'T} } -->
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; funion{'eq; 's1; 's2}}}; 'J[it] >- 's2 IN list{'T} } -->
   sequent ['ext] { 'H; z: "assert"{fmember{'eq; 'x; 's1}}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; z: "assert"{fmember{'eq; 'x; 's2}}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; z: "assert"{fmember{'eq; 'x; funion{'eq; 's1; 's2}}}; 'J['z] >- 'C['z] }

interactive funion_wf2 {| intro [] |} 'H :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- 's1 IN fset{'eq; 'T} } -->
   sequent [squash] { 'H >- 's2 IN fset{'eq; 'T} } -->
   sequent ['ext] { 'H >- funion{'eq; 's1; 's2} IN fset{'eq; 'T} }

(*
 * Intersection.
 *)
interactive fisect_wf1 {| intro [] |} 'H :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- 's1 IN list{'T} } -->
   sequent [squash] { 'H >- 's2 IN list{'T} } -->
   sequent ['ext] { 'H >- fisect{'eq; 's1; 's2} IN list{'T} }

interactive fisect_member_intro {| intro [intro_typeinf <<'x>>] |} 'H 'T :
   [wf] sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H >- 'x IN 'T } -->
   [wf] sequent [squash] { 'H >- 's1 IN list{'T} } -->
   [wf] sequent [squash] { 'H >- 's2 IN list{'T} } -->
   sequent [squash] { 'H >- "assert"{fmember{'eq; 'x; 's1}} } -->
   sequent [squash] { 'H >- "assert"{fmember{'eq; 'x; 's2}} } -->
   sequent ['ext] { 'H >- "assert"{fmember{'eq; 'x; fisect{'eq; 's1; 's2}}} }

interactive fisect_member_elim2 {| elim [elim_typeinf <<'x>>] |} 'H 'J 'T 'u 'v :
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; fisect{'eq; 's1; 's2}}}; 'J['z] >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; fisect{'eq; 's1; 's2}}}; 'J['z] >- 'x IN 'T } -->
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; fisect{'eq; 's1; 's2}}}; 'J['z] >- 's1 IN list{'T} } -->
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; fisect{'eq; 's1; 's2}}}; 'J['z] >- 's2 IN list{'T} } -->
   sequent ['ext] { 'H; u: "assert"{fmember{'eq; 'x; 's1}}; v: "assert"{fmember{'eq; 'x; 's2}}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; z: "assert"{fmember{'eq; 'x; fisect{'eq; 's1; 's2}}}; 'J['z] >- 'C['z] }

interactive fisect_wf2 {| intro [] |} 'H :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- 's1 IN fset{'eq; 'T} } -->
   sequent [squash] { 'H >- 's2 IN fset{'eq; 'T} } -->
   sequent ['ext] { 'H >- fisect{'eq; 's1; 's2} IN fset{'eq; 'T} }

(*
 * Subtraction.
 *)
interactive fsub_wf1 {| intro [] |} 'H :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- 's1 IN list{'T} } -->
   sequent [squash] { 'H >- 's2 IN list{'T} } -->
   sequent ['ext] { 'H >- fsub{'eq; 's1; 's2} IN list{'T} }

interactive fsub_member_intro {| intro [intro_typeinf <<'x>>] |} 'H 'T :
   [wf] sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H >- 'x IN 'T } -->
   [wf] sequent [squash] { 'H >- 's1 IN list{'T} } -->
   [wf] sequent [squash] { 'H >- 's2 IN list{'T} } -->
   sequent [squash] { 'H >- "assert"{fmember{'eq; 'x; 's1}} } -->
   sequent [squash] { 'H >- "assert"{bnot{fmember{'eq; 'x; 's2}}} } -->
   sequent ['ext] { 'H >- "assert"{fmember{'eq; 'x; fsub{'eq; 's1; 's2}}} }

interactive fsub_member_elim2 {| elim [elim_typeinf <<'x>>] |} 'H 'J 'T 'u 'v:
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; fsub{'eq; 's1; 's2}}}; 'J['z] >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; fsub{'eq; 's1; 's2}}}; 'J['z] >- 'x IN 'T } -->
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; fsub{'eq; 's1; 's2}}}; 'J['z] >- 's1 IN list{'T} } -->
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; fsub{'eq; 's1; 's2}}}; 'J['z] >- 's2 IN list{'T} } -->
   sequent ['ext] { 'H; u: "assert"{fmember{'eq; 'x; 's1}}; v: "assert"{bnot{fmember{'eq; 'x; 's2}}}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; z: "assert"{fmember{'eq; 'x; fsub{'eq; 's1; 's2}}}; 'J['z] >- 'C['z] }

interactive fsub_wf2 {| intro [] |} 'H :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- 's1 IN fset{'eq; 'T} } -->
   sequent [squash] { 'H >- 's2 IN fset{'eq; 'T} } -->
   sequent ['ext] { 'H >- fsub{'eq; 's1; 's2} IN fset{'eq; 'T} }

(*
 * Singleton.
 *)
interactive fsingleton_wf1 {| intro [] |} 'H :
   sequent [squash] { 'H >- 'x IN 'T } -->
   sequent ['ext] { 'H >- fsingleton{'x} IN list{'T} }

interactive fsingleton_member_intro {| intro [intro_typeinf <<'x>>] |} 'H 'T :
   [wf] sequent [squash] { 'H >- "type"{'T} } -->
   [wf] sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- "assert"{fcompare{'eq; 'x; 'y}} } -->
   sequent ['ext] { 'H >- "assert"{fmember{'eq; 'x; fsingleton{'y}}} }

interactive fsingleton_member_elim {| elim [elim_typeinf <<'y>>] |} 'H 'J 'T :
   [wf] sequent [squash] { 'H; x: "assert"{fmember{'eq; 'y; fsingleton{'z}}}; 'J['x] >- "type"{'T} } -->
   [wf] sequent [squash] { 'H; x: "assert"{fmember{'eq; 'y; fsingleton{'z}}}; 'J['x] >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H; x: "assert"{fmember{'eq; 'y; fsingleton{'z}}}; 'J['x] >- 'y IN 'T } -->
   [wf] sequent [squash] { 'H; x: "assert"{fmember{'eq; 'y; fsingleton{'z}}}; 'J['x] >- 'z IN 'T } -->
   sequent ['ext] { 'H; x: "assert"{fcompare{'eq; 'y; 'z}}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: "assert"{fmember{'eq; 'y; fsingleton{'z}}}; 'J['x] >- 'C['x] }

interactive fsingleton_wf2 {| intro [] |} 'H :
   sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- 'x IN 'T } -->
   sequent ['ext] { 'H >- fsingleton{'x} IN fset{'eq; 'T} }

(*
 * Empty.
 *)
interactive fempty_wf1 {| intro [] |} 'H :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent ['ext] { 'H >- fempty IN list{'T} }

interactive fempty_member_elim {| elim [] |} 'H 'J :
   sequent ['ext] { 'H; x: "assert"{fmember{'eq; 'y; fempty}}; 'J['x] >- 'C['x] }

interactive fempty_wf2 {| intro [] |} 'H :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent ['ext] { 'H >- fempty IN fset{'eq; 'T} }

interactive fequal_assert_elim2 {| elim [elim_typeinf_fset <<'s1>>] |} 'H 'J 'T :
   [wf] sequent [squash] { 'H; x: "assert"{fequal{'eq; 's1; 's2}}; 'J['x] >- "type"{'T} } -->
   [wf] sequent [squash] { 'H; x: "assert"{fequal{'eq; 's1; 's2}}; 'J['x] >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H; x: "assert"{fequal{'eq; 's1; 's2}}; 'J['x] >- 's1 IN fset{'eq; 'T} } -->
   [wf] sequent [squash] { 'H; x: "assert"{fequal{'eq; 's1; 's2}}; 'J['x] >- 's2 IN fset{'eq; 'T} } -->
   sequent ['ext] { 'H; x: 's1 = 's2 in fset{'eq; 'T}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: "assert"{fequal{'eq; 's1; 's2}}; 'J['x] >- 'C['x] }

interactive fequal_intro3 {| intro [intro_typeinf_fset <<'s1>>] |} 'H 'T :
   [wf] sequent [squash] { 'H >- "type"{'T} } -->
   [wf] sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- 's1 = 's2 in fset{'eq; 'T} } -->
   sequent ['ext] { 'H >- "assert"{fequal{'eq; 's1; 's2}} }

(*
 * Induction principle.
 *)
interactive fsquash_wf1 {| intro [intro_typeinf_fset <<'s>>] |} 'H 'T :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- 's IN list{'T} } -->
   sequent ['ext] { 'H >- fsquash{'eq; 's} IN list{unit} }

interactive fsub_null {| intro [intro_typeinf <<'u>>] |} 'H 'T :
   [wf] sequent [squash] { 'H >- "type"{'T} } -->
   [wf] sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H >- 's IN list{'T} } -->
   [wf] sequent [squash] { 'H >- 'u IN 'T } -->
   sequent [squash] { 'H >- "assert"{bnot{fmember{'eq; 'u; 's}}} } -->
   sequent ['ext] { 'H >- 's = fsub{'eq; 's; fsingleton{'u}} in list{'T} }

interactive fsquash_fsub1 {| intro [intro_typeinf <<'u>>] |} 'H 'T :
   [wf] sequent [squash] { 'H >- "type"{'T} } -->
   [wf] sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H >- 's IN list{'T} } -->
   [wf] sequent [squash] { 'H >- 'u IN 'T } -->
   sequent [squash] { 'H >- "assert"{fmember{'eq; 'u; 's}} } -->
   sequent ['ext] { 'H >- fsquash{'eq; 's} = cons{it; fsquash{'eq; fsub{'eq; 's; fsingleton{'u}}}} in list{unit} }

interactive fsquash_wf2 {| intro [intro_typeinf_fset <<'s>>] |} 'H 'T :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- 's IN fset{'eq; 'T} } -->
   sequent ['ext] { 'H >- fsquash{'eq; 's} IN list{unit} }

interactive fset_elim1 {| elim [] |} 'H 'J 'u 'z 'w :
   [wf] sequent [squash] { 'H; x: fset{'eq; 'T}; 'J['x] >- "type"{'T} } -->
   [wf] sequent [squash] { 'H; x: fset{'eq; 'T}; 'J['x] >- fequalp{'eq; 'T} } -->
   sequent ['ext] { 'H; x: fset{'eq; 'T}; 'J['x];
      u: fset{'eq; 'T};
      w: all z: 'T. ("assert"{fmember{'eq; 'z; 'u}} => 'C[fsub{'eq; 'u; fsingleton{'z}}]) >-
      'C['u] } -->
   sequent ['ext] { 'H; x: fset{'eq; 'T}; 'J['x] >- 'C['x] }

(*
 * Quotiented type.
 *)
interactive feset_wf {| intro [] |} 'H :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent ['ext] { 'H >- "type"{feset{'eq; 'T}} }

(*
 * Boolean universal.
 *)
interactive fball_wf1 {| intro [intro_typeinf <<'s>>] |} 'H fset{'eq; 'T} :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- 's IN list{'T} } -->
   sequent [squash] { 'H; x: 'T >- 'b['x] IN bool } -->
   sequent ['ext] { 'H >- fball{'s; x. 'b['x]} IN bool }

interactive fball_assert_intro1 {| intro [intro_typeinf <<'s>>] |} 'H fset{'eq; 'T} 'w :
   [wf] sequent [squash] { 'H >- "type"{'T} } -->
   [wf] sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H >- 's IN list{'T} } -->
   [wf] sequent [squash] { 'H; z: 'T >- 'b['z] IN bool } -->
   sequent [squash] { 'H; x: 'T; w: "assert"{fmember{'eq; 'x; 's}} >- "assert"{'b['x]} } -->
   sequent ['ext] { 'H >- "assert"{fball{'s; x. 'b['x]}} }

interactive fball_assert_elim1 {| elim [elim_typeinf_plusone <<'s>>] |} 'H 'J fset{'eq; 'T} 'a 'y 'u 'v 'w :
   [wf] sequent [squash] { 'H; x: "assert"{fball{'s; x. 'b['x]}}; 'J['x] >- "type"{'T} } -->
   [wf] sequent [squash] { 'H; x: "assert"{fball{'s; x. 'b['x]}}; 'J['x] >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H; x: "assert"{fball{'s; x. 'b['x]}}; 'J['x] >- 's IN list{'T} } -->
   [wf] sequent [squash] { 'H; x: "assert"{fball{'s; x. 'b['x]}}; 'J['x]; u: 'T; v: 'T; w: "assert"{fcompare{'eq; 'u; 'v}} >- 'b['u] = 'b['v] in bool } -->
   [wf] sequent [squash] { 'H; x: "assert"{fball{'s; x. 'b['x]}}; 'J['x] >- 'a IN 'T } -->
   [wf] sequent [squash] { 'H; x: "assert"{fball{'s; x. 'b['x]}}; 'J['x] >- "assert"{fmember{'eq; 'a; 's}} } -->
   sequent ['ext] { 'H; x: "assert"{fball{'s; x. 'b['x]}}; 'J['x]; y: "assert"{'b['a]} >- 'C['x] } -->
   sequent ['ext] { 'H; x: "assert"{fball{'s; x. 'b['x]}}; 'J['x] >- 'C['x] }

interactive fball_wf2 {| intro [intro_typeinf <<'s>>] |} 'H fset{'eq; 'T} 'u 'v 'w :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- 's IN fset{'eq; 'T} } -->
   sequent [squash] { 'H; u: 'T; v: 'T; w: "assert"{fcompare{'eq; 'u; 'v}} >- 'b['u] = 'b['v] in bool } -->
   sequent ['ext] { 'H >- fball{'s; x. 'b['x]} IN bool }

interactive fball_assert_intro2 {| intro [intro_typeinf <<'s>>] |}'H fset{'eq; 'T} 'w :
   [wf] sequent [squash] { 'H >- "type"{'T} } -->
   [wf] sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H >- 's IN fset{'eq; 'T} } -->
   [wf] sequent [squash] { 'H; u: 'T; v: 'T; w: "assert"{fcompare{'eq; 'u; 'v}} >- 'b['u] = 'b['v] in bool} -->
   sequent [squash] { 'H; x: 'T; w: "assert"{fmember{'eq; 'x; 's}} >- "assert"{'b['x]} } -->
   sequent ['ext] { 'H >- "assert"{fball{'s; x. 'b['x]}} }

interactive fball_assert_elim2 {| elim [elim_typeinf_plusone <<'s>>] |} 'H 'J fset{'eq; 'T} 'a 'y 'u 'v 'w :
   [wf] sequent [squash] { 'H; x: "assert"{fball{'s; x. 'b['x]}}; 'J['x] >- "type"{'T} } -->
   [wf] sequent [squash] { 'H; x: "assert"{fball{'s; x. 'b['x]}}; 'J['x] >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H; x: "assert"{fball{'s; x. 'b['x]}}; 'J['x] >- 's IN fset{'eq; 'T} } -->
   [wf] sequent [squash] { 'H; x: "assert"{fball{'s; x. 'b['x]}}; 'J['x]; u: 'T; v: 'T; w: "assert"{fcompare{'eq; 'u; 'v}} >- 'b['u] = 'b['v] in bool } -->
   [wf] sequent [squash] { 'H; x: "assert"{fball{'s; x. 'b['x]}}; 'J['x] >- 'a IN 'T } -->
   [wf] sequent [squash] { 'H; x: "assert"{fball{'s; x. 'b['x]}}; 'J['x] >- "assert"{fmember{'eq; 'a; 's}} } -->
   sequent ['ext] { 'H; x: "assert"{fball{'s; x. 'b['x]}}; 'J['x]; y: "assert"{'b['a]} >- 'C['x] } -->
   sequent ['ext] { 'H; x: "assert"{fball{'s; x. 'b['x]}}; 'J['x] >- 'C['x] }

(*
 * Boolean existential.
 *)
interactive fbexists_wf1 {| intro [intro_typeinf <<'s>>] |} 'H fset{'eq; 'T} 'z :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- 's IN list{'T} } -->
   sequent [squash] { 'H; z: 'T >- 'b['z] IN bool } -->
   sequent ['ext] { 'H >- fbexists{'s; x. 'b['x]} IN bool }

interactive fbexists_assert_intro1 {| intro [intro_typeinf_plusone <<'s>>] |} 'H fset{'eq; 'T} 'a 'u 'v 'w :
   [wf] sequent [squash] { 'H >- "type"{'T} } -->
   [wf] sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H >- 's IN list{'T} } -->
   [wf] sequent [squash] { 'H >- 'a IN 'T } -->
   [wf] sequent [squash] { 'H; u: 'T; v: 'T; w: "assert"{fcompare{'eq; 'u; 'v}} >- 'b['u] = 'b['v] in bool } -->
   [wf] sequent [squash] { 'H >- "assert"{fmember{'eq; 'a; 's}} } -->
   sequent [squash] { 'H >- "assert"{'b['a]} } -->
   sequent ['ext] { 'H >- "assert"{fbexists{'s; x. 'b['x]}} }

interactive fbexists_assert_elim1 {| elim [elim_typeinf <<'s>>] |} 'H 'J fset{'eq; 'T} 'u 'v 'w :
   [wf] sequent [squash] { 'H; x: "assert"{fbexists{'s; x. 'b['x]}}; 'J['x] >- "type"{'T} } -->
   [wf] sequent [squash] { 'H; x: "assert"{fbexists{'s; x. 'b['x]}}; 'J['x] >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H; x: "assert"{fbexists{'s; x. 'b['x]}}; 'J['x] >- 's IN list{'T} } -->
   [wf] sequent [squash] { 'H; x: "assert"{fbexists{'s; x. 'b['x]}}; 'J['x]; u: 'T >- 'b['u] IN bool } -->
   sequent ['ext] { 'H; u: 'T; v: "assert"{fmember{'eq; 'u; 's}}; w: "assert"{'b['u]}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: "assert"{fbexists{'s; x. 'b['x]}}; 'J['x] >- 'C['x] }

interactive fbexists_wf2 {| intro [intro_typeinf <<'s>>] |} 'H fset{'eq; 'T} 'u 'v 'w :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- 's IN fset{'eq; 'T} } -->
   sequent [squash] { 'H; u: 'T; v: 'T; w: "assert"{fcompare{'eq; 'u; 'v}} >- 'b['u] = 'b['v] in bool } -->
   sequent ['ext] { 'H >- fbexists{'s; x. 'b['x]} IN bool }

interactive fbexists_assert_intro2 {| intro [intro_typeinf_plusone <<'s>>] |} 'H fset{'eq; 'T} 'a 'u 'v 'w :
   [wf] sequent [squash] { 'H >- "type"{'T} } -->
   [wf] sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H >- 's IN fset{'eq; 'T} } -->
   [wf] sequent [squash] { 'H >- 'a IN 'T } -->
   [wf] sequent [squash] { 'H; u: 'T; v: 'T; w: "assert"{fcompare{'eq; 'u; 'v}} >- 'b['u] = 'b['v] in bool } -->
   [wf] sequent [squash] { 'H >- "assert"{fmember{'eq; 'a; 's}} } -->
   sequent [squash] { 'H >- "assert"{'b['a]} } -->
   sequent ['ext] { 'H >- "assert"{fbexists{'s; x. 'b['x]}} }

interactive fbexists_assert_elim3 {| elim [elim_typeinf <<'s>>] |}'H 'J fset{'eq; 'T} 'u 'v 'w :
   [wf] sequent [squash] { 'H; x: "assert"{fbexists{'s; x. 'b['x]}}; 'J['x] >- "type"{'T} } -->
   [wf] sequent [squash] { 'H; x: "assert"{fbexists{'s; x. 'b['x]}}; 'J['x] >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H; x: "assert"{fbexists{'s; x. 'b['x]}}; 'J['x] >- 's IN fset{'eq; 'T} } -->
   [wf] sequent [squash] { 'H; x: "assert"{fbexists{'s; x. 'b['x]}}; 'J['x]; u: 'T; v: 'T; w: "assert"{fcompare{'eq; 'u; 'v}} >- 'b['u] = 'b['v] in bool } -->
   sequent ['ext] { 'H; x: "assert"{bnot{fball{'s; x. bnot{'b['x]}}}}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: "assert"{fbexists{'s; x. 'b['x]}}; 'J['x] >- 'C['x] }

(*
 * Conversion to a list.
 *)
interactive foflist_wf {| intro [] |} 'H :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- 'l IN list{'T} } -->
   sequent ['ext] { 'H >- foflist{'l} IN fset{'eq; 'T} }

interactive foflist_member_intro_left {| intro [SelectOption 1; intro_typeinf <<'x>>] |} 'H 'T :
   [wf] sequent [squash] { 'H >- "type"{'T} } -->
   [wf] sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H >- 'x IN 'T } -->
   [wf] sequent [squash] { 'H >- 'y IN 'T } -->
   [wf] sequent [squash] { 'H >- 't IN list{'T} } -->
   sequent [squash] { 'H >- "assert"{fcompare{'eq; 'x; 'y}} } -->
   sequent ['ext] { 'H >- "assert"{fmember{'eq; 'x; foflist{cons{'y; 't}}}} }

interactive foflist_member_intro_right {| intro [SelectOption 2; intro_typeinf <<'x>>] |} 'H 'T :
   [wf] sequent [squash] { 'H >- "type"{'T} } -->
   [wf] sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H >- 'x IN 'T } -->
   [wf] sequent [squash] { 'H >- 'y IN 'T } -->
   [wf] sequent [squash] { 'H >- 't IN list{'T} } -->
   sequent [squash] { 'H >- "assert"{fmember{'eq; 'x; 't}} } -->
   sequent ['ext] { 'H >- "assert"{fmember{'eq; 'x; foflist{cons{'y; 't}}}} }

interactive foflist_member_elim_nil {| elim [] |} 'H 'J :
   sequent ['ext] { 'H; z: "assert"{fmember{'eq; 'x; foflist{nil}}}; 'J['z] >- 'C['z] }

interactive foflist_member_elim_cons3 {| elim [elim_typeinf <<'x>>] |} 'H 'J 'T :
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; foflist{cons{'y; 't}}}}; 'J[it] >- "type"{'T} } -->
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; foflist{cons{'y; 't}}}}; 'J[it] >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; foflist{cons{'y; 't}}}}; 'J[it] >- 'x IN 'T } -->
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; foflist{cons{'y; 't}}}}; 'J[it] >- 'y IN 'T } -->
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; foflist{cons{'y; 't}}}}; 'J[it] >- 't IN list{'T} } -->
   sequent ['ext] { 'H; z: "assert"{fcompare{'eq; 'x; 'y}}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; z: "assert"{fmember{'eq; 'x; foflist{'t}}}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; z: "assert"{fmember{'eq; 'x; foflist{cons{'y; 't}}}}; 'J['z] >- 'C['z] }

(*
 * Union.
 *)
interactive funion_member_intro_left3 {| intro [SelectOption 1; intro_typeinf <<'x>>] |}'H 'T :
   [wf] sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H >- 'x IN 'T } -->
   [wf] sequent [squash] { 'H >- 's1 IN fset{'eq; 'T} } -->
   [wf] sequent [squash] { 'H >- 's2 IN fset{'eq; 'T} } -->
   sequent [squash] { 'H >- "assert"{fmember{'eq; 'x; 's1}} } -->
   sequent ['ext] { 'H >- "assert"{fmember{'eq; 'x; funion{'eq; 's1; 's2}}} }

interactive funion_member_intro_right3 {| intro [SelectOption 2; intro_typeinf <<'x>>] |}'H 'T :
   [wf] sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H >- 'x IN 'T } -->
   [wf] sequent [squash] { 'H >- 's1 IN fset{'eq; 'T} } -->
   [wf] sequent [squash] { 'H >- 's2 IN fset{'eq; 'T} } -->
   sequent [squash] { 'H >- "assert"{fmember{'eq; 'x; 's2}} } -->
   sequent ['ext] { 'H >- "assert"{fmember{'eq; 'x; funion{'eq; 's1; 's2}}} }

interactive funion_member_elim3 {| elim [elim_typeinf <<'x>>] |} 'H 'J 'T :
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; funion{'eq; 's1; 's2}}}; 'J[it] >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; funion{'eq; 's1; 's2}}}; 'J[it] >- 'x IN 'T } -->
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; funion{'eq; 's1; 's2}}}; 'J[it] >- 's1 IN fset{'eq; 'T} } -->
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; funion{'eq; 's1; 's2}}}; 'J[it] >- 's2 IN fset{'eq; 'T} } -->
   sequent ['ext] { 'H; z: "assert"{fmember{'eq; 'x; 's1}}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; z: "assert"{fmember{'eq; 'x; 's2}}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; z: "assert"{fmember{'eq; 'x; funion{'eq; 's1; 's2}}}; 'J['z] >- 'C['z] }

(*
 * Intersection.
 *)
interactive fisect_member_intro3 {| intro [intro_typeinf <<'x>>] |} 'H 'T :
   [wf] sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H >- 'x IN 'T } -->
   [wf] sequent [squash] { 'H >- 's1 IN fset{'eq; 'T} } -->
   [wf] sequent [squash] { 'H >- 's2 IN fset{'eq; 'T} } -->
   sequent [squash] { 'H >- "assert"{fmember{'eq; 'x; 's1}} } -->
   sequent [squash] { 'H >- "assert"{fmember{'eq; 'x; 's2}} } -->
   sequent ['ext] { 'H >- "assert"{fmember{'eq; 'x; fisect{'eq; 's1; 's2}}} }

interactive fisect_member_elim3 {| elim [elim_typeinf <<'x>>] |} 'H 'J 'T :
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; fisect{'eq; 's1; 's2}}}; 'J['z] >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; fisect{'eq; 's1; 's2}}}; 'J['z] >- 'x IN 'T } -->
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; fisect{'eq; 's1; 's2}}}; 'J['z] >- 's1 IN fset{'eq; 'T} } -->
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; fisect{'eq; 's1; 's2}}}; 'J['z] >- 's2 IN fset{'eq; 'T} } -->
   sequent ['ext] { 'H; u: "assert"{fmember{'eq; 'x; 's1}}; v: "assert"{fmember{'eq; 'x; 's2}}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; z: "assert"{fmember{'eq; 'x; fisect{'eq; 's1; 's2}}}; 'J['z] >- 'C['z] }

(*
 * Subtraction.
 *)
interactive fsub_member_intro3 {| intro [intro_typeinf <<'x>>] |}'H 'T :
   [wf] sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H >- 'x IN 'T } -->
   [wf] sequent [squash] { 'H >- 's1 IN fset{'eq; 'T} } -->
   [wf] sequent [squash] { 'H >- 's2 IN fset{'eq; 'T} } -->
   sequent [squash] { 'H >- "assert"{fmember{'eq; 'x; 's1}} } -->
   sequent [squash] { 'H >- "assert"{bnot{fmember{'eq; 'x; 's2}}} } -->
   sequent ['ext] { 'H >- "assert"{fmember{'eq; 'x; fsub{'eq; 's1; 's2}}} }

interactive fsub_member_elim3 {| elim [elim_typeinf <<'x>>] |} 'H 'J 'T :
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; fsub{'eq; 's1; 's2}}}; 'J['z] >- fequalp{'eq; 'T} } -->
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; fsub{'eq; 's1; 's2}}}; 'J['z] >- 'x IN 'T } -->
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; fsub{'eq; 's1; 's2}}}; 'J['z] >- 's1 IN fset{'eq; 'T} } -->
   [wf] sequent [squash] { 'H; z: "assert"{fmember{'eq; 'x; fsub{'eq; 's1; 's2}}}; 'J['z] >- 's2 IN fset{'eq; 'T} } -->
   sequent ['ext] { 'H; u: "assert"{fmember{'eq; 'x; 's1}}; v: "assert"{bnot{fmember{'eq; 'x; 's2}}}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; z: "assert"{fmember{'eq; 'x; fsub{'eq; 's1; 's2}}}; 'J['z] >- 'C['z] }

(*
 * Universal quaintifier.
interactive fall_wf2 {| intro [] |} 'H :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- 's IN fset{'eq; 'T} } -->
   sequent [squash] { 'H; u: feset{'eq; 'T} >- "type"{'b['x]} } -->
   sequent ['ext] { 'H >- "type"{fall{'eq; 'T; 's; x. 'b['x]}} }

interactive fall_intro 'H 'u 'w :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent [squash] { 'H >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H >- 's IN fset{'eq; 'T} } -->
   sequent ['ext] { 'H; u: feset{'eq; 'T}; w: fmember{'eq; 'u; 's} >- 'b['u] } -->
   sequent ['ext] { 'H >- fall{'eq; 'T; 's; x. 'b['x]} }

interactive fall_elim 'H 'J 'a 'w :
   sequent [squash] { 'H; x: fall{'eq; 'T; 's; y. 'b['y]}; 'J['x] >- "type"{'T} } -->
   sequent [squash] { 'H; x: fall{'eq; 'T; 's; y. 'b['y]}; 'J['x] >- fequalp{'eq; 'T} } -->
   sequent [squash] { 'H; x: fall{'eq; 'T; 's; y. 'b['y]}; 'J['x] >- 's IN fset{'eq; 'T} } -->
   sequent [squash] { 'H; x: fall{'eq; 'T; 's; y. 'b['y]}; 'J['x] >- 'a IN 'T } -->
   sequent [squash] { 'H; x: fall{'eq; 'T; 's; y. 'b['y]}; 'J['x] >- "assert"{fmember{'eq; 'a; 's}} } -->
   sequent ['ext] { 'H; x: fall{'eq; 'T; 's; y. 'b['y]}; 'J['x]; w: 'b['a] >- 'C['x] }
   sequent ['ext] { 'H; x: fall{'eq; 'T; 's; y. 'b['y]}; 'J['x] >- 'C['x] }
 *)

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let fmember_subst_elementT x p =
   let t =
      try get_univ_arg p with
         RefineError _ ->
            let t = Sequent.concl p in
            let t = dest_assert t in
            let _, x, _ = dest_fmember t in
            infer_type p x
   in
      fmember_fun (Sequent.hyp_count_addr p) t x p

let assert_2of3_type p t =
   try get_with_arg p with
      RefineError _ ->
         let t = dest_assert t in
         let _, x, y = three_subterms t in begin
            try infer_type p x with
               RefineError _ ->
                  infer_type p y
         end

let fcompareSymT p =
   fcompare_sym (Sequent.hyp_count_addr p) (assert_2of3_type p (Sequent.concl p)) p

let fcompareTransT z p =
   fcompare_trans (Sequent.hyp_count_addr p) (assert_2of3_type p (Sequent.concl p)) z p

let assert_2of3_fset_type p t =
   dest_fset_type (assert_2of3_type p t)

let fsubseteqTransT t p =
   fsubseteq_trans (Sequent.hyp_count_addr p) (assert_2of3_fset_type p (Sequent.concl p)) t p

(*
 * -*-
 * Local Variables:
 * Caml-master: "mp.run"
 * End:
 * -*-
 *)
