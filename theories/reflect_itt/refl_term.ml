(*
 * Terms modulo alpha equality.
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

include Refl_raw_term

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Var

open Base_dtactic
open Base_auto_tactic
open Typeinf

open Itt_equal
open Itt_bool
open Itt_struct
open Itt_logic

open Refl_raw_term

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare eq_alpha{'t1; 't2}
declare eq_alpha_term{'f; 't1; 't2}
declare eq_alpha_bterm{'f; 'bt1; 'bt2}

declare vmap_nil
declare vmap_cons{'v1; 'v2; 'vmap}
declare vmap_compose{'vl1; 'vl2; 'vm; g. 'b['g]}
declare vmap_compare{'v1; 'v2; 'vm}
declare vmap_type
declare vmap_invert{'f}
declare vmap_id{'f}
declare vmap_length{'f; 'g}
declare vmap_join{'f; 'g}
declare vmap_fst{'f}
declare vmap_snd{'f}

declare bterm_type{'T}
declare term_type

declare term_depth{'t}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_vmap_compose
prec prec_vmap_fst

(*
 * Equality.
 *)
dform eq_alpha_df : mode[prl] :: parens :: "prec"[prec_equal] :: eq_alpha{'t1; 't2} =
   slot{'t1} space `"=" alpha space slot{'t2}

dform eq_alpha_term_df : mode[prl] :: parens :: "prec"[prec_equal] :: eq_alpha_term{'f; 't1; 't2} =
   slot{'t1} space `"=" alpha `"[" slot{'f} `"] " slot{'t2}

dform eq_alpha_bterm_df : mode[prl] :: parens :: "prec"[prec_equal] :: eq_alpha_bterm{'f; 't1; 't2} =
   slot{'t1} space `"=" alpha `"[" slot{'f} `"] " slot{'t2}

(*
 * Variable maps.
 *)
declare search{'a; 'b}
declare arrows{'a}

(* Application *)
dform vmap_type_df : mode[prl] :: vmap_type =
   `"VMap"

dform vmap_compare_df : mode[prl] :: parens :: "prec"[prec_equal] :: vmap_compare{'v1; 'v2; 'vm} =
   slot{'v1} `" =" slot{'vm} space slot{'v2}

dform vmap_invert_df : mode[prl] :: vmap_invert{'f} =
   `"Invert(" slot{'f} `")"

dform vmap_id_df : mode[prl] :: vmap_id{'f} =
   `"Id(" slot{'f} `")"

dform vmap_length_df : mode[prl] :: vmap_length{'f; 'g} =
   `"|" slot{'f} `"| = |" slot{'g} `"|"

dform vmap_join_df : mode[prl] :: vmap_join{'f; 'g} =
   `"Join(" slot{'f} `", " slot{'g} `")"

(* Empty list *)
dform vmap_nil_df : vmap_nil = `"[]"

(* Search for nil entry *)
dform vmap_cons_df : vmap_cons{'v1; 'v2; 'b} =
   search{vmap_cons{'v1; 'v2; vmap_nil}; 'b}

(* Keep searching down the list *)
dform search_df1 : search{'a; vmap_cons{'v1; 'v2; 'c}} =
   search{vmap_cons{'v1; 'v2; 'a}; 'c}

(* Found a nil terminator: use bracket notation *)
dform search_df2 : search{'a; vmap_nil} =
   `"[" pushm arrows{'a} popm `"]"

(* No nil terminator, so use :: notation *)
dform search_df3 : search{'a; 'b} =
   `"[" pushm arrows{'a} popm `"]." slot{'b}

(* Reverse entries and separate with ; *)
dform arrows_df1 : arrows{vmap_cons{'v1; 'v2; vmap_nil}} =
   slot{'v1} space rightarrow space slot{'v2}

dform arrows_df2 : arrows{vmap_cons{'v1; 'v2; 'b}} =
   arrows{'b} `";" hspace slot{'v1} space rightarrow space slot{'v2}

dform vmap_compose_df : mode[prl] :: parens :: "prec"[prec_vmap_compose] ::
   vmap_compose{'vl1; 'vl2; 'vm; g. 'b} =
   szone pushm[3] `"let " slot{'g} `" = " vmap_cons{'vl1; 'vl2; 'vm} `" in" hspace
      slot{'b} popm ezone

dform vmap_fst : mode[prl] :: parens :: "prec"[prec_vmap_fst] :: vmap_fst{'f} =
   slot{'f} `".1"

dform vmap_snd : mode[prl] :: parens :: "prec"[prec_vmap_fst] :: vmap_snd{'f} =
   slot{'f} `".2"

(*
 * Types.
 *)
dform bterm_type_df : mode[prl] :: bterm_type{'T} =
   `"BtermType(" slot{'T} `")"

dform term_type_df : mode[prl] :: term_type =
   `"Term"

dform term_depth_df : mode[prl] :: term_depth{'t} =
   `"depth(" slot{'t} `")"

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*
 * Variable maps.
 *)
prim_rw unfold_vmap_type :
   vmap_type <--> list{.var_type * var_type}

prim_rw unfold_vmap_compare :
   vmap_compare{'v1; 'v2; 'f} <-->
   list_ind{'f; eq_var{'v1; 'v2};
            h, t, g. spread{'h; a, b.
               ifthenelse{eq_var{'a; 'v1}; eq_var{'b; 'v2};
                  ifthenelse{eq_var{'b; 'v2}; bfalse; 'g}}}}

prim_rw unfold_vmap_invert :
   vmap_invert{'f} <-->
      map{lambda{x. spread{'x; u, v. 'v, 'u}}; 'f}

prim_rw unfold_vmap_id :
   vmap_id{'f} <-->
      list_ind{'f; btrue; h, t, g. band{spread{'h; u, v. eq_var{'u; 'v}}; 'g}}

prim_rw unfold_vmap_length :
   vmap_length{'f; 'g} <-->
      (list_ind{'f; lambda{x. list_ind{'x; btrue; h2, t2, g2. bfalse}};
         h1, t1, g1.
            lambda{x. list_ind{'x; bfalse; h2, t2, g2. 'g1 't2}}} 'g)

prim_rw unfold_vmap_join :
   vmap_join{'f; 'g} <-->
      (list_ind{'f; lambda{x. vmap_nil};
                h1, t1, g1.
                   lambda{x. list_ind{'x; vmap_nil; h2, t2, g2.
                      spread{'h1; u1, v1.
                         spread{'h2; u2, v2.
                            cons{pair{'u1; 'v2}; .'g1 't2}}}}}} 'g)

prim_rw unfold_vmap_nil : vmap_nil <--> nil

prim_rw unfold_vmap_cons :
   vmap_cons{'v1; 'v2; 'vm} <--> cons{pair{'v1; 'v2}; 'vm}

prim_rw unfold_vmap_compose :
   vmap_compose{'vl1; 'vl2; 'vm; g. 'b['g]} <-->
      (list_ind{'vl1; lambda{l. lambda{g. list_ind{'l; 'b['g]; h, t, f. bfalse}}};
                h1, t1, f1. lambda{l. lambda{g. list_ind{'l; bfalse;
                h2, t2, f2. 'f1 't2 vmap_cons{'h1; 'h2; 'g}}}}} 'vl2 'vm)

prim_rw unfold_vmap_fst :
   vmap_fst{'f} <-->
      list_ind{'f; nil; h, t, g. spread{'h; u, v. cons{'u; 'g}}}

prim_rw unfold_vmap_snd :
   vmap_snd{'f} <-->
      list_ind{'f; nil; h, t, g. spread{'h; u, v. cons{'v; 'g}}}

(*
 * Equality.
 *)
prim_rw unfold_eq_alpha :
   eq_alpha{'t1; 't2} <-->
      eq_alpha_term{vmap_nil; 't1; 't2}

prim_rw unfold_eq_alpha_term :
   eq_alpha_term{'f; 't1; 't2} <-->
   match_term{'t1;
      v1, tl1.
         match_term{'t2;
            v2, tl2.
               ifthenelse{band{is_nil{'tl1}; is_nil{'tl2}};
                          vmap_compare{'v1; 'v2; 'f};
                          band{eq_var{'v1; 'v2}; ball2{'tl1; 'tl2; t1, t2. eq_alpha_term{'f; 't1; 't2}}}};
            op2, bterms2. bfalse};
      op1, bterms1.
         match_term{'t2;
            v2, tl2. bfalse;
            op2, bterms2. band{eq_op{'op1; 'op2};
                               ball2{'bterms1; 'bterms2;
                               bt1, bt2. eq_alpha_bterm{'f; 'bt1; 'bt2}}}}}

prim_rw unfold_eq_alpha_bterm :
   eq_alpha_bterm{'f; 'bt1; 'bt2} <-->
   spread{'bt1; sl1, t1.
      spread{'bt2; sl2, t2.
         vmap_compose{'sl1; 'sl2; 'f; g. eq_alpha_term{'g; 't1; 't2}}}}

(*
 * Types.
 *)
prim_rw unfold_term_type :
   term_type <--> (quot x, y : raw_term_type // "assert"{eq_alpha{'x; 'y}})

prim_rw unfold_bterm_type :
   bterm_type{'T} <--> (quot x, y : raw_bterm_type{'T} // "assert"{eq_alpha_bterm{vmap_nil; 'x; 'y}})

(*
prim_rw unfold_term_depth :
   term_depth{'t} <-->
      match_term{'t;
                 v, tl. list_ind{'tl; 1; h, t, g. term_depth{'h} +@ 'g};
                 op, bterms. list_ind{'bterms; 1; h, t, g. term_depth{bterm_term{'h}} +@ 'g}}
*)

let fold_vmap_type = makeFoldC << vmap_type >> unfold_vmap_type
let fold_vmap_nil = makeFoldC << vmap_nil >> unfold_vmap_nil
let fold_vmap_cons = makeFoldC << vmap_cons{'v1; 'v2; 'f} >> unfold_vmap_cons
let fold_vmap_compose = makeFoldC << vmap_compose{'vl1; 'vl2; 'f; g.'b['g]} >> unfold_vmap_compose
let fold_vmap_compare = makeFoldC << vmap_compare{'v1; 'v2; 'f} >> unfold_vmap_compare
let fold_vmap_invert = makeFoldC << vmap_invert{'f} >> unfold_vmap_invert
let fold_vmap_id = makeFoldC << vmap_id{'f} >> unfold_vmap_id
let fold_vmap_length = makeFoldC << vmap_length{'f; 'g} >> unfold_vmap_length
let fold_vmap_join = makeFoldC << vmap_join{'f; 'g} >> unfold_vmap_join
let fold_vmap_fst = makeFoldC << vmap_fst{'f} >> unfold_vmap_fst
let fold_vmap_snd = makeFoldC << vmap_snd{'f} >> unfold_vmap_snd
let fold_eq_alpha = makeFoldC << eq_alpha{'t1; 't2} >> unfold_eq_alpha
let fold_eq_alpha_term = makeFoldC << eq_alpha_term{'f; 't1; 't2} >> unfold_eq_alpha_term
let fold_eq_alpha_bterm = makeFoldC << eq_alpha_bterm{'f; 'bt1; 'bt2} >> unfold_eq_alpha_bterm
let fold_term_type = makeFoldC << term_type >> unfold_term_type
let fold_bterm_type = makeFoldC << bterm_type{'T} >> unfold_bterm_type
(*
let fold_term_depth = makeFoldC << term_depth{'t} >> unfold_term_depth
*)

(************************************************************************
 * REDUCTIONS                                                           *
 ************************************************************************)

(*
 * Variable maps.
 *)
interactive_rw reduce_vmap_compare_nil :
   vmap_compare{'v1; 'v2; vmap_nil} <--> eq_var{'v1; 'v2}

interactive_rw reduce_vmap_compare_cons :
   vmap_compare{'v1; 'v2; vmap_cons{'v3; 'v4; 'f}} <-->
      ifthenelse{eq_var{'v3; 'v1}; eq_var{'v4; 'v2};
         ifthenelse{eq_var{'v4; 'v2}; bfalse;
            vmap_compare{'v1; 'v2; 'f}}}

interactive_rw reduce_vmap_compose_nil_nil :
   vmap_compose{nil; nil; 'vm; g. 'b['g]} <-->
      'b['vm]

interactive_rw reduce_vmap_compose_nil_cons :
   vmap_compose{nil; cons{'h; 't}; 'vm; g. 'b['g]} <-->
      bfalse

interactive_rw reduce_vmap_compose_cons_nil :
   vmap_compose{cons{'h; 't}; nil; 'vm; g. 'b['g]} <-->
      bfalse

interactive_rw reduce_vmap_compose_cons_cons :
   vmap_compose{cons{'h1; 't1}; cons{'h2; 't2}; 'vm; g. 'b['g]} <-->
      vmap_compose{'t1; 't2; vmap_cons{'h1; 'h2; 'vm}; g. 'b['g]}

interactive_rw reduce_vmap_invert_nil :
   vmap_invert{vmap_nil} <--> vmap_nil

interactive_rw reduce_vmap_invert_cons :
   vmap_invert{vmap_cons{'v1; 'v2; 'vm}} <--> vmap_cons{'v2; 'v1; vmap_invert{'vm}}

interactive_rw reduce_vmap_id_nil :
   vmap_id{vmap_nil} <--> btrue

interactive_rw reduce_vmap_id_cons :
   vmap_id{vmap_cons{'v1; 'v2; 'f}} <--> band{eq_var{'v1; 'v2}; vmap_id{'f}}

interactive_rw reduce_vmap_length_nil_nil :
   vmap_length{vmap_nil; vmap_nil} <--> btrue

interactive_rw reduce_vmap_length_nil_cons :
   vmap_length{vmap_nil; vmap_cons{'v1; 'v2; 'f}} <--> bfalse

interactive_rw reduce_vmap_length_cons_nil :
   vmap_length{vmap_cons{'v1; 'v2; 'f}; vmap_nil} <--> bfalse

interactive_rw reduce_vmap_length_cons_cons :
   vmap_length{vmap_cons{'v1; 'v2; 'f}; vmap_cons{'v3; 'v4; 'g}} <-->
      vmap_length{'f; 'g}

interactive_rw reduce_vmap_join_nil_nil :
   vmap_join{vmap_nil; vmap_nil} <--> vmap_nil

interactive_rw reduce_vmap_join_nil_cons :
   vmap_join{vmap_nil; vmap_cons{'v1; 'v2; 'f}} <--> vmap_nil

interactive_rw reduce_vmap_join_cons_nil :
   vmap_join{vmap_cons{'v1; 'v2; 'f}; vmap_nil} <--> vmap_nil

interactive_rw reduce_vmap_join_cons_cons :
   vmap_join{vmap_cons{'v1; 'v2; 'f}; vmap_cons{'v3; 'v4; 'g}} <-->
      vmap_cons{'v1; 'v4; vmap_join{'f; 'g}}

interactive_rw reduce_vmap_fst_nil :
   vmap_fst{vmap_nil} <--> nil

interactive_rw reduce_vmap_fst_cons :
   vmap_fst{vmap_cons{'v1; 'v2; 'f}} <--> cons{'v1; vmap_fst{'f}}

interactive_rw reduce_vmap_snd_nil :
   vmap_snd{vmap_nil} <--> nil

interactive_rw reduce_vmap_snd_cons :
   vmap_snd{vmap_cons{'v1; 'v2; 'f}} <--> cons{'v2; vmap_snd{'f}}

(*
 * Alpha equality.
 *)
interactive_rw reduce_eq_alpha_term_bvar_bvar :
   eq_alpha_term{'vm; bvar{'v1; 'tl1}; bvar{'v2; 'tl2}} <-->
      ifthenelse{band{is_nil{'tl1}; is_nil{'tl2}};
                 vmap_compare{'v1; 'v2; 'vm};
                 band{eq_var{'v1; 'v2}; ball2{'tl1; 'tl2; t1, t2. eq_alpha_term{'vm; 't1; 't2}}}}

interactive_rw reduce_eq_alpha_term_bvar_term :
   eq_alpha_term{'vm; bvar{'v; 'tl}; term{'op; 'bterms}} <--> bfalse

interactive_rw reduce_eq_alpha_term_term_bvar :
   eq_alpha_term{'vm; term{'op; 'bterms}; bvar{'v; 'tl}} <--> bfalse

interactive_rw reduce_eq_alpha_term_term_term :
   eq_alpha_term{'vm; term{'op1; 'bterms1}; term{'op2; 'bterms2}} <-->
      band{eq_op{'op1; 'op2};
           ball2{'bterms1; 'bterms2; bt1, bt2. eq_alpha_bterm{'vm; 'bt1; 'bt2}}}

(*
 * Term depth.
 *)
(*
interactive_rw reduce_term_depth_bvar :
   term_depth{bvar{'v; 'tl}} <-->
      list_ind{'tl; 1; h, t, g. term_depth{'h} +@ 'g}

interactive_rw reduce_term_depth_bterm :
   term_depth{bterm{'op; 'bterms}} <-->
      list_ind{'bterms; 1; h, t, g. term_depth{bterm_term{'h}} +@ 'g}
*)

(************************************************************************
 * REDUCTIONS                                                           *
 ************************************************************************)

let reduce_info =
   [<< vmap_compare{'v1; 'v2; vmap_nil} >>, reduce_vmap_compare_nil;
    << vmap_compare{'v1; 'v2; vmap_cons{'v3; 'v4; 'vm}} >>, reduce_vmap_compare_cons;
    << vmap_compose{nil; nil; 'vm; g. 'b['g]} >>, reduce_vmap_compose_nil_nil;
    << vmap_compose{nil; cons{'h; 't}; 'vm; g. 'b['g]} >>, reduce_vmap_compose_nil_cons;
    << vmap_compose{cons{'h; 't}; nil; 'vm; g. 'b['g]} >>, reduce_vmap_compose_cons_nil;
    << vmap_compose{cons{'h1; 't1}; cons{'h2; 't2}; 'vm; g. 'b['g]} >>, reduce_vmap_compose_cons_cons;
    << vmap_invert{vmap_nil} >>, reduce_vmap_invert_nil;
    << vmap_invert{vmap_cons{'v1; 'v2; 'vm}} >>, reduce_vmap_invert_cons;
    << vmap_id{vmap_nil} >>, reduce_vmap_id_nil;
    << vmap_id{vmap_cons{'v1; 'v2; 'f}} >>, reduce_vmap_id_cons;
    << vmap_length{vmap_nil; vmap_nil} >>, reduce_vmap_length_nil_nil;
    << vmap_length{vmap_nil; vmap_cons{'v1; 'v2; 'f}} >>, reduce_vmap_length_nil_cons;
    << vmap_length{vmap_cons{'v1; 'v2; 'f}; vmap_nil} >>, reduce_vmap_length_cons_nil;
    << vmap_length{vmap_cons{'v1; 'v2; 'f}; vmap_cons{'v3; 'v4; 'g}} >>, reduce_vmap_length_cons_cons;
    << vmap_join{vmap_nil; vmap_nil} >>, reduce_vmap_join_nil_nil;
    << vmap_join{vmap_nil; vmap_cons{'v1; 'v2; 'f}} >>, reduce_vmap_join_nil_cons;
    << vmap_join{vmap_cons{'v1; 'v2; 'f}; vmap_nil} >>, reduce_vmap_join_cons_nil;
    << vmap_join{vmap_cons{'v1; 'v2; 'f}; vmap_cons{'v3; 'v4; 'g}} >>, reduce_vmap_join_cons_cons;
    << vmap_fst{vmap_nil} >>, reduce_vmap_fst_nil;
    << vmap_fst{vmap_cons{'v1; 'v2; 'f}} >>, reduce_vmap_fst_cons;
    << vmap_snd{vmap_nil} >>, reduce_vmap_snd_nil;
    << vmap_snd{vmap_cons{'v1; 'v2; 'f}} >>, reduce_vmap_snd_cons;
    << eq_alpha_term{'vm; bvar{'v1; 'tl1}; bvar{'v2; 'tl2}} >>, reduce_eq_alpha_term_bvar_bvar;
    << eq_alpha_term{'vm; bvar{'v; 'tl}; term{'op; 'bterms}} >>, reduce_eq_alpha_term_bvar_term;
    << eq_alpha_term{'vm; term{'op; 'bterms}; bvar{'v; 'tl}} >>, reduce_eq_alpha_term_term_bvar;
    << eq_alpha_term{'vm; term{'op1; 'bterms1}; term{'op2; 'bterms2}} >>, reduce_eq_alpha_term_term_term]

let reduce_resource = Top_conversionals.add_reduce_info reduce_resource reduce_info

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Variable maps.
 *)
interactive vmap_type_type2 {| intro [] |} 'H :
   sequent ['ext] { 'H >- "type"{vmap_type} }

interactive vmap_elim {| elim [ThinOption thinT] |} 'H 'J 'v1 'v2 'g 'w :
   [main] sequent ['ext] { 'H; f: vmap_type; 'J['f] >- 'C[vmap_nil] } -->
   [main] sequent ['ext] { 'H; f: vmap_type; 'J['f]; v1: var_type; v2: var_type; g: vmap_type; w: 'C['g] >- 'C[vmap_cons{'v1; 'v2; 'g}] } -->
   sequent ['ext] { 'H; f: vmap_type; 'J['f] >- 'C['f] }

interactive vmap_compare_wf {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'vm IN vmap_type } -->
   [wf] sequent [squash] { 'H >- 'v1 IN var_type } -->
   [wf] sequent [squash] { 'H >- 'v2 IN var_type } -->
   sequent ['ext] { 'H >- vmap_compare{'v1; 'v2; 'vm} IN bool }

interactive vmap_nil_wf2 {| intro [] |} 'H :
   sequent ['ext] { 'H >- vmap_nil IN vmap_type }

interactive vmap_cons_wf2 {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'v1 IN var_type } -->
   [wf] sequent [squash] { 'H >- 'v2 IN var_type } -->
   [wf] sequent [squash] { 'H >- 'vm IN vmap_type } -->
   sequent ['ext] { 'H >- vmap_cons{'v1; 'v2; 'vm} IN vmap_type }

interactive vmap_compose_wf2 {| intro [] |} 'H 'f :
   [wf] sequent [squash] { 'H >- 'vl1 IN list{var_type} } -->
   [wf] sequent [squash] { 'H >- 'vl2 IN list{var_type} } -->
   [wf] sequent [squash] { 'H >- 'vm IN vmap_type } -->
   [wf] sequent [squash] { 'H; f: vmap_type >- 'b['f] IN bool } -->
   sequent ['ext] { 'H >- vmap_compose{'vl1; 'vl2; 'vm; g. 'b['g]} IN bool }

interactive vmap_invert_wf2 {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'f IN vmap_type } -->
   sequent ['ext] { 'H >- vmap_invert{'f} IN vmap_type }

interactive vmap_id_wf {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'f IN vmap_type } -->
   sequent ['ext] { 'H >- vmap_id{'f} IN bool }

interactive vmap_length_wf {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'f IN vmap_type } -->
   [wf] sequent [squash] { 'H >- 'g IN vmap_type } -->
   sequent ['ext] { 'H >- vmap_length{'f; 'g} IN bool }

interactive vmap_join_wf {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'f IN vmap_type } -->
   [wf] sequent [squash] { 'H >- 'g IN vmap_type } -->
   sequent ['ext] { 'H >- vmap_join{'f; 'g} IN vmap_type }

interactive vmap_fst_wf {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'f IN vmap_type } -->
   sequent ['ext] { 'H >- vmap_fst{'f} IN list{var_type} }

interactive vmap_snd_wf {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'f IN vmap_type } -->
   sequent ['ext] { 'H >- vmap_snd{'f} IN list{var_type} }

(*
 * Properties about the variable comparison.
 *)
interactive vmap_compare_sym 'H :
   sequent [squash] { 'H >- 'f IN vmap_type } -->
   sequent [squash] { 'H >- 'v1 IN var_type } -->
   sequent [squash] { 'H >- 'v2 IN var_type } -->
   sequent [squash] { 'H >- "assert"{vmap_compare{'v2; 'v1; vmap_invert{'f}}} } -->
   sequent ['ext] { 'H >- "assert"{vmap_compare{'v1; 'v2; 'f}} }

interactive vmap_compare_trans 'H 'g 'v2 :
   sequent [squash] { 'H >- 'f IN vmap_type } -->
   sequent [squash] { 'H >- 'g IN vmap_type } -->
   sequent [squash] { 'H >- 'v1 IN var_type } -->
   sequent [squash] { 'H >- 'v2 IN var_type } -->
   sequent [squash] { 'H >- 'v3 IN var_type } -->
   sequent [squash] { 'H >- "assert"{vmap_id{'g}} } -->
   sequent [squash] { 'H >- "assert"{vmap_length{'f; 'g}} } -->
   sequent [squash] { 'H >- "assert"{vmap_compare{'v1; 'v2; vmap_join{'f; 'g}}} } -->
   sequent [squash] { 'H >- "assert"{vmap_compare{'v2; 'v3; vmap_join{'g; 'f}}} } -->
   sequent ['ext] { 'H >- "assert"{vmap_compare{'v1; 'v3; 'f}} }

(*
 * Alpha equality on terms.
 *)
interactive eq_alpha_term_wf {| intro [SelectOption 1] |} 'H :
   [wf] sequent [squash] { 'H >- 'f IN vmap_type } -->
   [wf] sequent [squash] { 'H >- 't1 IN raw_term_type } -->
   [wf] sequent [squash] { 'H >- 't2 IN raw_term_type } -->
   sequent ['ext] { 'H >- eq_alpha_term{'f; 't1; 't2} IN bool }

interactive eq_alpha_bterm_wf2 {| intro [SelectOption 2] |} 'H 'T1 'T2 :
   [wf] sequent [squash] { 'H >- subtype{'T1; raw_term_type} } -->
   [wf] sequent [squash] { 'H >- subtype{'T2; raw_term_type} } -->
   [wf] sequent [squash] { 'H >- 'f IN vmap_type } -->
   [wf] sequent [squash] { 'H >- 't1 IN raw_bterm_type{'T1} } -->
   [wf] sequent [squash] { 'H >- 't2 IN raw_bterm_type{'T2} } -->
   sequent ['ext] { 'H >- eq_alpha_bterm{'f; 't1; 't2} IN bool }

interactive eq_alpha_term_ref 'H 'v :
   [wf] sequent [squash] { 'H >- 'f IN vmap_type } -->
   [main] sequent [squash] { 'H; v: var_type >- "assert"{vmap_compare{'v; 'v; 'f}} } -->
   [wf] sequent [squash] { 'H >- 't IN raw_term_type } -->
   sequent ['ext] { 'H >- "assert"{eq_alpha_term{'f; 't; 't}} }

interactive eq_alpha_term_sym 'H :
   [wf] sequent [squash] { 'H >- 'f IN vmap_type } -->
   [wf] sequent [squash] { 'H >- 't1 IN raw_term_type } -->
   [wf] sequent [squash] { 'H >- 't2 IN raw_term_type } -->
   [main] sequent [squash] { 'H >- "assert"{eq_alpha_term{vmap_invert{'f}; 't2; 't1}} } -->
   sequent ['ext] { 'H >- "assert"{eq_alpha_term{'f; 't1; 't2}} }

interactive eq_alpha_term_trans 'H 'g 't2 :
   [wf] sequent [squash] { 'H >- 'f IN vmap_type } -->
   [wf] sequent [squash] { 'H >- 'g IN vmap_type } -->
   [wf] sequent [squash] { 'H >- 't1 IN raw_term_type } -->
   [wf] sequent [squash] { 'H >- 't2 IN raw_term_type } -->
   [wf] sequent [squash] { 'H >- 't3 IN raw_term_type } -->
   [main] sequent [squash] { 'H >- "assert"{vmap_id{'g}} } -->
   [main] sequent [squash] { 'H >- "assert"{vmap_length{'f; 'g}} } -->
   [main] sequent [squash] { 'H >- "assert"{eq_alpha_term{vmap_join{'f; 'g}; 't1; 't2}} } -->
   [main] sequent [squash] { 'H >- "assert"{eq_alpha_term{vmap_join{'g; 'f}; 't2; 't3}} } -->
   sequent ['ext] { 'H >- "assert"{eq_alpha_term{'f; 't1; 't3}} }

(*
 * Unconditional alpha-equality.
 *)
interactive eq_alpha_wf {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 't1 IN raw_term_type } -->
   [wf] sequent [squash] { 'H >- 't2 IN raw_term_type } -->
   sequent ['ext] { 'H >- eq_alpha{'t1; 't2} IN bool }

interactive eq_alpha_ref 'H :
   [wf] sequent [squash] { 'H >- 't IN raw_term_type } -->
   sequent ['ext] { 'H >- "assert"{eq_alpha{'t; 't}} }

interactive eq_alpha_sym 'H :
   [wf] sequent [squash] { 'H >- 't1 IN raw_term_type } -->
   [wf] sequent [squash] { 'H >- 't2 IN raw_term_type } -->
   [main] sequent [squash] { 'H >- "assert"{eq_alpha{'t2; 't1}} } -->
   sequent ['ext] { 'H >- "assert"{eq_alpha{'t1; 't2}} }

interactive eq_alpha_trans 'H 't2 :
   [wf] sequent [squash] { 'H >- 't1 IN raw_term_type } -->
   [wf] sequent [squash] { 'H >- 't2 IN raw_term_type } -->
   [wf] sequent [squash] { 'H >- 't3 IN raw_term_type } -->
   [main] sequent [squash] { 'H >- "assert"{eq_alpha{'t1; 't2}} } -->
   [main] sequent [squash] { 'H >- "assert"{eq_alpha{'t2; 't3}} } -->
   sequent ['ext] { 'H >- "assert"{eq_alpha{'t1; 't3}} }

(*
 * Term type.
 *)
interactive term_type_type {| intro [] |} 'H :
   sequent ['ext] { 'H >- "type"{term_type} }

(*
 * Depth of a term.
 *)
(*
interactive term_depth_wf1 'H :
   sequent [squash] { 'H >- 't IN raw_term_type } -->
   sequent ['ext] { 'H >- term_depth{'t} IN int }
*)

(*
 * Bound term type.
 *)
(*
interactive eq_alpha_bterm_ref2 'H 'T 'v :
   sequent [squash] { 'H >- subtype{'T; term_type} } -->
   sequent [squash] { 'H >- 'f IN vmap_type } -->
   sequent [squash] { 'H; v: var_type >- "assert"{vmap_compare{'v; 'v; 'f}} } -->
   sequent [squash] { 'H >- 't IN raw_bterm_type{'T} } -->
   sequent ['ext] { 'H >- "assert"{eq_alpha_bterm{'f; 't; 't}} }

interactive eq_alpha_bterm_sym2 'H 'T :
   sequent [squash] { 'H >- subtype{'T; term_type} } -->
   sequent [squash] { 'H >- 'f IN vmap_type } -->
   sequent [squash] { 'H >- 't1 IN raw_bterm_type{'T} } -->
   sequent [squash] { 'H >- 't2 IN raw_bterm_type{'T} } -->
   sequent [squash] { 'H >- "assert"{eq_alpha_bterm{vmap_invert{'f}; 't2; 't1}} } -->
   sequent ['ext] { 'H >- "assert"{eq_alpha_bterm{'f; 't1; 't2}} }

interactive eq_alpha_bterm_trans2 'H 'T 'g 't2 :
   sequent [squash] { 'H >- subtype{'T; term_type} } -->
   sequent [squash] { 'H >- 'f IN vmap_type } -->
   sequent [squash] { 'H >- 'g IN vmap_type } -->
   sequent [squash] { 'H >- 't1 IN raw_bterm_type{'T} } -->
   sequent [squash] { 'H >- 't2 IN raw_bterm_type{'T} } -->
   sequent [squash] { 'H >- 't3 IN raw_bterm_type{'T} } -->
   sequent [squash] { 'H >- "assert"{vmap_id{'g}} } -->
   sequent [squash] { 'H >- "assert"{vmap_length{'f; 'g}} } -->
   sequent [squash] { 'H >- "assert"{eq_alpha_bterm{vmap_join{'f; 'g}; 't1; 't2}} } -->
   sequent [squash] { 'H >- "assert"{eq_alpha_bterm{vmap_join{'g; 'f}; 't2; 't3}} } -->
   sequent ['ext] { 'H >- "assert"{eq_alpha_bterm{'f; 't1; 't3}} }

interactive bterm_type_type 'H :
   sequent [squash] { 'H >- subtype{'T; term_type} } -->
   sequent ['ext] { 'H >- "type"{bterm_type{'T}} }

(*
 * Elimination form.
 *)
interactive term_type_elim1 'H 'J 'T 'y 'z 'w 'v 'op 'bterms 'terms :
   sequent ['ext] { 'H; x: term_type; 'J['x];
      T: univ[1:l];
      y: subtype{'T; term_type};
      z: (w: 'T -> 'C['w]);
      op: operator_type;
      bterms : list{bterm_type{'T}}
      >- 'C[term{'op; 'bterms}] } -->
   sequent ['ext] { 'H; x: term_type; 'J['x];
      T: univ[1:l];
      y: subtype{'T; term_type};
      z: (w: 'T -> 'C['w]);
      v: var_type;
      terms: list{'T}
      >- 'C[bvar{'v; 'terms}] } -->
   sequent ['ext] { 'H; x: term_type; 'J['x] >- 'C['x] }
*)

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let eq_alpha_term = << eq_alpha{'t1; 't2} >>
let eq_alpha_opname = opname_of_term eq_alpha_term
let mk_eq_alpha_term = mk_dep0_dep0_term eq_alpha_opname
let is_eq_alpha_term = is_dep0_dep0_term eq_alpha_opname
let dest_eq_alpha = dest_dep0_dep0_term eq_alpha_opname

(*
 * Comparison on vars.
 *)
let vmapSymT p =
   (vmap_compare_sym (Sequent.hyp_count_addr p)
    thenLT [addHiddenLabelT "wf";
            addHiddenLabelT "wf";
            addHiddenLabelT "wf";
            addHiddenLabelT "main"]) p

let vmapTransT g t p =
   (vmap_compare_trans (Sequent.hyp_count_addr p) g t
    thenLT [addHiddenLabelT "wf";
            addHiddenLabelT "wf";
            addHiddenLabelT "wf";
            addHiddenLabelT "wf";
            addHiddenLabelT "wf";
            addHiddenLabelT "assertion";
            addHiddenLabelT "assertion";
            addHiddenLabelT "main";
            addHiddenLabelT "main"]) p

(*
 * Equaivalence relation operations.
 *)
let eq_alphaRefT p =
   let concl = Sequent.concl p in
   let t = dest_assert concl in
      if is_eq_alpha_term t then
         (eq_alpha_ref (Sequent.hyp_count_addr p)
          thenT addHiddenLabelT "wf") p
      else
         let v = maybe_new_vars1 p "v" in
            (eq_alpha_term_ref (Sequent.hyp_count_addr p) v
             thenT addHiddenLabelT "wf") p

let eq_alphaSymT p =
   let concl = Sequent.concl p in
   let t = dest_assert concl in
      if is_eq_alpha_term t then
         (eq_alpha_sym (Sequent.hyp_count_addr p)
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  addHiddenLabelT "main"]) p
      else
         (eq_alpha_term_sym (Sequent.hyp_count_addr p)
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  addHiddenLabelT "main"]) p

let eq_alphaTransT t2 p =
   let concl = Sequent.concl p in
   let t = dest_assert concl in
      if is_eq_alpha_term t then
         (eq_alpha_trans (Sequent.hyp_count_addr p) t2
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  addHiddenLabelT "main";
                  addHiddenLabelT "main"]) p
      else
         let g = get_with_arg p in
            (eq_alpha_term_trans (Sequent.hyp_count_addr p) g t2
             thenLT [addHiddenLabelT "wf";
                     addHiddenLabelT "wf";
                     addHiddenLabelT "wf";
                     addHiddenLabelT "wf";
                     addHiddenLabelT "wf";
                     addHiddenLabelT "assertion";
                     addHiddenLabelT "assertion";
                     addHiddenLabelT "main";
                     addHiddenLabelT "main"]) p

(*
 * -*-
 * Local Variables:
 * Caml-master: "mp.run"
 * End:
 * -*-
 *)
