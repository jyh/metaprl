(*
 * These are the declares for the terms in a Filter_summary.summary_item.
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
 *)

include Perv
include Nuprl_font
include Base_dform
include Ocaml_df

open Printf
open Mp_debug

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Summary%t" eflush

(************************************************************************
 * HTML                                                                 *
 ************************************************************************)

declare package_link[name:s]

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "interface"{'intf}
declare "implementation"{'impl}
declare "location"[start:n, finish:n]{'body}

declare "rewrite"[name:s]{'redex; 'contractum; 'proof}
declare "cond_rewrite"[name:s]{'params; 'args; 'redex; 'contractum; 'proof}
declare "axiom"[name:s]{'stmt; 'proof}
declare "rule"[name:s]{'params; 'stmt; 'proof}
declare "opname"[name:s]{'term}
declare "mlterm"{'term; 'cons; 'oexpr}
declare "condition"{'term; 'cons; 'oexpr}
declare "mlrewrite"[name:s]{'params; 'redex; 'contracta; 'body; 'resources}
declare "parent"{'path; 'opens; 'resources}
declare "module"[name:s]{'info}
declare "dform"{'modes; 'redex; 'def}
declare "prec"[name:s]
declare "prec_rel"[pr:s]
declare "id"[n:n]
declare "resource"[name:s]{'extract; 'improve; 'data}
declare "infix"[name:s]
declare "magic_block"[name:s]{'items}
declare "summary_item"{'term}
declare "resource_defs"{'res}

declare "inherit_df"
declare "prec_df"[name:s]
declare "parens_df"
declare "mode_df"[mode:s]

declare "df_none"
declare "df_term"{'t}
declare "df_ml"[printer:s, buffer:s]{'contracta; 'code}

declare "none"
declare "some"{'t}

declare "meta_theory"{'A}
declare "meta_theorem"{'A}
declare "meta_implies"{'A; 'B}
declare "meta_function"{'arg; 'A; 'B}
declare "meta_iff"{'A; 'B}
declare "meta_labeled"[label:s]{'meta}

declare "context_param"[name:s]
declare "var_param"[name:s]
declare "term_param"{'t}

(* Arguments *)
declare "int_arg"[i:n]
declare "term_arg"{'t}
declare "type_arg"{'t}
declare "bool_arg"[s:t]
declare "string_arg"[s:s]
declare "subst_arg"{'t}
declare "term_list_arg"{'t}
declare "arglist"{'t}

(* Proofs *)
declare "interactive"{'t}

declare "href"[command:s]{'t}

declare "status_bad"
declare "status_partial"
declare "status_asserted"
declare "status_complete"
declare "status"{'sl}

declare "goal_status"{'sl}
declare "goal_label"[s:s]
declare "goal_list"{'goals}
declare "goal"{'status; 'label; 'assums; 'goal}
declare "subgoals"{'subgoals; 'extras}
declare "rule_box"[text:s]
declare "proof"{'main; 'goal; 'text; 'subgoals}

(* Packages *)
declare "package"[name:s]
declare "packages"{'pl}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

(*
 * Modes.
 *)
declare dform_modes{'l}

dform dform_modes_df1 : dform_modes{cons{'hd; 'tl}} =
   slot{'hd} " " keyword["::"] " " dform_modes{dform_modes; 'tl}

dform dform_modes_df2 : internal :: dform_modes{dform_modes; cons{'hd; 'tl}} =
   slot{'hd} " " keyword["::"] " " dform_modes{dform_modes; 'tl}

dform dform_modes_df3 : internal :: dform_modes{nil} =
   `""

dform dform_modes_df3 : internal :: dform_modes{dform_modes; nil} =
   `""

(*
 * Space the items.
 *)
declare space_list{'l}

dform space_list_df1 : internal :: space_list{cons{'hd; cons{'tl1; 'tl2}}} =
   slot{'hd} " " space_list{cons{'tl1; 'tl2}}

dform space_list_df2 : internal :: space_list{cons{'hd; nil}} =
   slot{'hd}

dform space_list_df2 : internal :: space_list{nil} =
   `""

(*
 * Interface just declares it.
 *)
declare lines{'e}

dform lines_nil_df : internal :: lines{nil} =
   `""

dform lines_cons_df : internal :: lines{cons{'e1; 'e2}} =
   newline szone slot{'e1} ezone lines{'e2}

dform interface_df : "interface"{'body} =
   szone pushm[0]
   info["Interface:"] newline
   pushm[4] info["begin"] lines{'body} popm newline
   info["end"] newline
   popm ezone

dform implementation_df : "implementation"{'body} =
   szone pushm[0]
   info["Implementation:"] newline
   pushm[4] info["begin"] lines{'body} popm newline
   info["end"] newline
   popm ezone

dform location_df : "location"[start:n, finish:n]{'body} =
   slot{'body}

(*
 * Display a simple rewrite.
 *)
dform rewrite_df : "rewrite"[name:s]{'redex; 'contractum; 'proof; 'res} =
   szone pushm[4]
   slot{'proof} info[" rewrite"] " " slot[name:s] `" :" hspace slot{'res} slot{'redex} " " longleftrightarrow hspace slot{'contractum}
   popm ezone

(*
 * Resource annotations
 *)
declare res_def_list{'res}
declare resources{'resources}

dform resources_nil_df : internal :: resources{nil} =
   `""

dform resources_cons_df : internal :: resources{cons{'h; 't}} =
   szone keyword["{|"] pushm res_def_list{cons{'h; 't}} popm keyword["|} "] ezone

dform res_def_list_df1 : internal :: res_def_list{cons{'a; nil}} =
   slot{'a}

dform res_def_list_df2 : internal :: res_def_list{cons{'a; 'b}} =
   slot{'a} keyword[";"] hspace res_def_list{'b}

dform resource_defs_df1 : resource_defs[name:s]{'args} =
   slot[name:s] " " slot{'args}

dform resource_defs_dfs : internal :: resource_defs[start:n, finish:n, name:s]{'args} =
   resource_defs[name:s]{'args}

(*
 * A conditional rewrite requires special handling of the params.
 *)
dform context_param_df : "context_param"[name:s] =
   slot[name:s]

dform var_param_df : "var_param"[name:s] =
   slot[name:s]

dform term_param_df : "term_param"{'t} =
   szone pushm[4]
   slot{'t}
   popm ezone

dform cond_rewrite_df : "cond_rewrite"[name:s]{'params; 'args; 'redex; 'contractum; 'proof; 'res} =
   szone pushm[4]
   slot{'proof} info[" rewrite"] " " slot[name:s] " " resources{'res} slot{'params} keyword[" :"] " " slot{'args}
   " " longrightarrow slot{'redex} longleftrightarrow slot{'contractum}
   popm ezone

dform axiom_df : "axiom"[name:s]{'stmt; 'proof; 'res} =
   szone pushm[4]
   slot{'proof} info[" rule"] " " slot[name:s] `" " resources{'res} `": : " slot{'stmt}
   popm ezone

dform rule_df : "rule"[name:s]{'params; 'stmt; 'proof; 'res} =
   szone pushm[4]
   slot{'proof} info[" rule"] " " slot[name:s] " " resources{'res} space_list{'params} `":" hspace slot{'stmt}
   ezone popm

dform opname_df : "opname"[name:s]{'term} =
   szone pushm[4]
   info["declare"] " " slot["raw"]{'term}
   ezone popm

dform mlterm_df : "mlterm"{'term; 'cons; 'oexpr} =
   szone pushm[4]
   info["mlterm"] " " slot{'term}
   ezone popm

dform condition_df : "condition"{'term; 'cons; 'oexpr} =
   szone pushm[4]
   info["condition"] " " slot{'term}
   ezone popm

dform mlrewrite_df1 : "mlrewrite"[name:s]{'params; 'redex; 'contracta; 'body; 'res} =
   szone pushm[4]
   info["mlrewrite"] " " slot[name:s] " " resources{'res} space_list{'params} `":" hspace
   slot{'redex} keyword["="] slot{'body}
   popm ezone

(*
 * Parent path is separated by dots.
 *)
declare path{'t}
declare begin_cd{'t}
declare cdinternal{'t}
declare end_cd

dform begin_cd_df1 : internal :: begin_cd{'path} =
   izone `"<a href=\"http://cd.metaprl.local//" cdinternal{'path}

dform cd_internal_df1 : internal :: cdinternal{cons{."parent"[name:s]; cons{'n2; 'n3}}} =
   slot[name:s] `"/" cdinternal{cons{'n2; 'n3}}

dform cd_internal_df2 : internal :: cdinternal{cons{."parent"[name:s]; nil}} =
   slot[name:s] cdinternal{nil}

dform cd_internal_df3 : internal :: cdinternal{nil} =
   `"\">" ezone

dform end_cd_df1 : internal :: end_cd =
   izone `"</a>" ezone

dform path_parent_nil_df : internal :: path{cons{."parent"[name:s]; nil}} =
   slot[name:s]

dform path_parent_cons_df : internal :: path{cons{."parent"[name:s]; .cons{'n1; 'n2}}} =
   slot[name:s] keyword["."] cons{'n1; 'n2}

dform parent_df : "parent"{'path; 'opens; 'resources} =
   info["include"] " " begin_cd{'path} path{'path} end_cd

(*
 * Nested module is indented.
 *)
dform module_df : "module"[name:s]{'info} =
   szone pushm[4]
   info["module"] " " slot[name:s] `" = " break slot{'info}
   ezone popm

dform dform_df : "dform"[name:s]{'modes; 'redex; 'def} =
   szone pushm[4]
   info["dform"] " " slot[name:s]
   " " keyword[": "] dform_modes{'modes} slot["raw"]{'redex}
   " " keyword["="] hspace pushm slot{'def} popm
   ezone popm

(*
 * Precedence relations.
 *)
declare "rel"{'op}

dform rel_lt_df : internal :: "rel"["lt"] = keyword["<"]
dform rel_eq_df : internal :: "rel"["eq"] = keyword["="]
dform rel_gt_df : internal :: "rel"["gt"] = keyword[">"]

dform prec_df : "prec"[name:s] =
   info["prec"] " " slot[name:s]

dform prec_rel_df : cons{prec_rel[op]; cons{prec_rel[left]; cons{prec_rel[right]; nil}}} =
   info["prec "] slot[left] `" " "rel"[op] `" " slot[right]

dform id_df : "id"[n:n] =
   info["Id: "] slot[n:s]

dform resource_df : "resource"[name]{'extract; 'improve; 'data; 'arg} =
   szone
   info["resource"] " " slot[name:s]
   keyword["("] pushm[0]
                'extract keyword[";"] hspace
                'improve keyword[";"] hspace
                'data keyword[";"] hspace
                'arg keyword[")"]
                popm
   ezone

dform infix_df : "infix"[name] =
   info["infix"] " " slot[name:s]

dform magic_block_df : "magic_block"[name:s]{'items} =
   info["magic_block"] " " slot[name:s] keyword[" ="] space slot{'items}

dform summary_item_df : "summary_item"{'term} =
   slot{'term}

dform df_term_df : df_term{'t} =
   slot{'t}

dform meta_theorem_df : meta_theorem{'A} =
   slot{'A}

dform meta_implies_df : meta_implies{'A; 'B} =
   slot{'A} " " longrightarrow hspace slot{'B}

dform meta_function_df : meta_function{'arg; 'A; 'B} =
   szone pushm[0] slot{'arg} keyword[": "] slot{'A} `" " popm ezone longrightarrow hspace slot{'B}

dform meta_labeled_df : meta_labeled[label:s]{'A} =
   keyword["[\""] slot[label] keyword["\"] "] slot{'A}

dform mode_df : mode_df[s:s] =
   keyword["mode["] slot[s:s] keyword["]"]

dform prec_df : prec_df[s:s] =
   keyword["prec["] slot[s:s] keyword["]"]

dform parens_df : parens_df =
   keyword["parens"]

(*
 * Packages.
 *)
declare packages_df

dform packages_df1 : internal :: packages{'packages} =
   szone pushm[0] pushm[4] info["Root theories:"] hspace
       packages_df{'packages} popm hspace
   info["end"] popm ezone

dform packages_df2 : internal :: packages_df{cons{package[name:s]; 'next}} =
   info["module "] cd_begin[name:s] slot[name:s] cd_end hspace packages_df{'next}

dform packages_df3 : internal :: packages_df{nil} =
   `""

(********************************
 * Argument lists
 *)
dform int_arg_df : internal :: int_arg[i:n] =
   slot[i:s]

dform term_arg_df : internal :: term_arg{'t} =
   't

dform type_arg_df : internal :: type_arg{'t} =
   't

dform bool_arg_df : internal :: bool_arg[s:t] =
   slot[s:s]

dform string_arg_df : internal :: string_arg[s:s] =
   slot[s:s]

dform subst_arg_df : internal :: subst_arg{'t} =
   't

dform term_list_arg_df : internal :: term_list_arg{'terms} =
   space_list{'terms}

dform arglist_df1 : internal :: arglist{'args} =
   szone pushm space_list{'args} popm ezone

(********************************
 * Proofs.
 *)
declare msequent
declare goals_df
declare goal_list_status

dform proof_df : internal :: proof{'main; goal_list{'goal}; 'text; 'subgoals} =
   szone pushm pagebreak goals_df{'main; 'goal} 'text 'subgoals popm ezone

dform goals_df : internal :: goals_df{goal{'status; 'label; 'assums; 'goal}; 'cache} =
   'status `"[" goal_list_status{'cache} `"]" newline 'label msequent{'assums; 'goal}

dform goal_list_status_df1 : internal :: goal_list_status{cons{goal{goal_status{'status}; 'label; 'assums; 'goal}; cons{'hd; 'tl}}} =
   df_last{'status} `" " goal_list_status{cons{'hd; 'tl}}

dform goal_list_status_df2 : internal :: goal_list_status{cons{goal{goal_status{'status}; 'label; 'assums; 'goal}; nil}} =
   df_last{'status}

(*
 * Display the meta-sequent.
 *)
declare numbered_assums

dform msequent_df1 : internal :: msequent{nil; 'goal} =
   'goal newline

dform msequent_df2 : internal :: msequent{'assums; 'goal} =
   numbered_assums{cons{nil; nil}; 'assums} 'goal newline

dform numbered_assums_df1 : internal :: numbered_assums{'number; cons{'a; 'b}} =
   szone df_length{'number} `". " pushm 'a popm newline ezone numbered_assums{cons{nil; 'number}; 'b}

dform numbered_assums_df2 : internal :: numbered_assums{'number; nil} =
   `"====" newline

(*
 * Status line includes commands to move up the tree.
 *)
declare goal_status_cd
declare goal_cd_dot
declare goal_cd_up
declare goal_cd_begin
declare goal_cd_middle
declare goal_cd_end

dform status_df2 : internal :: goal_status{nil} = `""

dform status_df1 : internal :: goal_status{cons{'a; 'b}} =
   goal_status{cons{'a; nil}; 'b}

dform status_df3 : internal :: goal_status{'l; cons{'a; 'b}} =
   goal_status{cons{'a; 'l}; 'b}

dform status_df4 : internal :: goal_status{'l; nil} =
   goal_status_cd{goal_cd_dot; 'l}

dform status_df5 : internal :: goal_status_cd{'cd; cons{'a; 'b}} =
   goal_status_cd{cons{goal_cd_up; 'cd}; 'b} goal_cd_begin{'cd} 'a `" " goal_cd_end

dform status_df5b : internal :: goal_status_cd{'cd; nil} =
   `""

dform status_df6 : internal :: goal_cd_begin{'cd} =
   izone `"<a href=\"cd.metaprl.local/" goal_cd_middle{'cd}

dform status_df7 : internal :: goal_cd_middle{goal_cd_dot} =
   `".\">" ezone

dform status_df8 : internal :: goal_cd_middle{cons{goal_cd_up; 'cd}} =
   `"/.." goal_cd_middle{'cd}

dform status_df9 : internal :: goal_cd_end =
   izone `"</a>" ezone

(*
 * Label is printed with surrounding dots.
 *)
dform label_df : internal :: goal_label[name:s] =
   `"...." slot[name:s] `"...." newline

dform status_bad_df : status_bad =
   keyword["-"]

dform status_partial_df : status_partial =
   keyword["#"]

dform status_asserted_df : status_asserted =
   keyword["!"]

dform status_complete : status_complete =
   keyword["*"]

(*
 * Rule box.
 *)
dform rule_box_df1 : internal :: rule_box[text:s] =
   newline szone info["BY "] pushm slot[text:s] popm ezone

dform rule_box_df2 : internal :: rule_box{'t} =
   newline szone info_begin `"BY [" pushm 't `"]" popm ezone info_end

(*
 * Subgoals are printed in simplified form.
 *)
declare child_df

dform subgoals_df1 : internal :: subgoals{'children; 'extras} =
   newline subgoals{cons{nil; nil}; 'children; 'extras}

dform subgoals_df2 : internal :: subgoals{'number; cons{'child; 'tl}; 'extras} =
   newline child_df{'number; 'child} subgoals{cons{nil; 'number}; 'tl; 'extras}

dform subgoals_df3 : internal :: subgoals{'number; nil; cons{'a; 'b}} =
   newline info["===="] newline subgoals{'number; cons{'a; 'b}; nil}

dform subgoals_df4 : internal :: subgoals{'number; cons{goal{goal_status{'status}; 'label; 'assums; 'goal}; 'tl}; nil} =
   szone info_begin df_length{'number} `". " pushm df_last{'status} info_end newline 'label 'goal popm ezone newline
   subgoals{cons{nil; 'number}; nil; 'tl}

dform subgoals_df5 : internal :: subgoals{'number; nil; nil} =
   `""

dform child_df1 : internal :: child_df{'number; goal_list{'child}} =
   szone info_begin df_length{'number} `". " pushm `"[" goal_list_status{'child} `"]" info_end newline child_df{'child} popm ezone

dform child_df2 : internal :: child_df{cons{goal{'status; 'label; 'assums; 'goal}; 'tl}} =
   'label 'goal

(************************************************************************
 * ML INTERFACE                                                         *
 ************************************************************************)

let interface_term = << "interface"{'intf} >>
let interface_opname = opname_of_term interface_term
let mk_interface_term tl =
   mk_dep0_term interface_opname (mk_xlist_term tl)

let implementation_term = << "implementation"{'impl} >>
let implementation_opname = opname_of_term implementation_term
let mk_implementation_term tl =
   mk_dep0_term implementation_opname (mk_xlist_term tl)

let package_term = << "package"[name:s] >>
let package_opname = opname_of_term package_term
let mk_package_term = mk_string_term package_opname

let packages_term = << "packages"{'pl} >>
let packages_opname = opname_of_term packages_term
let mk_packages_term tl =
   mk_simple_term packages_opname [mk_xlist_term tl]

let href_term = << "href"[s:s] >>
let href_opname = opname_of_term href_term
let mk_href_term = mk_string_dep0_term href_opname

let status_bad_term = << "status_bad" >>
let status_partial_term = << "status_partial" >>
let status_asserted_term = << "status_asserted" >>
let status_complete_term = << "status_complete" >>

let status_term = << "goal_status"{'sl} >>
let status_opname = opname_of_term status_term
let mk_status_term tl =
   mk_simple_term status_opname [mk_xlist_term tl]

let goal_label_term = << "goal_label"[s:s] >>
let goal_label_opname = opname_of_term goal_label_term
let mk_goal_label_term s =
   mk_string_term goal_label_opname s

let mk_labeled_goal_term label goal =
   mk_simple_term goal_label_opname [label; goal]

let goal_term = << "goal"{'status; 'label; 'assums; 'goal} >>
let goal_opname = opname_of_term goal_term
let mk_goal_term status label assums goal =
   mk_simple_term goal_opname [status; label; mk_xlist_term assums; goal]

let goal_list_term = << "goal_list"{'goals} >>
let goal_list_opname = opname_of_term goal_list_term
let mk_goal_list_term goals =
   mk_simple_term goal_list_opname [mk_xlist_term goals]

let subgoals_term = << "subgoals"{'subgoals; 'extras} >>
let subgoals_opname = opname_of_term subgoals_term
let mk_subgoals_term subgoals extras =
   mk_simple_term subgoals_opname [mk_xlist_term subgoals; mk_xlist_term extras]

let rule_box_term = << "rule_box"[s:s] >>
let rule_box_opname = opname_of_term rule_box_term
let mk_rule_box_string_term s =
   mk_string_term rule_box_opname s
let mk_rule_box_term t =
   mk_simple_term rule_box_opname [t]

let proof_term = << "proof"{'main; 'goal; 'text; 'subgoals} >>
let proof_opname = opname_of_term proof_term
let mk_proof_term main goal text subgoals =
   mk_simple_term proof_opname [main; goal; text; subgoals]
let dest_proof = four_subterms

let int_arg_term = << "int_arg"[i:n] >>
let int_arg_opname = opname_of_term int_arg_term
let mk_int_arg_term i =
   mk_number_term int_arg_opname (Mp_num.Int i)

let term_arg_term = << "term_arg"{'t} >>
let term_arg_opname = opname_of_term term_arg_term
let mk_term_arg_term t =
   mk_simple_term term_arg_opname [t]

let type_arg_term = << "type_arg"{'t} >>
let type_arg_opname = opname_of_term type_arg_term
let mk_type_arg_term t =
   mk_simple_term type_arg_opname [t]

let bool_arg_term = << "bool_arg"[s:t] >>
let bool_arg_opname = opname_of_term bool_arg_term
let mk_bool_arg_term b =
   mk_string_term bool_arg_opname (if b then "true" else "false")

let string_arg_term = << "string_arg"[s:s] >>
let string_arg_opname = opname_of_term string_arg_term
let mk_string_arg_term s =
   mk_string_term string_arg_opname s

let subst_arg_term = << "subst_arg"{'t} >>
let subst_arg_opname = opname_of_term subst_arg_term
let mk_subst_arg_term t =
   mk_simple_term subst_arg_opname [t]

let term_list_arg_term = << "term_list_arg"{'t} >>
let term_list_arg_opname = opname_of_term term_list_arg_term
let mk_term_list_arg_term tl =
   mk_simple_term term_list_arg_opname [mk_xlist_term tl]

let arglist_term = << "arglist"{'t} >>
let arglist_opname = opname_of_term arglist_term
let mk_arglist_term tl =
   mk_simple_term arglist_opname [mk_xlist_term tl]

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
