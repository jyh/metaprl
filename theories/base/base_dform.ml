(*
 * Display forms for basic objects.
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

open Printf
open Mp_debug

open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermType
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError
open Dform
open Rformat

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Base_dform%t" eflush

(*
 * Display forms.
 *)
declare bvar{var[v:v]}
declare " "
declare "^"
declare "_"
declare "{"
declare "}"
declare "$"
declare "["
declare "]"
declare ";"
declare "\\"

(*
 * Length of a list.
 *)
declare df_length{'l}
declare df_last{'l}

(*
 * Variables.
 *)
dform var_src_df : mode[src] :: var[v:v] =
   `"'" slot[v:s]

dform var_prl_df : mode[prl] :: var[v:v] =
   slot[v:s]

dform var_tex_df : mode[tex] :: var[v:v] =
   izone `"{\\it " ezone slot[v:s] izone `"\\/}" ezone

(*
dform var_html_df : mode[html] :: var[v:v] =
   izone `"<font color=\"#114466\"><b>" ezone slot[v:s] izone `"</b></font>" ezone
*)
dform var_html_df : mode[html] :: var[v:v] =
   izone `"<b>" ezone slot[v:s] izone `"</b>" ezone

dform so_var1_df : var[v:v]{'x1} = var[v:v] "[" 'x1  "]"

dform so_var2_df : var[v:v]{'x1; 'x2} =
   szone var[v:v] "[" pushm[0] 'x1 ";" space 'x2 popm "]" ezone

dform so_var3_df : var[v:v]{'x1; 'x2; 'x3} =
   szone var[v:v] "[" pushm[0] 'x1 ";"
                       space 'x2 ";"
                       space 'x3 popm "]" ezone

dform so_var4_df : var[v:v]{'x1; 'x2; 'x3; 'x4} =
   szone var[v:v] "[" pushm[0] 'x1 ";"
                       space 'x2 ";"
                       space 'x3 ";"
                       space 'x4 popm "]" ezone

dform so_var5_df : var[v:v]{'x1; 'x2; 'x3; 'x4; 'x5} =
   szone var[v:v] "[" pushm[0] 'x1 ";"
                       space 'x2 ";"
                       space 'x3 ";"
                       space 'x4 ";"
                       space 'x5 popm "]" ezone

dform so_var6_df : var[v:v]{'x1; 'x2; 'x3; 'x4; 'x5; 'x6} =
   szone var[v:v] "[" pushm[0] 'x1 ";"
                       space 'x2 ";"
                       space 'x3 ";"
                       space 'x4 ";"
                       space 'x5 ";"
                       space 'x6 popm "]" ezone

dform so_var7_df : var[v:v]{'x1; 'x2; 'x3; 'x4; 'x5; 'x6; 'x7} =
   szone var[v:v] "[" pushm[0] 'x1 ";"
                       space 'x2 ";"
                       space 'x3 ";"
                       space 'x4 ";"
                       space 'x5 ";"
                       space 'x6 ";"
                       space 'x7 popm "]" ezone

dform so_var8_df : var[v:v]{'x1; 'x2; 'x3; 'x4; 'x5; 'x6; 'x7; 'x8} =
   szone var[v:v] "[" pushm[0] 'x1 ";"
                       space 'x2 ";"
                       space 'x3 ";"
                       space 'x4 ";"
                       space 'x5 ";"
                       space 'x6 ";"
                       space 'x7 ";"
                       space 'x8 popm "]" ezone

dform so_var9_df : var[v:v]{'x1; 'x2; 'x3; 'x4; 'x5; 'x6; 'x7; 'x8; 'x9} =
   szone var[v:v] "[" pushm[0] 'x1 ";"
                       space 'x2 ";"
                       space 'x3 ";"
                       space 'x4 ";"
                       space 'x5 ";"
                       space 'x6 ";"
                       space 'x7 ";"
                       space 'x8 ";"
                       space 'x9 popm "]" ezone

ml_dform bvar_df : bvar{var[v:v]} format_term buf = fun
   term ->
      format_string buf v

(*
 * Rewriting.
 *)
dform rewrite_df : mode["src"] :: "rewrite"{'redex; 'contractum} =
   slot{'redex} `"<-->" slot{'contractum}

dform rewrite_df : mode["prl"] :: "rewrite"{'redex; 'contractum} =
   szone pushm[3] slot{'redex} " " longleftrightarrow " " slot{'contractum} popm ezone

(*
 * For sequents.
 * In the "format" function,
 *    i is the hyp number, if it is known
 *    cflag is true if the last term was a conclusion
 *    t is the term to be printed.
 *)
ml_dform sequent_src_df : "sequent"{'ext; 'seq} format_term buf =
   let rec format_goal goals i len =
      if i <> len then
         begin
            format_string buf (if i = 0 then ">-" else ";");
            format_space buf;
            format_term buf NOParens (SeqGoal.get goals i);
            format_goal goals (i + 1) len
         end
   in
   let rec format_hyp hyps i len =
      if i <> len then
         let _ =
            if i <> 0 then
               format_string buf ";"
         in
         let _ =
            match SeqHyp.get hyps i with
               Hypothesis (v, a) ->
                  format_space buf;
                  format_string buf v;
                  format_string buf ". ";
                  format_term buf NOParens a
             | Context (v, values) ->
                  format_space buf;
                  format_term buf NOParens (mk_so_var_term v values)
         in
            format_hyp hyps (i + 1) len
   in
   let format term =
      let { sequent_args = args;
            sequent_hyps = hyps;
            sequent_goals = goals
          } = explode_sequent term
      in
         format_szone buf;
         format_pushm buf 0;
         format_string buf "sequent {";
         format_hyp hyps 0 (SeqHyp.length hyps);
         format_goal goals 0 (SeqGoal.length goals);
         format_string buf " }";
         format_popm buf;
         format_ezone buf
   in
      format

ml_dform sequent_prl_df : mode["prl"] :: "sequent"{'ext; 'seq} format_term buf =
   let format_arg = function
      [] ->
         ()
    | args ->
         format_string buf "[";
         let rec format = function
            arg::t ->
               format_term buf NOParens arg;
               if t <> [] then
                  format_string buf "; ";
               format t
          | [] ->
               ()
         in
            format args;
            format_string buf "]";
            format_space buf
   in
   let rec format_hyp hyps i len =
      if i <> len then
         let lead = (string_of_int (i + 1)) ^ ". " in
         let _ =
            if i = 0 then
               format_break buf lead ""
            else
               format_break buf lead "; ";
            match SeqHyp.get hyps i with
               Context (v, values) ->
                  (* This is a context hypothesis *)
                  format_term buf NOParens (mk_so_var_term v values)
             | Hypothesis (v, a) ->
                  format_szone buf;
                  format_string buf v;
                  format_string buf ":";
                  format_space buf;
                  format_term buf NOParens a;
                  format_ezone buf
         in
            format_hyp hyps (i + 1) len
   in
   let rec format_goal goals i len =
      if i <> len then
         let a = SeqGoal.get goals i in
            if i = 0 then
               format_break buf "\159 " " \159 "
            else
               format_break buf "; " "\159 ";
            format_term buf NOParens a;
            format_goal goals (i + 1) len
   in
   let format term =
      let { sequent_args = args;
            sequent_hyps = hyps;
            sequent_goals = goals
          } = explode_sequent term
      in
         format_szone buf;
         format_pushm buf 0;
         format_arg (dest_xlist args);
         format_hyp hyps 0 (SeqHyp.length hyps);
         format_goal goals 0 (SeqGoal.length goals);
         format_popm buf;
         format_ezone buf
   in
      format

ml_dform sequent_html_df : mode["html"] :: "sequent"{'ext; 'seq} format_term buf =
   let format_arg = function
      [] ->
         ()
    | args ->
         format_string buf "[";
         let rec format = function
            arg::t ->
               format_term buf NOParens arg;
               if t <> [] then
                  format_string buf "; ";
               format t
          | [] ->
               ()
         in
            format args;
            format_string buf "]";
            format_space buf
   in
   let rec format_hyp hyps i len =
      if i <> len then
         let lead = (string_of_int (i + 1)) ^ ". " in
         let _ =
            if i = 0 then
               format_break buf lead ""
            else
               format_break buf lead "; ";
            match SeqHyp.get hyps i with
               Context (v, values) ->
                  (* This is a context hypothesis *)
                  format_term buf NOParens (mk_so_var_term v values)
             | Hypothesis (v, a) ->
                  format_szone buf;
                  format_string buf v;
                  format_string buf ":";
                  format_space buf;
                  format_term buf NOParens a;
                  format_ezone buf
         in
            format_hyp hyps (i + 1) len
   in
   let rec format_goal goals i len =
      if i <> len then
         let a = SeqGoal.get goals i in
            if i = 0 then
               format_break buf "<i>&#8866;</i> " " <i>&#8866;</i> "
            else
               format_break buf "; " "<i>&#8866;</i> ";
            format_term buf NOParens a;
            format_goal goals (i + 1) len
   in
   let format term =
      let { sequent_args = args;
            sequent_hyps = hyps;
            sequent_goals = goals
          } = explode_sequent term
      in
         format_szone buf;
         format_pushm buf 0;
         format_arg (dest_xlist args);
         format_hyp hyps 0 (SeqHyp.length hyps);
         format_goal goals 0 (SeqGoal.length goals);
         format_popm buf;
         format_ezone buf
   in
      format

ml_dform sequent_prl_df : mode["tex"] :: "sequent"{'ext; 'seq} format_term buf =
   let format_arg = function
      [] ->
         ()
    | args ->
         format_string buf "[";
         let rec format = function
            arg::t ->
               format_term buf NOParens arg;
               if t <> [] then
                  format_string buf "; ";
               format t
          | [] ->
               ()
         in
            format args;
            format_string buf "]";
            format_space buf
   in
   let rec format_hyp hyps i len =
      if i <> len then
         let lead = (string_of_int (i + 1)) ^ ". " in
         let _ =
            if i = 0 then
               format_break buf lead ""
            else
               format_break buf lead "; ";
            match SeqHyp.get hyps i with
               Context (v, values) ->
                  (* This is a context hypothesis *)
                  format_term buf NOParens (mk_so_var_term v values)
             | Hypothesis (v, a) ->
                  format_szone buf;
                  format_string buf v;
                  format_string buf ":";
                  format_space buf;
                  format_term buf NOParens a;
                  format_ezone buf
         in
            format_hyp hyps (i + 1) len
   in
   let rec format_goal goals i len =
      if i <> len then
         let a = SeqGoal.get goals i in
            if i = 0 then
               begin
                  format_izone buf;
                  format_string buf "$\\vdash$";
                  format_ezone buf;
                  format_space buf
               end
            else
               format_break buf "; " "$\\vdash$ ";
            format_term buf NOParens a;
            format_goal goals (i + 1) len
   in
   let format term =
      let { sequent_args = args;
            sequent_hyps = hyps;
            sequent_goals = goals
          } = explode_sequent term
      in
         format_szone buf;
         format_pushm buf 0;
         format_arg (dest_xlist args);
         format_hyp hyps 0 (SeqHyp.length hyps);
         format_goal goals 0 (SeqGoal.length goals);
         format_popm buf;
         format_ezone buf
   in
      format

(*
 * This is a convenient way to print a number.
 *)
ml_dform df_length_df : internal :: df_length{'l} format_term buf = fun term ->
      format_int buf (List.length (dest_xlist (one_subterm term)))

(*
 * Get the last item in a list.
 *)
dform df_last_df1 : internal :: df_last{cons{'a; cons{'b; 'c}}} =
   df_last{cons{'b; 'c}}

dform df_last_df2 : internal :: df_last{cons{'a; nil}} =
   'a

(************************************************************************
 * COMMANDS                                                             *
 ************************************************************************)

dform space_df : internal :: " " = `" "
dform hat_df : internal :: "^" = `"^"
dform underscore_df : internal :: "_" = `"_"
dform left_curly_df : internal :: "{" = `"{"
dform right_curly_df : internal :: "}" = `"}"
dform dollar_df : internal :: "$" = `"$"
dform left_brack_df : internal :: "[" = `"["
dform right_brack_df : internal :: "]" = `"]"
dform semicolor_df : internal :: ";" = `";"
dform newline_df : internal :: "\\" = \newline

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
