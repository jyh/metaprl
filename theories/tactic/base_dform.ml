(*
 * @begin[doc]
 * @module[Dform]
 *
 * The @hrefmodule[Dform] module implements basic display forms for
 * variables and sequents.
 *
 * @docoff
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
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
 * Author: Jason Hickey @email{jyh@cs.caltech.edu}
 * Modified by: Aleksey Nogin @email{nogin@cs.cornell.edu}
 *
 * @end[license]
 *)

(*
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
extends Perv
extends Nuprl_font
(* @docoff *)

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
   show_loading "Loading Base_dform%t"

let debug_dform = load_debug "dform"

(* @terms *)
declare bvar{'v}
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
 * List helper operations.
 *)
declare df_length{'l}
declare df_last{'l}
declare df_concat{'sep;'l}
declare df_rev_concat{'sep;'l}

(* same as "szone 'e ezone" *)
declare szone{'e}
(* @docoff *)

(*
 * @begin[doc]
 * Variables are terms with the opname @tt{var}, and a single @emph{var}
 * parameter.  @emph{Second-order} variables also have (unbound) subterms
 * that correspond to the free variables in the term being represented (in
 * a redex), or terms to be substituted for those variables (in a contractum).
 *
 * Display for mechanism would convert the variable term into a @tt{display_var}
 * term to avoid having to deal with argument lists of arbitrary length.
 *
 * The @tt{tex} mode display form for @tt{display_var} uses some heuristics to split
 * the variable name into the name and the subscript part and is omited from the
 * documentation.
 * @end[doc]
 *)
declare var_list{'t}

dform var_prl_df : mode[prl] :: display_var[v:v]{nil} =
   slot[v:v]

dform var_src_df : mode[src] :: display_var[v:v]{nil} =
   `"'" slot[v:v]

dform var_html_df : mode[html] :: display_var[v:v]{nil} =
   izone `"<font color=\"#114466\"><b>" ezone slot[v:v] izone `"</b></font>" ezone

dform so_var_df : display_var[v:v]{'t} =
   szone display_var[v:v]{nil} `"[" pushm[0] var_list{'t} popm `"]" ezone

dform var_list_df1 : var_list{cons{'a;'b}} =
   'a `";" hspace var_list{'b}

dform var_list_df2 : var_list{cons{'a;nil}} =
   'a

(* @docoff *)

let split_digits s =
   let rec aux i =
      if (i=0) then 0 else
         let i' = pred i in
         if String_util.is_digit(s.[i']) then aux i' else i
   in
      let len = String.length s in
      let i = aux len in
      String.sub s 0 i, String.sub s i (len-i)

let dvar_opname = opname_of_term <<display_var[v:v]{nil}>>

ml_dform var_tex_df : mode[tex] :: display_var[v:v]{nil} format_term buf = fun
   term ->
      let v =
         match (dest_op (dest_term term).term_op).op_params with
            [p] ->
               begin match dest_param p with
                  Var v -> v
                | _ -> raise (Invalid_argument "var_tex_df")
               end
          | _ ->
            raise (Invalid_argument "var_tex_df")
      in match String_util.split '_' v with
         [] ->
            raise (Invalid_argument "var_tex_df: string has an empty name")
       | h::tl ->
            let h,tl =
               if List.for_all (String_util.for_all String_util.is_digit) tl then
                  let hn,hd = split_digits h in
                     if (hn <> "") && (hd <> "") then hn, hd::tl else h,tl
               else
                  h,tl
            in
               format_string buf h;
               if (tl<>[]) then begin
                  format_izone buf;
                  format_string buf "_{";
                  format_ezone buf;
                  format_string buf (String.concat "," tl);
                  format_izone buf;
                  format_string buf "}";
                  format_ezone buf
               end

let bvar_opname = opname_of_term <<bvar{'v}>>

ml_dform bvar_df : bvar{'v} format_term buf = fun
   term ->
      let t = dest_dep0_term bvar_opname term in
         if is_var_term t then
            format_string buf (dest_var t)
         else
            format_term buf LTParens t

(*
 * Rewriting.
 *)

dform rewrite_df2 : "rewrite"{'redex; 'contractum} =
   szone pushm[3] slot{'redex} " " longleftrightarrow " " slot{'contractum} popm ezone

(*
 * For sequents.
 * In the "format" function,
 *    i is the hyp number, if it is known
 *    cflag is true if the last term was a conclusion
 *    t is the term to be printed.
 *)
ml_dform sequent_src_df : mode["src"] :: "sequent"{'ext; 'seq} format_term buf =
   let rec format_goal goals i len =
      if i <> len then
         begin
            format_string buf (if i = 0 then " >-" else ";");
            format_space buf;
            format_term buf NOParens (SeqGoal.get goals i);
            format_goal goals (succ i) len
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
                  format_string buf ": ";
                  format_term buf NOParens a
             | Context (v, values) ->
                  format_space buf;
                  format_term buf NOParens (mk_so_var_term v values)
         in
            format_hyp hyps (succ i) len
   in
   let format term =
      let { sequent_args = args;
            sequent_hyps = hyps;
            sequent_goals = goals
          } = explode_sequent term
      in
         format_szone buf;
         format_pushm buf 0;
         format_string buf "sequent [";
         format_term buf NOParens args;
         format_string buf "] {";
         format_hyp hyps 0 (SeqHyp.length hyps);
         format_goal goals 0 (SeqGoal.length goals);
         format_string buf " }";
         format_popm buf;
         format_ezone buf
   in
      format

(*
 * @begin[doc]
 * The refiner uses a special rewpresentation for sequents that requires the
 * display form to be implemented in ML.
 * @end[doc]
 *)
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
   in
   let rec format_hyp hyps i len =
      if i <> len then
         let lead = (string_of_int (succ i)) ^ ". " in
         let _ =
            if i = 0 then
               format_hbreak buf lead " "
            else
               format_hbreak buf lead "; ";
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
            format_hyp hyps (succ i) len
   in
   let rec format_goal goals i len =
      if i <> len then
         let a = SeqGoal.get goals i in
            if i = 0 then
               format_hbreak buf "\159 " " \159 "
            else
               format_hbreak buf "; " "\159 ";
            format_term buf NOParens a;
            format_goal goals (succ i) len
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
         let hlen = SeqHyp.length hyps in
         if (hlen>0) then format_hyp hyps 0 hlen;
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
   in
   let rec format_hyp hyps i len =
      if i <> len then
         let lead = (string_of_int (succ i)) ^ ". " in
         let _ =
            if i = 0 then
               format_hbreak buf lead " "
            else
               format_hbreak buf lead "; ";
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
            format_hyp hyps (succ i) len
   in
   let rec format_goal goals i len =
      if i <> len then
         let a = SeqGoal.get goals i in
            if i = 0 then begin
               format_hspace buf;
               format_term buf NOParens <<Nuprl_font!vdash>>
            end else
               format_hbreak buf "; " "  ";
            format_term buf NOParens a;
            format_goal goals (succ i) len
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
         let hlen = SeqHyp.length hyps in
         if (hlen>0) then format_hyp hyps 0 hlen;
         format_goal goals 0 (SeqGoal.length goals);
         format_popm buf;
         format_ezone buf
   in
      format

ml_dform sequent_tex_df : mode["tex"] :: "sequent"{'ext; 'seq} format_term buf =
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
   in
   let rec format_hyp hyps i len =
      if i <> len then
         let lead = (string_of_int (succ i)) ^ ". " in
         let _ =
            if i = 0 then
               format_hbreak buf lead " "
            else
               format_hbreak buf lead "; ";
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
            format_hyp hyps (succ i) len
   in
   let rec format_goal goals i len =
      if i <> len then
         let a = SeqGoal.get goals i in
            if i > 0 then
               format_hbreak buf "; " "";
            format_term buf NOParens a;
            format_goal goals (succ i) len
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
         let hlen = SeqHyp.length hyps in
         if (hlen>0) then format_hyp hyps 0 hlen;
         format_hspace buf;
         format_term buf NOParens <<mathmacro["vdash"]>>;
         format_szone buf;
         format_pushm buf 0;
         format_space buf;
         format_goal goals 0 (SeqGoal.length goals);
         format_popm buf;
         format_ezone buf;
         format_popm buf;
         format_ezone buf
   in
      format

(*
 * This is a convenient way to print a number.
 *)
ml_dform df_length_df : internal :: df_length{'l} format_term buf = fun term ->
   try
      format_int buf (List.length (dest_xlist (one_subterm term)))
   with
      RefineError _ ->
         format_string buf "???"

(*
 * Get the last item in a list.
 *)
dform df_last_df1 : internal :: df_last{cons{'a; cons{'b; 'c}}} =
   df_last{cons{'b; 'c}}

dform df_last_df2 : internal :: df_last{cons{'a; nil}} =
   'a

(*
 * List concatenation
 *)
dform df_concat_cons : internal :: df_concat{'sep; cons{'hd; 'tl}} =
   slot{'hd} slot{'sep} df_concat{'sep;'tl}

dform df_concat_nil : internal :: df_concat{'sep; cons{'hd; nil}} =
   slot{'hd}

dform df_concat_nil2 : internal :: df_concat{'sep; nil} =
   `""

(*
 * List rev_concatenation
 *)
dform df_rev_concat_cons : internal :: df_rev_concat{'sep; cons{'hd; 'tl}} =
   df_rev_concat{'sep; 'tl} slot{'sep} slot{'hd}

dform df_rev_concat_nil : internal :: df_rev_concat{'sep; cons{'hd; nil}} =
   slot{'hd}

dform df_rev_concat_nil2 : internal :: df_rev_concat{'sep; nil} =
   `""

(*
 * Perv!bind
 *)
dform bind_df : except_mode[src] :: bind{x. 'T} =
   tt["bind"] `"(" slot{'x} `"." slot{'T} `")"

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
dform semicolon_df : internal :: ";" = `";"
dform newline_df : internal :: "\\" = \newline

dform szone_df : internal :: szone{'e} =
   szone slot{'e} ezone

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
