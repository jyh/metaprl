(*
 * Display forms for basic objects.
 *)

include Perv
include Nuprl_font

open Printf
open Nl_debug

open Refiner.Refiner
open Refiner.Refiner.Term
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
declare bvar{var[@v:v]}
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
 * Variables.
 *)
dform var_src_df : mode[src] :: var[@v:v] =
   `"'" slot[@v:s]

dform var_prl_df : mode[prl] :: var[@v:v] =
   slot[@v:s]

dform so_var1_df : var[@v:v]{'x1} = var[@v:v] "[" 'x1  "]"

dform so_var2_df : var[@v:v]{'x1; 'x2} =
   szone var[@v:v] "[" pushm[0] 'x1 ";" space 'x2 popm "]" ezone

dform so_var3_df : var[@v:v]{'x1; 'x2; 'x3} =
   szone var[@v:v] "[" pushm[0] 'x1 ";"
                       space 'x2 ";"
                       space 'x3 popm "]" ezone

dform so_var4_df : var[@v:v]{'x1; 'x2; 'x3; 'x4} =
   szone var[@v:v] "[" pushm[0] 'x1 ";"
                       space 'x2 ";"
                       space 'x3 ";"
                       space 'x4 popm "]" ezone

dform so_var5_df : var[@v:v]{'x1; 'x2; 'x3; 'x4; 'x5} =
   szone var[@v:v] "[" pushm[0] 'x1 ";"
                       space 'x2 ";"
                       space 'x3 ";"
                       space 'x4 ";"
                       space 'x5 popm "]" ezone

dform so_var6_df : var[@v:v]{'x1; 'x2; 'x3; 'x4; 'x5; 'x6} =
   szone var[@v:v] "[" pushm[0] 'x1 ";"
                       space 'x2 ";"
                       space 'x3 ";"
                       space 'x4 ";"
                       space 'x5 ";"
                       space 'x6 popm "]" ezone

dform so_var7_df : var[@v:v]{'x1; 'x2; 'x3; 'x4; 'x5; 'x6; 'x7} =
   szone var[@v:v] "[" pushm[0] 'x1 ";"
                       space 'x2 ";"
                       space 'x3 ";"
                       space 'x4 ";"
                       space 'x5 ";"
                       space 'x6 ";"
                       space 'x7 popm "]" ezone

dform so_var8_df : var[@v:v]{'x1; 'x2; 'x3; 'x4; 'x5; 'x6; 'x7; 'x8} =
   szone var[@v:v] "[" pushm[0] 'x1 ";"
                       space 'x2 ";"
                       space 'x3 ";"
                       space 'x4 ";"
                       space 'x5 ";"
                       space 'x6 ";"
                       space 'x7 ";"
                       space 'x8 popm "]" ezone

dform so_var9_df : var[@v:v]{'x1; 'x2; 'x3; 'x4; 'x5; 'x6; 'x7; 'x8; 'x9} =
   szone var[@v:v] "[" pushm[0] 'x1 ";"
                       space 'x2 ";"
                       space 'x3 ";"
                       space 'x4 ";"
                       space 'x5 ";"
                       space 'x6 ";"
                       space 'x7 ";"
                       space 'x8 ";"
                       space 'x9 popm "]" ezone

mldform bvar_df : bvar{var[@v:v]} format_term buf =
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
mldform sequent_src_df : mode["src"] :: "sequent"{'ext; 'seq} format_term buf =
   let rec format_goal goals i len =
      if i <> len then
         begin
            format_string buf (if i = 0 then ">-" else ";");
            format_space buf;
            format_term buf NOParens goals.(i);
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
            match hyps.(i) with
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
   let { sequent_args = args;
         sequent_hyps = hyps;
         sequent_goals = goals
       } = explode_sequent term
   in
      format_szone buf;
      format_pushm buf 0;
      format_string buf "sequent {";
      format_hyp hyps 0 (Array.length hyps);
      format_goal goals 0 (Array.length goals);
      format_string buf " }";
      format_popm buf;
      format_ezone buf

mldform sequent_prl_df : mode["prl"] :: "sequent"{'ext; 'seq} format_term buf =
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
               format_ibreak buf lead ""
            else
               format_break buf lead "; "
         in
         let _ =
            match hyps.(i) with
               Context (v, values) ->
                  (* This is a context hypothesis *)
                  format_term buf NOParens (mk_so_var_term v values)
             | Hypothesis (v, a) ->
                  format_string buf v;
                  format_string buf ": ";
                  format_term buf NOParens a
         in
            format_hyp hyps (i + 1) len
   in
   let rec format_goal goals i len =
      if i <> len then
         let a = goals.(i) in
         let _ =
            if i = 0 then
               format_ibreak buf "   " " \159 "
            else
               format_break buf "; " "\159 "
         in
            format_term buf NOParens a;
            format_goal goals (i + 1) len
   in
   let { sequent_args = args;
         sequent_hyps = hyps;
         sequent_goals = goals
       } = explode_sequent term
   in
      format_szone buf;
      format_pushm buf 0;
      format_arg (dest_xlist args);
      format_hyp hyps 0 (Array.length hyps);
      format_goal goals 0 (Array.length goals);
      format_popm buf;
      format_ezone buf

(************************************************************************
 * COMMANDS                                                             *
 ************************************************************************)

dform space_df : " " = space
dform hat_df : "^" = `"^"
dform underscore_df : "_" = `"_"
dform left_curly_df : "{" = `"{"
dform right_curly_df : "}" = `"}"
dform dollar_df : "$" = `"$"
dform left_brack_df : "[" = `"["
dform right_brack_df : "]" = `"]"
dform semicolor_df : ";" = `";"
dform newline_df : "\\" = \newline

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
