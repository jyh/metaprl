(*
 * Display forms for basic objects.
 *)

include Perv
include Nuprl_font

open Printf
open Debug

open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
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
mldform var_src_df : mode[src] :: var[@v:v] format_term buf =
   format_string buf "'";
   format_string buf v

mldform var_prl_df : mode[prl] :: var[@v:v] format_term buf =
   format_string buf v

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
   slot{'redex} " " longleftrightarrow " " slot{'contractum}

(*
 * For sequents.
 * In the "format" function,
 *    i is the hyp number, if it is known
 *    cflag is true if the last term was a conclusion
 *    t is the term to be printed.
 *)
mldform sequent_src_df : mode["src"] :: "sequent"{'seq} format_term buf =
   (let rec format (i, cflag, sflag, t) =
      let sep = if sflag then "; " else "" in
	 if is_context_term t then
            (* This is a context hypothesis *)
	    let v, subterm, values = dest_context t in
	       format_string buf sep;
	       format_space buf;
	       format_term buf NOParens (mk_so_var_term v values);
	       format (i + 1, cflag, true, subterm)

         else if is_hyp_term t then
            let v, a, b = dest_hyp t in
	       format_string buf sep;
	       format_space buf;
	       format_string buf v;
	       format_string buf ". ";
               format_term buf NOParens a;
               format (i + 1, false, true, b)

         else if t = null_concl then
            ()

         else if is_concl_term t then
            let a, b = dest_concl t in
	       format_string buf (if cflag then sep else " >>");
               format_space buf;
               format_term buf NOParens a;
               format (i + 1, true, true, b)

         else
            raise (Term.TermMatch ("sequent_print", seq, "not a sequent"))
   in
      format_szone buf;
      format_pushm buf 0;
      format_string buf "sequent {";
      format (1, false, false, seq);
      format_string buf " }";
      format_popm buf;
      format_ezone buf)

mldform sequent_prl_df : mode["prl"] :: "sequent"{'seq} format_term buf =
   let rec format (i, cflag, sflag, t) =
      let lead = (string_of_int i) ^ ". " in
      let sep = if sflag then "; " else "" in
      let format_xbreak = if sflag then format_break else format_ibreak in
	 if is_context_term t then
            (* This is a context hypothesis *)
	    let v, subterm, values = dest_context t in
	       format_xbreak buf lead sep;
	       format_term buf NOParens (mk_so_var_term v values);
	       format (i + 1, cflag, true, subterm)

         else if is_hyp_term t then
            let v, a, b = dest_hyp t in
               format_xbreak buf lead sep;
	       format_string buf v;
	       format_string buf ": ";
               format_term buf NOParens a;
               format (i + 1, false, true, b)

         else if t = null_concl then
            ()

         else if is_concl_term t then
            let a, b = dest_concl t in
               format_xbreak buf
	       (if cflag then "   " else "\159  ")
	       (if cflag then sep else " \159 ");
               format_term buf NOParens a;
               format (i + 1, true, true, b)

         else
            format_term buf NOParens t
   in
      format_szone buf;
      format_pushm buf 0;
      format (1, false, false, seq);
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
 *
 * $Log$
 * Revision 1.8  1998/06/01 13:55:35  jyh
 * Proving twice one is two.
 *
 * Revision 1.7  1998/05/28 13:47:12  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.6  1998/05/01 18:43:36  jyh
 * Added raw display.
 *
 * Revision 1.5  1998/04/29 20:53:45  jyh
 * Initial working display forms.
 *
 * Revision 1.4  1998/04/28 18:30:56  jyh
 * ls() works, adding display.
 *
 * Revision 1.3  1998/04/24 19:39:06  jyh
 * Updated debugging.
 *
 * Revision 1.2  1998/04/24 02:43:10  jyh
 * Added more extensive debugging capabilities.
 *
 * Revision 1.1  1997/04/28 15:51:54  jyh
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
 * Revision 1.3  1996/09/02 19:39:45  jyh
 * Semi working package management.
 *
 * Revision 1.2  1996/05/21 02:16:13  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.1  1996/04/11 13:33:25  jyh
 * This is the final version with the old syntax for terms.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
