(*
 * Print refine exceptions.
 *)

open Printf

open Debug

open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermAddr
open Refiner.Refiner.TermMeta
open Refiner.Refiner.Rewrite
open Refiner.Refiner.RefineError
open Rformat
open Simple_print
open Dform
open Dform_print

(*
 * Show the file loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Refine_exn%t" eflush

(*
 * Default printer uses the Simple_print.
 *)
type printers =
   { format_term : dform_base -> buffer -> term -> unit;
     format_bterm : dform_base -> buffer -> bound_term -> unit;
     format_param : dform_base -> buffer -> param -> unit;
     format_mterm : dform_base -> buffer -> meta_term -> unit
   }

let simple_printers =
   { format_term = (fun _ t -> format_simple_term t);
     format_bterm = (fun _ t -> format_simple_bterm t);
     format_param = (fun _ t -> format_simple_param t);
     format_mterm = (fun _ t -> format_simple_mterm t);
   }

let dform_printers =
   { format_term = format_term;
     format_bterm = format_bterm;
     format_param = (fun _ p -> format_simple_param p);
     format_mterm = format_mterm
   }

(*
 * Print an address as a list of ints.
 *)
let format_address buf addr =
   format_string buf (string_of_address addr)

(*
 * Just print out a bunch of strings.
 *)
let rec format_strings buf = function
   [h] ->
      format_string buf h
 | h::t ->
      format_string buf h;
      format_space buf;
      format_strings buf t
 | [] ->
      ()

(*
 * Match type in the rewriter.
 *)
let format_match_type db buf printers = function
   ParamMatch p ->
      format_string buf "ParamMatch:";
      format_space buf;
      printers.format_param db buf p
 | VarMatch s ->
      format_string buf "VarMatch:";
      format_space buf;
      format_string buf s
 | TermMatch t ->
      format_string buf "TermMatch:";
      format_space buf;
      printers.format_term db buf t
 | BTermMatch bt ->
      format_string buf "BTermMatch:";
      format_space buf;
      printers.format_bterm db buf bt

(*
 * Print a refinement error.
 *)
let format_refine_error db buf printers name error =
   let rec format indent name error =
      format_newline buf;
      for i = 0 to indent do
         format_char buf ' ';
      done;
      format_string buf name;
      format_string buf ": ";
      match error with
         GenericError ->
            format_string buf "Generic refiner error"
       | StringError s ->
            format_string buf s
       | IntError i ->
            format_int buf i
       | TermError t ->
            printers.format_term db buf t
       | StringIntError (s, i) ->
            format_string buf s;
            format_space buf;
            format_int buf i
       | StringStringError (s1, s2) ->
            format_string buf s1;
            format_space buf;
            format_string buf s2
       | StringTermError (s, t) ->
            format_string buf s;
            format_space buf;
            printers.format_term db buf t
       | GoalError (name, e) ->
            format (indent + 3) name e
       | SecondError (name, e) ->
            format (indent + 3) name e
       | SubgoalError (i, name, e) ->
            format_int buf i;
            format_space buf;
            format (indent + 3) name e
       | PairError (name1, e1, name2, e2) ->
            format (indent + 3) name1 e1;
            format (indent + 3) name2 e2
       | NodeError (s, t, el) ->
            format_string buf s;
            format_space buf;
            printers.format_term db buf t
       | AddressError (addr, t) ->
            format_address buf addr;
            format_space buf;
            printers.format_term db buf t
       | TermMatchError (t, s2) ->
            format_string buf s2;
            format_newline buf;
            printers.format_term db buf t
       | TermPairMatchError (t1, t2) ->
            printers.format_term db buf t1;
            format_newline buf;
            printers.format_term db buf t2
       | MetaTermMatchError mt ->
            printers.format_mterm db buf mt
       | RewriteBoundSOVar s ->
            format_string buf "BoundSoVar:";
            format_space buf;
            format_string buf s
       | RewriteFreeSOVar s ->
            format_string buf "FreeSOVar:";
            format_space buf;
            format_string buf s
       | RewriteSOVarArity s ->
            format_string buf "SOVarArity:";
            format_space buf;
            format_string buf s
       | RewriteBoundParamVar s ->
            format_string buf "BoundParamVar:";
            format_space buf;
            format_string buf s
       | RewriteFreeParamVar s ->
            format_string buf "FreeParamVar:";
            format_space buf;
            format_string buf s
       | RewriteBadRedexParam p ->
            format_string buf "BadRedexParam:";
            format_space buf;
            printers.format_param db buf p
       | RewriteNoRuleOperator ->
            format_string buf "NoRuleOperator"
       | RewriteBadMatch t ->
            format_string buf "BadMatch:";
            format_space buf;
            format_match_type db buf printers t
       | RewriteAllSOInstances s ->
            format_string buf "AllSOInstances:";
            format_space buf;
            format_string buf s
       | RewriteMissingContextArg s ->
            format_string buf "MissingContextArg:";
            format_space buf;
            format_string buf s
       | RewriteStringError s ->
            format_string buf "StringError:";
            format_space buf;
            format_string buf s
       | RewriteAddressError (a, name, e) ->
            format_address buf a;
            format_space buf;
            format (indent + 3) name e
       | RewriteFreeContextVars vars ->
            format_string buf "FreeContextVars: ";
            format_strings buf vars
   in
      format 0 name error

(*
 * Convert an exception to a string.
 *)
let format_exn db buf printers exn =
   let format = function
      RefineError (name, msg) ->
         format_string buf "Refine error:";
         format_space buf;
         format_refine_error db buf printers name msg
    | exn ->
         format_string buf (Printexc.to_string exn)
   in
      format_pushm buf 4;
      format exn;
      format_popm buf

(*
 * Formatting.
 *)
let format_refine_error db buf name error =
   format_refine_error db buf dform_printers name error

let format_exn db buf exn =
   format_exn db buf dform_printers exn

(*
 * Print to a channel.
 *)
let print db f x =
   try f x with
      exn ->
         let buf = new_buffer () in
            format_exn db buf exn;
            format_newline buf;
            print_to_channel 80 buf stderr;
            flush stderr;
            raise exn

let print_exn db out s exn =
   let db = get_mode_base db "prl" in
   let buf = new_buffer () in
      format_szone buf;
      format_pushm buf 4;
      format_string buf s;
      format_space buf;
      format_exn db buf exn;
      format_popm buf;
      format_ezone buf;
      format_newline buf;
      print_to_channel 80 buf out;
      flush out;
      raise exn

(*
 * $Log$
 * Revision 1.4  1998/07/02 18:35:40  jyh
 * Refiner modules now raise RefineError exceptions directly.
 * Modules in this revision have two versions: one that raises
 * verbose exceptions, and another that uses a generic exception.
 *
 * Revision 1.3  1998/07/01 04:37:01  nogin
 * Moved Refiner exceptions into a separate module RefineErrors
 *
 * Revision 1.2  1998/06/12 13:46:59  jyh
 * D tactic works, added itt_bool.
 *
 * Revision 1.1  1998/05/28 15:01:04  jyh
 * Partitioned refiner into subdirectories.
 *
 * Revision 1.6  1998/05/27 15:13:54  jyh
 * Functorized the refiner over the Term module.
 *
 * Revision 1.5  1998/05/18 18:28:10  nogin
 * Removed standardize_apart function, compare_* functions
 *     and BadParamMatch exception
 *
 * Revision 1.4  1998/04/28 18:30:43  jyh
 * ls() works, adding display.
 *
 * Revision 1.3  1998/04/24 02:42:48  jyh
 * Added more extensive debugging capabilities.
 *
 * Revision 1.2  1998/04/21 19:53:59  jyh
 * Upgraded refiner for program extraction.
 *
 * Revision 1.1  1998/04/09 15:26:40  jyh
 * Added strip_mfunction.
 *
 * Revision 1.1  1998/04/08 14:57:33  jyh
 * ImpDag is in mllib.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
