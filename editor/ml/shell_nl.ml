(*
 * Define the additional grammar for the shell.
 *)

include Nltop

open Printf
open Lexing

open Nl_debug

open Pcaml
open MLast

open Refiner.Refiner.Term
open Refiner.Refiner.RefineError
open Resource
open Rformat

open Filter_ast
open Term_grammar
open Filter_grammar

open Tacticals
open Nltop

(************************************************************************
 * CONSTANTS                                                            *
 ************************************************************************)

(*
 * Version number.
 *)
let version = "1.07.0.1"

module ShellP4 =
struct
   (************************************************************************
    * TYPES                                                                *
    ************************************************************************)

   (*
    * Type of buffered input.
    *)
   type input_buf =
      { mutable buf_index : int;
        mutable buf_buffer : string
      }

   (************************************************************************
    * PRINTERS                                                             *
    ************************************************************************)

   (*
    * This is the current display form database.
    *)
   let df = ref None

   let set_df df' =
      df := df'

   let get_df found notfound =
      match !df with
         Some df ->
            found df
       | None ->
            notfound

   let get_dfbase () =
      match !df with
         Some df ->
            df
       | None ->
            Dform.null_base

   (*
    * Printers.
    *)
   let string_of_term t =
      (get_df Dform.string_of_term Simple_print.string_of_term) t

   (*
    * Use format library for term printing.
    *)
   let print_term t =
      Format.print_string (string_of_term t)

   (************************************************************************
    * QUOTATIONS                                                           *
    ************************************************************************)

   (*
    * Term parsing.
    *)
   let mk_opname_null _ =
      raise (Failure "Shell_p4.mk_opname: no current package")

   let mk_opname_ref = ref mk_opname_null

   let set_mk_opname = function
      Some f ->
         mk_opname_ref := f
    | None ->
         mk_opname_ref := mk_opname_null

   (*
    * Base term grammar.
    *)
   module TermGrammarBefore : TermGrammarSig =
   struct
      let mk_opname loc l =
         try !mk_opname_ref l with
            exn ->
               Stdpp.raise_with_loc loc exn

      (*
       * Term grammar.
       *)
      let gram = Pcaml.gram
      let term_eoi = Grammar.Entry.create gram "term"
      let term = Grammar.Entry.create gram "term"
      let quote_term = Grammar.Entry.create gram "quote_term"
      let mterm = Grammar.Entry.create gram "mterm"
      let singleterm = Grammar.Entry.create gram "singleterm"
      let bound_term = Grammar.Entry.create gram "bound_term"
      let xdform = Grammar.Entry.create gram "xdform"
   end

   (*
    * Extended term grammar.
    *)
   module TermGrammar = MakeTermGrammar (TermGrammarBefore)

   (*
    * String -> string translator.
    *)
                        let term_exp s =
                           let cs = Stream.of_string s in
                           let t = Grammar.Entry.parse TermGrammar.term_eoi cs in
                              build_ml_term (0, 0) t

                        let term_patt s =
                           raise (Failure "Shell_p4.term_patt: not implemented yet")

                        let _ = Quotation.add "term" (Quotation.ExAst (term_exp, term_patt))
                        let _ = Quotation.default := "term"

   (************************************************************************
    * MODULE                                                               *
    ************************************************************************)

   (*
    * Reference to current command set.
    *)
                        let toploop =
                           let rsrc = Nltop.ext_toploop_resource in
                              ref (rsrc.resource_extract rsrc)

   (*
    * Set the module.
    * Collect the toplevel commands to use.
    * Shell commands are always added in.
    *)
                        let set_module name commands =
      let name = String.capitalize name in
      let rsrc =
         try Nltop.get_resource name with
            Not_found ->
               eprintf "Module %s: commands not found%t" name eflush;
               Nltop.ext_toploop_resource
      in
      let rsrc = toploop_add rsrc commands in
         toploop := rsrc.resource_extract rsrc

   (************************************************************************
    * ARGUMENT COLLECTION                                                  *
    ************************************************************************)

   (*
    * -I <dir>
    *)
   let includes = ref []

   let get_includes () =
      !includes

   let add_include dir =
      includes := !includes @ [dir]

   (*
    * Anonymous arguments are rejected.
    *)
   let handle_anon_arg arg =
      raise (Failure ("illegal argument: " ^ arg))

   (*
    * Argument specifications.
    *)
   let spec =
      ["-I", Arg.String add_include, "add an directory to the path for include files"]

   let _ =
      Arg.current := 0;
      Env_arg.parse spec handle_anon_arg "Nuprl-Light toploop"

   (************************************************************************
    * TOPLEVEL                                                             *
    ************************************************************************)

   (*
    * Save the text in the input_buffers during each toplevel read.
    *)
   type info =
      Buffered of (int * int * string) list
    | Filename of string
    | File of in_channel

   let input_info = ref (Buffered [])

   (*
    * Push a new value into the buffer.
    *)
   let push_buffer abs len buf =
      match !input_info with
         Buffered l ->
            input_info := Buffered ((abs, len, buf) :: l)
       | _ ->
            raise (Failure "Shell_p4.push_buffer")

   (*
    * Reset the input to the buffered state
    * with an empty buffer.
    *)
   let reset_input () =
      let _ =
         match !input_info with
            File input ->
               close_in input
          | _ ->
               ()
      in
         input_info := Buffered []

   (*
    * Set the file to read from.
    *)
   let set_file name =
      reset_input ();
      input_info := Filename name

   (*
    * Get the text associated with a location.
    *)
   let get_buffered_text (start, finish) bufs =
      let count = finish - start in
      let s = String_util.create "Shell_p4.get_buffered_text" count in
      let rec collect count = function
         (pos, len, buf) :: t ->
            if start > pos then
               if start + count - pos > len then
                  raise (Failure "collect")
               else
                  String_util.blit "Shell_p4.get_buffered_text" buf (start - pos) s 0 count
            else if start + count > pos then
               let amount = start + count - pos in
                  if amount > len then
                     raise (Failure "collect")
                  else
                     begin
                        String_util.blit "Shell_p4.get_buffered_text" buf 0 s (pos - start) amount;
                        collect (count - amount) t
                     end
            else
               collect count t
       | [] ->
            if count <> 0 then
               raise (Failure "collect")
      in
         try
            collect count bufs;
            s
         with
            Failure "collect" ->
               eprintf "Can't recover input, characters (%d, %d)%t" start finish eflush;
               raise (Failure "get_text")

   (*
    * Get the text from the file.
    *)
   let get_file_text (start, finish) input =
      let buf = String_util.create "Shell_p4.get_file_text" (finish - start) in
         try
            seek_in input start;
            really_input input buf 0 (finish - start);
            buf
         with
            End_of_file ->
               eprintf "Can't recover input, characters (%d, %d)%t" start finish eflush;
               raise (Failure "get_file_text")

   (*
    * Get the text from the input.
    *)
   let get_text loc =
      match !input_info with
         Buffered bufs ->
            get_buffered_text loc bufs
       | Filename name ->
            begin
               try
                  let input = open_in name in
                     input_info := File input;
                     get_file_text loc input
               with
                  Sys_error _ ->
                     let start, finish = loc in
                        eprintf "Can't recover input, file %s, characters (%d, %d)%t" name start finish eflush;
                        raise (Failure "get_text")
            end
       | File input ->
            get_file_text loc input

   (*
    * Create an empty buffer.
    *)
   let create_buffer () =
      { buf_index = 0; buf_buffer = "" }

   (*
    * Wrap the input channel so that we can recover input.
    *)
   let stream_of_channel inx =
      let buf = create_buffer () in
      let refill loc =
         let str = input_line inx ^ "\n" in
            buf.buf_index <- 0;
            buf.buf_buffer <- str;
            push_buffer loc (String.length str) str
      in
      let rec read loc =
         let { buf_index = index; buf_buffer = buffer } = buf in
            if index = String.length buffer then
               try
                  refill loc;
                  read loc
               with
                  End_of_file ->
                     None
            else
               let c = buffer.[index] in
                  buf.buf_index <- index + 1;
                  Some c
      in
         reset_input ();
         Stream.from read

   (************************************************************************
    * TACTIC SAVING                                                        *
    ************************************************************************)

   (*
    * We save the tactic and its text to be passed to the refiner.
    *)
   let saved_tactic = ref ("\"no saved tactic\"",
                           let loc = (0, 0) in
                              <:expr< $str: "no saved tactic"$ >>)

   let set_tactic s e =
      saved_tactic := (s, e)

   let get_tactic () =
      !saved_tactic

   (************************************************************************
    * COMPILING TACTICS                                                    *
    ************************************************************************)

   (*
    * Evaluate a tactic through the toploop resource.
    *)
   let eval_tactic expr =
      match expr_of_ocaml_expr !toploop expr with
         TacticExpr tac ->
            tac
       | _ ->
            raise (RefineError ("eval_tactic", StringError "expression is not a tactic"))

   (************************************************************************
    * SHELL GRAMMAR                                                        *
    ************************************************************************)

   module Unit =
   struct
   end

   module Infix = MakeFilterGrammar (Unit)

   EXTEND
      GLOBAL: str_item;

      str_item:
         [[ "refine"; e = refine_item ->
             let e = <:expr< $lid:"refine"$ $e$ >> in
                <:str_item< $exp: e$ >>
          ]];

      refine_item:
         [[ e = expr ->
             set_tactic (get_text loc) e;
             e
          ]];
   END

   (************************************************************************
    * TOPLOOP                                                              *
    ************************************************************************)

   let rec print_expr out = function
      UnitExpr () ->
         fprintf out "() : unit\n"
    | BoolExpr b ->
         fprintf out "%b : bool\n" b
    | IntExpr i ->
         fprintf out "%d : int\n" i
    | StringExpr s ->
         fprintf out "%s : string\n" s
    | TermExpr t ->
         print_term t
    | TacticExpr _ ->
         fprintf out "- : tactic\n"
    | ConvExpr _ ->
         fprintf out "-: conv\n"
    | ListExpr l ->
         fprintf out "[%a] : list\n" print_expr_list l
    | TupleExpr l ->
         fprintf out "(%a) : tuple\n" print_expr_list l
    | FunExpr _ ->
         fprintf out "- : expr -> expr\n"
    | UnitFunExpr _ ->
         fprintf out "- : unit -> expr\n"
    | BoolFunExpr _ ->
         fprintf out "- : bool -> expr\n"
    | IntFunExpr _ ->
         fprintf out "- : int -> expr\n"
    | StringFunExpr _ ->
         fprintf out "- : string -> expr\n"
    | TermFunExpr _ ->
         fprintf out "- : term -> expr\n"
    | TacticFunExpr _ ->
         fprintf out "- : tactic -> expr\n"
    | IntTacticFunExpr _ ->
         fprintf out "- : (int -> tactic) -> tactic\n"
    | ConvFunExpr _ ->
         fprintf out "- : conv -> expr\n"
    | AddrFunExpr _ ->
         fprintf out "- : address -> expr\n"
    | StringListFunExpr _ ->
         fprintf out "- : string list -> expr\n"
    | TermListFunExpr _ ->
         fprintf out "- : term list -> expr\n"
    | TacticListFunExpr _ ->
         fprintf out "- : tactic list -> expr\n"
    | ConvListFunExpr _ ->
         fprintf out "- : conv list -> expr\n"

   and print_expr_list out = function
      [expr] ->
         print_expr out expr
    | expr :: exprs ->
         fprintf out "%a; %a" print_expr expr print_expr_list exprs
    | [] ->
         ()

   (*
    * Evaluate a struct item.
    *)
   let eval_str_item loc item =
      print_expr stdout (expr_of_ocaml_str_item !toploop item);
      flush stdout

   (*
    * Evaluate a directive.
    *)
   let eval_directive loc str = function
      DpNon ->
         eprintf "Directive DpNon: %s%t" str eflush
    | DpStr str' ->
         eprintf "Directive DpStr: %s/%s%t" str str' eflush
    | DpInt str' ->
         eprintf "Directive DpInt: %s/%s%t" str str' eflush
    | DpIde strs ->
         eprintf "Directive DpIde: %s" str;
         List.iter (fun s -> eprintf "/%s" s) strs;
         eflush stderr

   (*
    * Evaluate a toplevel phrase.
    *)
   let eval_phrase = function
      PhStr (loc, item) ->
         eval_str_item loc item
    | PhDir (loc, str, param) ->
         eval_directive loc str param

   (*
    * We just loop on the input.  Evaluation is performed by
    * the toploop resource.
    *)
   let main () =
      let instream = stream_of_channel stdin in
         printf "Nuprl-Light %s\n%t" version eflush;
         while true do
            output_string stdout "# ";
            flush stdout;
            try
               match Grammar.Entry.parse Pcaml.top_phrase instream with
                  Some phrase ->
                     eval_phrase phrase
                | None ->
                     exit 0
            with
               Stdpp.Exc_located ((start, finish), exn) ->
                  let df = get_dfbase () in
                  let buf = new_buffer () in
                     format_string buf "chars ";
                     format_int buf start;
                     format_string buf "-";
                     format_int buf finish;
                     format_string buf ": ";
                     Filter_exn.format_exn df buf exn;
                     print_to_channel 80 buf stderr;
                     eflush stderr
             | exn ->
                  let df = get_dfbase () in
                  let buf = new_buffer () in
                     format_string buf "uncaught exception: ";
                     Filter_exn.format_exn df buf exn;
                     print_to_channel 80 buf stderr;
                     eflush stderr
         done
end

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
