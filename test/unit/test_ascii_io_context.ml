(* unit-link: filter *)
(* Ascii_io's context hypotheses (the C entries: out_hyp's Context arm,
   add_context, and the C arms of add_items_aux and add_items_debug).  The
   proof census reads them in every theory sequent with a context, with
   the debug flag off; nothing read one with it on (2026-11-18 rank737,
   row 747: the debug reader's G, C and fallback arms).  The sequent
   <H>; x: a; <J<|H|>[x]> >- b is written to a file, the file is
   printed, and it is read back with the flag off and on.
   Read from the output: each context is one C entry naming its variable,
   the contexts it may see and its arguments (J\ H\ t2); the debug reader
   echoes the entries as it adds them, the sequent's S entry not among
   them; both reads give the term back.  The G arm is format 1.0.6
   compatibility (stated: nothing writes G).
   The expected file is the output of the code as written (2026-11-18),
   never typed.  Mutants (2026-11-18, each rebuilt and relinked; an
   identity control unchanged): the plain reader's C refused, the debug
   reader's C refused, a context's list of contexts dropped: 3 of 3 RED.
   The file is removed at the end (the unit tests share one directory). *)
open Term_sig
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
module A = Ascii_io.AsciiIO

let v = Lm_symbol.add
let op s = Opname.make_opname [ s ]
let c s = mk_simple_term (op s) []
let file = "test_ascii_io_context.prla"
let seq hyps concl = mk_sequent_term { sequent_args = mk_xlist_term []; sequent_hyps = SeqHyp.of_list hyps; sequent_concl = concl }
(* <H>; x: a; <J<|H|>[x]> >- b *)
let t = seq [ Context (v "H", [], []); Hypothesis (v "x", c "a"); Context (v "J", [ v "H" ], [ mk_var_term (v "x") ]) ] (c "b")

let lines () = let ic = open_in_bin file in
  let rec go acc = match input_line ic with l -> go (l :: acc) | exception End_of_file -> List.rev acc in
  let l = go [] in close_in ic; l

let () =
  (let oc = open_out_bin file in A.write_term oc (A.initialize ()) t; close_out oc);
  print_endline "== the file";
  List.iter print_endline (lines ());
  List.iter (fun flag ->
      Printf.printf "== read (debug %b)\n%!" flag;
      Lm_debug.set_debug "ascii_io" flag;
      (match let ic = open_in_bin file in Fun.protect ~finally:(fun () -> close_in ic) (fun () -> A.get_term (A.read_table ic)) with
       | t' -> Printf.printf "   alpha-equal: %b\n%!" (Refiner.Refiner.TermSubst.alpha_equal t t')
       | exception e -> Printf.printf "   raised %s\n%!" (Printexc.to_string e));
      flush stderr;
      Lm_debug.set_debug "ascii_io" false)
    [ false; true ];
  (try Sys.remove file with Sys_error _ -> ())
