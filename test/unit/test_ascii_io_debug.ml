(* Ascii_io's reader with its debug flag on (add_items_debug, which
   echoes each entry to stderr as it adds it), which nothing reached
   (2026-11-16 rank): the file test_ascii_io_save writes for
   f{F[a]; sequent { x: a >- G<|H|>[x] }}, read back with the flag off and
   on, as it is, with an entry naming one that does not exist, and with an
   entry under an unknown label.  The outcomes agree with the flag off and
   on (only the refusal's message differs: add_items vs add_items_debug).
   The echoed entries are part of the expected file.
   The expected file is the output of the code as written (2026-11-16),
   never typed. *)
open Term_sig
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
module A = Ascii_io.AsciiIO
module P = Simple_print.SimplePrint

let v = Lm_symbol.add
let op s = Opname.make_opname [ s ]
let c s = mk_simple_term (op s) []
let file = "test_ascii_io_debug.prla"
let lines_of f = let ic = open_in_bin f in
  let rec go acc = match input_line ic with l -> go (l :: acc) | exception End_of_file -> List.rev acc in
  let l = go [] in close_in ic; l
let write_lines f l = let oc = open_out_bin f in List.iter (fun s -> output_string oc s; output_char oc '\n') l; close_out oc
let table_of l = write_lines file l; let ic = open_in_bin file in
  Fun.protect ~finally:(fun () -> close_in ic) (fun () -> A.read_table ic)
let say fmt = Printf.ksprintf (fun s -> print_string s; flush stdout) fmt
let write_fresh t = let oc = open_out_bin file in A.write_term oc (A.initialize ()) t; close_out oc; lines_of file

let seq hyps concl = mk_sequent_term { sequent_args = mk_xlist_term []; sequent_hyps = SeqHyp.of_list hyps; sequent_concl = concl }
let term fa = mk_simple_term (op "f") [ mk_so_var_term (v "F") [] [ fa ];
                                        seq [ Hypothesis (v "x", c "a") ] (mk_so_var_term (v "G") [ v "H" ] [ mk_var_term (v "x") ]) ]
let t1 = term (c "a")
let t2 = term (c "b")

let read_with flag name l =
  say "== read (debug %b): %s\n" flag name;
  Lm_debug.set_debug "ascii_io" flag;
  (match table_of l with
   | exception e -> say "   read_table raised %s\n" (Printexc.to_string e)
   | tbl ->
      match A.get_term tbl with
      | t -> say "   get_term alpha-equal to t1: %b\n" (Refiner.Refiner.TermSubst.alpha_equal t1 t)
      | exception e -> say "   get_term raised %s\n" (Printexc.to_string e));
  Lm_debug.set_debug "ascii_io" false

let edit l old news =
  if List.length (List.filter (( = ) old) l) <> 1 then failwith ("edit: no single line " ^ String.escaped old);
  List.concat_map (fun x -> if x = old then news else [ x ]) l

let () =
  let fresh = write_fresh t1 in
  List.iter (fun flag ->
      read_with flag "the file written fresh" fresh;
      read_with flag "an entry naming another that does not exist" (edit fresh "VF\tF\tF\\\\ \\\\ t" [ "VF\tF\tF\\\\ \\\\ zz" ]);
      read_with flag "an entry with an unknown label" (fresh @ [ "Q\tq\tx" ]))
    [ false; true ]
