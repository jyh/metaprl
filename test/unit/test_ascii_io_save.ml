(* Ascii_io's save path for second-order variables and sequents: what
   write_term writes against a table read from an existing file, as the
   filter does when it saves a proof over the old .prla
   (filter/base/filter_cache.ml).  test_ascii_io_compat covers the save of
   plain terms; no test, theory build or proof replay reached out_term's
   reuse of an old V (second-order variable) or S (sequent) entry, its
   conversions of the old formats (an S/G pair, <= 1.0.6; a variable entry
   under another label, <= 1.0.7), or print_out's arms for them (bisect at
   c013b0579 and 008a9607e).

   The term is f{F[a]; sequent { x: a >- G<|H|>[x] }}.  Each case builds a
   file (written fresh, then edited by hand where the case says), reads it
   with read_table, writes the term (or a changed one) against that table,
   and prints the lines written and whether they read back to the term
   saved.  The expected file is the output of the code as written.
   Pinned as found: an unchanged entry is written as it was, its label's
   case kept; an S/G pair is written back as one S line; of two copies of
   an entry the one the table maps the structure to is kept and the other
   dropped (for the sequent, the later copy s2); an entry whose structure
   changed is written fresh under a new name (F5, s1).  Two cases raise:
   a variable entry under a T label (a guess at the <= 1.0.7 form, which
   out_term relabels "V"; read_table's add_term refuses it first), and a
   variable entry naming an argument that does not exist. *)
open Term_sig
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
module A = Ascii_io.AsciiIO
module P = Simple_print.SimplePrint

let v = Lm_symbol.add
let op s = Opname.make_opname [ s ]
let c s = mk_simple_term (op s) []
let file = "test_ascii_io_save.prla"
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

let save name l t =
  say "== save: %s\n" name;
  match table_of l with
  | exception e -> say "   read_table raised %s\n" (Printexc.to_string e)
  | tbl ->
      let oc = open_out_bin file in
      match Fun.protect ~finally:(fun () -> close_out oc) (fun () -> A.write_term oc tbl t) with
      | exception e -> say "   write_term raised %s\n" (Printexc.to_string e)
      | () ->
          let out = lines_of file in
          List.iter (fun l -> say "   %s\n" (String.escaped l)) out;
          let back = try Ok (A.get_term (table_of out)) with e -> Error e in
          match back with
          | Ok b -> say "   read back alpha-equal to the term saved: %b\n" (Refiner.Refiner.TermSubst.alpha_equal t b)
          | Error e -> say "   read back raised %s\n" (Printexc.to_string e)

(* Replace the one line equal to [old] by [news]; a case that does not
   find its line says so rather than run on the unedited file. *)
let edit l old news =
  if List.length (List.filter (( = ) old) l) <> 1 then failwith ("edit: no single line " ^ String.escaped old);
  List.concat_map (fun x -> if x = old then news else [ x ]) l

let () =
  let fresh = write_fresh t1 in
  say "== the file written fresh\n";
  List.iter (fun l -> say "   %s\n" (String.escaped l)) fresh;
  let vf = "VF\tF\tF\\\\ \\\\ t" and sl = "S\ts\tt2\\\\ h\\\\ G" in
  save "the same term over its own file" fresh t1;
  save "a changed argument of F" fresh t2;
  save "the V entry relabelled v" (edit fresh vf [ "vF\tF\tF\\\\ \\\\ t" ]) t1;
  save "the S entry relabelled s" (edit fresh sl [ "s\ts\tt2\\\\ h\\\\ G" ]) t1;
  save "<= 1.0.6: the sequent as an S/G pair" (edit fresh sl [ "S\ts\tt2 h"; "G\ts\tG" ]) t1;
  save "<= 1.0.7: F under a T label" (edit fresh vf [ "TF\tF\tF\\\\ \\\\ t" ]) t1;
  save "F duplicated as F2" (edit fresh vf [ vf; "VF\tF2\tF\\\\ \\\\ t" ]) t1;
  save "the sequent duplicated as s2" (edit fresh sl [ sl; "S\ts2\tt2\\\\ h\\\\ G" ]) t1;
  save "F's entry names other arguments" (edit fresh vf [ "VF\tF\tF\\\\ \\\\ t1" ]) t1;
  save "the sequent's entry names another conclusion" (edit fresh sl [ "S\ts\tt2\\\\ h\\\\ t" ]) t1
