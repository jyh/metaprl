(* unit-link: filter *)
(* Basic.term_to_stamp (library/basic.ml), the Nuprl-5 link's reader of a
   stamp term, which no unit test, theory build or proof census reached
   (2026-11-15 re-rank, deadsplit680; its callers are all link-protocol
   code: db, definition, library, orb).  A stamp holds the process id and
   the time, so nothing here prints one: two new stamps are made, and
   the test prints the round trip stamp_to_term / term_to_stamp, their
   order, and term_to_stamp on terms that are not stamps (a constant,
   and a stamp term with one parameter replaced).  A refusal prints the
   first line Basic.error writes before it raises (Basic.Nuprl5_Exception
   is not exported); the rest of what it writes is the term, which holds
   this host's address, pid and time, and is dropped.  The expected file is the output of the code as
   written (2026-11-15). *)
open Term_sig
open Refiner.Refiner.Term

let ans f = try f () with e -> Printexc.to_string e

(* run f with stdout captured; Basic.error prints its words and then the
   offending term, which holds this host's address, pid and time: keep the
   first line (the words) only *)
let words f =
  flush stdout;
  let file = Filename.temp_file "tns" ".out" in
  let saved = Unix.dup Unix.stdout in
  let fd = Unix.openfile file [ Unix.O_WRONLY; Unix.O_TRUNC ] 0o600 in
  Unix.dup2 fd Unix.stdout; Unix.close fd;
  let r = ans f in
  flush stdout; Unix.dup2 saved Unix.stdout; Unix.close saved;
  let ic = open_in_bin file in
  let first = try input_line ic with End_of_file -> "" in
  close_in ic; Sys.remove file;
  if first = "" then r else r ^ " (" ^ first ^ ")"
let b x = string_of_bool x

(* the stamp term with parameter k replaced *)
let with_param t k p =
  let { term_op; term_terms } = dest_term t in
  let { op_name; op_params } = dest_op term_op in
  mk_term (mk_op op_name (List.mapi (fun i q -> if i = k then p else q) op_params)) term_terms

let () =
  let s1 = Basic.new_stamp () in
  let s2 = Basic.new_stamp () in
  let t1 = Basic.stamp_to_term s1 in
  Printf.printf "round trip equal          %s\n" (ans (fun () -> b (Basic.equal_stamps_p (Basic.term_to_stamp t1) s1)));
  Printf.printf "s1, s2 equal              %s\n" (b (Basic.equal_stamps_p s1 s2));
  Printf.printf "s1 in s1's transaction    %s\n" (b (Basic.in_transaction_p s1 s1));
  Printf.printf "s1 before s2              %s\n" (ans (fun () -> b (Basic.transaction_less s1 s2)));
  Printf.printf "s2 before s1              %s\n" (ans (fun () -> b (Basic.transaction_less s2 s1)));
  let num = make_param (Number (Lm_num.num_of_int 7)) in
  let tok = make_param (Token (Opname.make_opname [ "t" ])) in
  List.iter (fun (name, t) -> Printf.printf "term_to_stamp %-12s %s\n%!" name (words (fun () -> ignore (Basic.term_to_stamp t); "accepted")))
    [ "c", mk_simple_term (Opname.make_opname [ "c" ]) [];
      "pid number", with_param t1 4 num;
      "tseq token", with_param t1 3 tok;
      "seq token", with_param t1 1 tok;
      "a subterm", mk_term (dest_term t1).term_op [ mk_bterm [] t1 ] ]
