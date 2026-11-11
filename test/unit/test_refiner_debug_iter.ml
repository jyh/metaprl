(* Refiner_debug (TERMS = both) runs each term operation in std and ds.
   TermOp.iter_down, TermOp.iter_up and TermMeta.iter_mterm take a
   callback run for its side effect on every subterm.  The reduce resource
   (support/tactics/top_conversionals.ml, cound_vars) counts with such a
   callback how many times each second-order variable occurs in a
   contractum, and pre-reduces the subterms that occur more than once.
   If the debug refiner runs the callback once per implementation, every
   count doubles, every variable looks copied, and the resource
   pre-reduces subterms it should leave alone: itt_int_ext's ind unfolding
   then never stops under TERMS = both.

   This test runs each iterator in std alone, in ds alone and in the debug
   refiner over the same terms, and prints how many times the callback
   ran and the second-order variable counts cound_vars would compute.
   The expected output is as the code printed it when the test was
   written. *)
open Lm_symbol

module Count (R : Refiner_sig.RefinerSig) = struct
  open R
  let op s = Opname.make_opname [ s ]
  let v = Lm_symbol.add
  let so x = TermMan.mk_so_var_term (v x) [] []
  let f a b = Term.mk_simple_term (op "f") [ a; b ]
  let term = f (so "a") (f (so "b") (f (so "a") (Term.mk_var_term (v "x"))))
  let mterm = Term_sig.MetaImplies (Term_sig.MetaTheorem term, Term_sig.MetaTheorem (so "b"))

  let run name iter t =
    let calls = ref 0 in
    let tbl = Hashtbl.create 7 in
    iter (fun t ->
        incr calls;
        if TermMan.is_so_var_term t then begin
          let x, _, _ = TermMan.dest_so_var t in
          Hashtbl.replace tbl (string_of_symbol x) (1 + try Hashtbl.find tbl (string_of_symbol x) with Not_found -> 0)
        end) t;
    let counts = List.sort Stdlib.compare (Hashtbl.fold (fun k n l -> Printf.sprintf "%s=%d" k n :: l) tbl []) in
    Printf.sprintf "%s: %d calls, %s" name !calls (String.concat " " counts)

  let all () =
    [ run "iter_down" TermOp.iter_down term;
      run "iter_up" TermOp.iter_up term;
      run "iter_mterm" TermMeta.iter_mterm mterm ]
end

module Std = Count (Refiner_std.Refiner)
module Ds = Count (Refiner_ds.Refiner)
module Dbg = Count (Refiner_debug.MakeRefinerDebug (Refiner_std.Refiner) (Refiner_ds.Refiner))

let () =
  List.iter (fun (name, l) -> List.iter (fun s -> Printf.printf "%-6s %s\n" name s) l)
    [ ("std", Std.all ()); ("ds", Ds.all ()); ("debug", Dbg.all ()) ]
