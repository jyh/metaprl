(* TermAddr.subterm_exists on a context term, in term_std and term_ds.
   term_ds holds  'C<|J|>[a; b]{f{c}}  as one SOContext node whose
   subterms are its arguments followed by the term in the hole, and no
   unit test asked subterm_exists about one (bisect at a45cd0437:
   Term_addr_ds.subterm_exists's SOContext arm unreached).  Each line is
   an address and what the two implementations answer (Subterm i is the
   i-th subterm from 1, or from the right when negative; Subterm 0 raises
   Invalid_argument).  The two agree on every address; only the wording
   of Subterm 0's refusal differs.  The expected file is the output of the
   code. *)
open Term_sig
open Term_addr_sig
let v = Lm_symbol.add
module S (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermMan
  open R.TermAddr
  let op s = Opname.make_opname [ s ]
  let mk s ts = mk_simple_term (op s) ts
  let ctx = mk_context_term (v "C") (mk "f" [ mk "c" [] ]) [ v "J" ] [ mk "a" []; mk "b" [] ]
  let ask addr =
    try string_of_bool (subterm_exists ctx (make_address addr)) with Invalid_argument s -> "Invalid_argument " ^ s
end
module Std = S (Refiner_std.Refiner)
module Ds = S (Refiner_ds.Refiner)
let () =
  let show = function Subterm i -> string_of_int i | ArgAddr -> "arg" | ClauseAddr i -> "clause " ^ string_of_int i in
  List.iter (fun addr ->
      let s = Std.ask addr and d = Ds.ask addr in
      Printf.printf "%-22s std %-6s ds %s\n" ("[" ^ String.concat "; " (List.map show addr) ^ "]") s (if s = d then "the same" else d))
    [ [ Subterm 1 ]; [ Subterm 2 ]; [ Subterm 3 ]; [ Subterm 4 ]; [ Subterm (-1) ]; [ Subterm (-3) ]; [ Subterm (-4) ];
      [ Subterm 3; Subterm 1 ]; [ Subterm 3; Subterm 2 ]; [ Subterm 1; Subterm 1 ]; [ Subterm 0 ] ]
