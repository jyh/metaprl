(*
 * Utilities for tactics.
 *
 * $Log$
 * Revision 1.1  1997/04/28 15:52:41  jyh
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
 * Revision 1.1  1996/09/25 22:52:06  jyh
 * Initial "tactical" commit.
 *
 *)

open Term

(*
 * Sequent operations.
 *)
let get_pos_hyp_index i count =
   if i < 0 then
      count - i
   else
      i

let get_pos_hyp_num i (t, _) =
   if i < 0 then
      (num_hyps t) - i
   else
      i

let var_of_hyp i (t, _) =
   fst (nth_hyp t i)

let hyp_count (t, _) =
   num_hyps t

let get_decl_number (t, _) v =
   Term.get_decl_number t v

let nth_hyp i (t, _) =
   let _, h = Term.nth_hyp t i in
      h

let declared_vars (t, _) = Term.declared_vars t

let concl (t, _) = nth_concl t 0

let goal (t, _) = t

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
