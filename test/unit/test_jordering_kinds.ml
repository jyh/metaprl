(* Jordering.is_const and is_var (refiner/reflib/jordering.ml), JProver's
   classification of a position by its kind (Jtypes.pos_kind), on every
   kind, bare and under GammaPos.  The prover tests reach only the kinds
   the prover builds there (Const, Var, NewVar, NewVarQ); the others were
   unvisited (2026-11-15 profile).  Pinned as found: EigenVar counts as a
   constant (its declaration says it "behaves like a constant"), and
   Atom, EmptyVar, Root and Dummy are neither.
   The expected file is the output of the code as written, never typed. *)
open Jtypes

let kinds = [
  "EmptyVar", EmptyVar; "Atom", Atom; "Const 1", Const 1; "Dummy", Dummy; "EigenVar", EigenVar;
  "Var 1", Var 1; "NewVar 1", NewVar 1; "NewVarQ 1", NewVarQ 1; "Root", Root;
]

let () =
  List.iter (fun (name, k) ->
      List.iter (fun (label, k) ->
          Printf.printf "%-22s is_const %-5b is_var %b\n" label (Jordering.is_const (k, 0)) (Jordering.is_var (k, 0)))
        [ name, k; "GammaPos (" ^ name ^ ")", GammaPos k ]) kinds
