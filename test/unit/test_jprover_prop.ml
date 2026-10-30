(* JProver (refiner/reflib: jall, jordering, jtunify), the connection-based
   prover behind MetaPRL's jproverT, on propositional formulas.  On 400
   random formulas over the atoms p, q, r with not, and, or, implies (depth
   up to 3), using a JLogic over plain terms, against truth tables:
     - classical (C): it proves the formula exactly when it is a tautology;
     - intuitionistic (LJ): whatever it proves is a tautology;
     - Glivenko's theorem: LJ proves not not F exactly when F is a
       tautology;
     - LJ and the multiple-conclusion LJmc prove the same formulas.
   A run that raises anything but JProver's "not provable" / multiplicity
   errors counts as a difference.  17 formulas on which LJ did not
   finish in 10 s are skipped and counted (see hangs below).  It prints each count with how many
   formulas it was tried on, and the first difference.  The generator is a
   fixed linear congruential sequence, not Random. *)
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Jlogic_sig

let state = ref 67
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

type f = A of int | Not of f | And of f * f | Or of f * f | Imp of f * f
let rec gen d =
  if d = 0 || pick 4 = 0 then A (pick 3)
  else match pick 4 with
    | 0 -> Not (gen (d - 1)) | 1 -> And (gen (d - 1), gen (d - 1))
    | 2 -> Or (gen (d - 1), gen (d - 1)) | _ -> Imp (gen (d - 1), gen (d - 1))
let rec show = function
  | A i -> [| "p"; "q"; "r" |].(i) | Not a -> "~" ^ show a
  | And (a, b) -> "(" ^ show a ^ " & " ^ show b ^ ")" | Or (a, b) -> "(" ^ show a ^ " | " ^ show b ^ ")"
  | Imp (a, b) -> "(" ^ show a ^ " => " ^ show b ^ ")"
let rec eval v = function
  | A i -> v.(i) | Not a -> not (eval v a) | And (a, b) -> eval v a && eval v b
  | Or (a, b) -> eval v a || eval v b | Imp (a, b) -> (not (eval v a)) || eval v b
let tautology f =
  List.for_all (fun k -> eval [| k land 1 = 1; k land 2 = 2; k land 4 = 4 |] f) [ 0; 1; 2; 3; 4; 5; 6; 7 ]

let op s = Opname.make_opname [ s ]
let o_not = op "not" and o_and = op "and" and o_or = op "or" and o_imp = op "implies"
let rec build = function
  | A i -> mk_simple_term (op [| "p"; "q"; "r" |].(i)) []
  | Not a -> mk_simple_term o_not [ build a ]
  | And (a, b) -> mk_simple_term o_and [ build a; build b ]
  | Or (a, b) -> mk_simple_term o_or [ build a; build b ]
  | Imp (a, b) -> mk_simple_term o_imp [ build a; build b ]

module L = struct
  let is_all_term _ = false
  let dest_all _ = invalid_arg "dest_all"
  let is_exists_term _ = false
  let dest_exists _ = invalid_arg "dest_exists"
  let is_and_term = is_dep0_dep0_term o_and
  let dest_and = two_subterms
  let is_or_term = is_dep0_dep0_term o_or
  let dest_or = two_subterms
  let is_implies_term = is_dep0_dep0_term o_imp
  let dest_implies = two_subterms
  let is_not_term = is_dep0_term o_not
  let dest_not = one_subterm
  let is_box_term _ = false
  let dest_box _ = invalid_arg "dest_box"
  type inference = int
  let empty_inf = 0
  let append_inf n _ _ _ = n + 1
end
module P = Jall.JProver (L)

let prove calc f =
  try Ok (P.gen_prover (Some 3) calc [] [ build f ]) with
  | Refiner.Refiner.RefineError.RefineError _ -> Error ()
  | e -> raise e

let names = [| "C proves F iff F is a tautology"; "what LJ proves is a tautology";
               "LJ proves ~~F iff F is a tautology"; "LJ and LJmc prove the same" |]
let tried = Array.make 4 0 and ok = Array.make 4 0 and first = Array.make 4 None
let note k b what = tried.(k) <- tried.(k) + 1; if b then ok.(k) <- ok.(k) + 1 else if first.(k) = None then first.(k) <- Some what
let proved = function Ok _ -> true | Error () -> false

(* Formulas on which a check did not finish in 10 s when each formula was
   run alone (2026-10-30, OCaml 5.4.1): declared, skipped and counted, not
   run.  Each is a non-theorem whose double negation LJ and LJmc search for
   a long time although the multiplicity is capped at 3 (one ran over 120 s
   native); the smallest seen is ~~((r => r) => r), whose search at
   multiplicity 2 had taken over 99,000 steps after 5 s.  Whether the
   search is infinite or only very large is not measured. *)
let hangs = [ 14; 29; 64; 66; 99; 115; 120; 157; 182; 211; 241; 246; 302; 332; 337; 380; 393 ]

let () =
  let n = 400 in
  let fs = Array.init n (fun _ -> gen 3) in
  let only = try Some (int_of_string Sys.argv.(1)) with _ -> None in
  let nt = ref 0 and nlj = ref 0 and skipped = ref 0 in
  Array.iteri (fun k f ->
    if only <> None && only <> Some k then () else
    if only = None && List.mem k hangs then incr skipped else begin
    let t = tautology f in
    if t then incr nt;
    let s = show f in
    let guard k g = try g () with e -> note k false (s ^ ": raised " ^ Printexc.to_string e) in
    guard 0 (fun () -> note 0 (proved (prove Classical f) = t) (s ^ (if t then ": a tautology, not proved" else ": proved, not a tautology")));
    guard 1 (fun () ->
        let lj = proved (prove (Intuit SingleConcl) f) in
        if lj then incr nlj;
        note 1 ((not lj) || t) (s ^ ": LJ proved a non-tautology");
        guard 3 (fun () -> note 3 (proved (prove (Intuit MultiConcl) f) = lj) (s ^ (if lj then ": LJ only" else ": LJmc only"))));
    guard 2 (fun () -> note 2 (proved (prove (Intuit SingleConcl) (Not (Not f))) = t) (s ^ ": ~~F"))
    end) fs;
  Printf.printf "%d formulas, %d skipped (did not finish in 10 s), %d tautologies, %d proved in LJ\n" n !skipped !nt !nlj;
  Array.iteri (fun k name ->
      Printf.printf "%-40s %4d of %4d\n" name ok.(k) tried.(k);
      match first.(k) with None -> () | Some w -> Printf.printf "  first difference: %s\n" w) names
