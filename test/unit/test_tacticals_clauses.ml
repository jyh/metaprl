(* The clause tacticals of Tacticals_boot.Tacticals (onHypT, onClausesT,
   onAllHypsT and the rest), which test_tacticals_boot leaves out.  Goals are
   sequents of 0-5 entries, each a hypothesis x_k : A_k or a context J_k.
   The clause tactic is a recorder: applied at clause i it logs i, then is
   idT, failT or cutT of the goal itself (two subgoals, "assertion" and
   "main", both the same sequent), chosen per clause at random.  Each
   tactical is run with TacticInternal.refine, and the log and the subgoals'
   labels are compared with a model read from tacticals_boot.ml:
     onClausesT [i..]       the clauses in the order given; [] is idT
     onMClausesT            the same, the rest on "main" subgoals only
     onAllHypsT             the hypotheses from the LAST to the first,
                            contexts skipped; the conclusion is not visited
     onAllCumulativeHypsT   the hypotheses from the first to the last
     onAllClausesT          onAllHypsT, then clause 0 on every subgoal it
                            left (all the hypothesis visits come first)
     tryOn...               each clause under tryT
     onAllM...              the rest on "main" subgoals only
     tryOnAllMClausesT      tryOnAllMHypsT thenMT tryT clause 0, the same way
   The log is in the order the refiner applies the tactics, which the model
   takes to be depth first, subgoals left to right.
   The generator is a fixed linear congruential sequence, not Random. *)
open Refiner.Refiner
open Refiner.Refiner.TermType
open Tactic_boot
open Tacticals_boot.Tacticals

let state = ref 1113
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

type e = H of int | X of int
type eff = Id | Fail | Cut
let op s = Opname.make_opname [ s ]
let t name = Term.mk_simple_term (op name) []
let v = Lm_symbol.add
let mkseq es =
  TermMan.mk_sequent_term
    { sequent_args = TermMan.mk_xlist_term [];
      sequent_hyps = Term.SeqHyp.of_list (List.map (function
          | H k -> Term_sig.Hypothesis (v (Printf.sprintf "x%d" k), t (Printf.sprintf "A%d" k))
          | X k -> Term_sig.Context (v (Printf.sprintf "J%d" k), [], [])) es);
      sequent_concl = t "C" }
let arg goal = { TacticInternalType.ref_goal = Refine.mk_msequent goal []; ref_label = "main";
                 ref_attributes = TacticInternal.attribute_info_of_raw_attributes [];
                 ref_bookmark = Mp_resource.empty_bookmark; ref_sentinal = Tactic.null_sentinal }

type tl = Clauses of int list | MClauses of int list | TryClauses of int list | AllHyps | AllCum | AllClauses
        | TryAllHyps | TryAllCum | TryAllClauses | AllMHyps | AllMCum | TryAllMCum | TryAllMHyps | TryAllMClauses
let tshow = function
  | Clauses l -> "onClausesT " ^ String.concat "," (List.map string_of_int l)
  | MClauses l -> "onMClausesT " ^ String.concat "," (List.map string_of_int l)
  | TryClauses l -> "tryOnClausesT " ^ String.concat "," (List.map string_of_int l)
  | AllHyps -> "onAllHypsT" | AllCum -> "onAllCumulativeHypsT" | AllClauses -> "onAllClausesT"
  | TryAllHyps -> "tryOnAllHypsT" | TryAllCum -> "tryOnAllCumulativeHypsT" | TryAllClauses -> "tryOnAllClausesT"
  | AllMHyps -> "onAllMHypsT" | AllMCum -> "onAllMCumulativeHypsT" | TryAllMCum -> "tryOnAllMCumulativeHypsT"
  | TryAllMHyps -> "tryOnAllMHypsT" | TryAllMClauses -> "tryOnAllMClausesT"

(* The model: a step list run over goal labels, giving (log, Some labels | None). *)
type step = { idx : int; try_ : bool; mainonly : bool }  (* mainonly: this step reaches only "main" subgoals of the previous *)
let model eff (steps, phase2) =
  let log = ref [] in
  let one s lab =
    log := s.idx :: !log;
    match eff.(s.idx) with
    | Id -> Some [ lab ] | Cut -> Some [ "assertion"; "main" ]
    | Fail -> if s.try_ then Some [ lab ] else None in
  (* thenT a rest: rest on each subgoal of a, depth first; thenMT: rest only on main/"" labels.
     The label "" handling of thenMT: the subgoals are labelled under "" and restored, so a subgoal
     still at "" gets the goal's label; our recorder only makes "", "assertion", "main". *)
  let rec run lab = function
    | [] -> Some [ lab ]
    | s :: rest ->
       let lab_in = match rest with r :: _ when r.mainonly -> "" | _ -> lab in
       (match one s lab_in with
        | None -> None
        | Some subs ->
           let res = List.fold_left (fun acc l -> match acc with
               | None -> None
               | Some out ->
                  let go = match rest with r :: _ when r.mainonly -> l = "" || l = "main" | _ -> true in
                  if go then (match run l rest with None -> None | Some x -> Some (out @ x)) else Some (out @ [ l ])) (Some []) subs in
           (match rest with r :: _ when r.mainonly -> Option.map (List.map (fun l -> if l = "" then lab else l)) res | _ -> res)) in
  let r = match phase2 with
    | None -> run "main" steps
    | Some (s0, m) ->
       (* thenT (thenMT) phase1 phase2: phase 1 finishes on every subgoal before phase 2 runs on any *)
       let lab1 = if m then "" else "main" in
       (match run lab1 steps with
        | None -> None
        | Some ls ->
           let res = List.fold_left (fun acc l -> match acc with
               | None -> None
               | Some out -> if (not m) || l = "" || l = "main" then Option.map (fun x -> out @ x) (run l [ s0 ]) else Some (out @ [ l ]))
               (Some []) ls in
           if m then Option.map (List.map (fun l -> if l = "" then "main" else l)) res else res) in
  (List.rev !log, r)

let hyp_idx es = List.concat (List.mapi (fun i e -> match e with H _ -> [ i + 1 ] | X _ -> []) es)
let steps_of es w = match w with
  | Clauses l -> List.map (fun i -> { idx = i; try_ = false; mainonly = false }) l
  | MClauses l -> List.mapi (fun k i -> { idx = i; try_ = false; mainonly = k > 0 }) l
  | TryClauses l -> List.map (fun i -> { idx = i; try_ = true; mainonly = false }) l
  | AllHyps -> List.map (fun i -> { idx = i; try_ = false; mainonly = false }) (List.rev (hyp_idx es))
  | AllCum -> List.map (fun i -> { idx = i; try_ = false; mainonly = false }) (hyp_idx es)
  | AllClauses -> List.map (fun i -> { idx = i; try_ = false; mainonly = false }) (List.rev (hyp_idx es))
  | TryAllHyps -> List.map (fun i -> { idx = i; try_ = true; mainonly = false }) (List.rev (hyp_idx es))
  | TryAllCum -> List.map (fun i -> { idx = i; try_ = true; mainonly = false }) (hyp_idx es)
  | TryAllClauses -> List.map (fun i -> { idx = i; try_ = true; mainonly = false }) (List.rev (hyp_idx es))
  | AllMHyps -> List.mapi (fun k i -> { idx = i; try_ = false; mainonly = k > 0 }) (List.rev (hyp_idx es))
  | AllMCum -> List.mapi (fun k i -> { idx = i; try_ = false; mainonly = k > 0 }) (hyp_idx es)
  | TryAllMCum -> List.mapi (fun k i -> { idx = i; try_ = true; mainonly = k > 0 }) (hyp_idx es)
  | TryAllMHyps -> List.mapi (fun k i -> { idx = i; try_ = true; mainonly = k > 0 }) (List.rev (hyp_idx es))
  | TryAllMClauses -> List.mapi (fun k i -> { idx = i; try_ = true; mainonly = k > 0 }) (List.rev (hyp_idx es))
let phase2_of = function
  | AllClauses -> Some ({ idx = 0; try_ = false; mainonly = false }, false)
  | TryAllClauses -> Some ({ idx = 0; try_ = true; mainonly = false }, false)
  | TryAllMClauses -> Some ({ idx = 0; try_ = true; mainonly = false }, true)
  | _ -> None

let reallog = ref []
let recorder eff goal i = funT (fun _ -> reallog := i :: !reallog;
                                  match eff.(i) with Id -> idT | Fail -> failT | Cut -> cutT goal)
let build tac = function
  | Clauses l -> onClausesT l tac | MClauses l -> onMClausesT l tac | TryClauses l -> tryOnClausesT l tac
  | AllHyps -> onAllHypsT tac | AllCum -> onAllCumulativeHypsT tac | AllClauses -> onAllClausesT tac
  | TryAllHyps -> tryOnAllHypsT tac | TryAllCum -> tryOnAllCumulativeHypsT tac | TryAllClauses -> tryOnAllClausesT tac
  | AllMHyps -> onAllMHypsT tac | AllMCum -> onAllMCumulativeHypsT tac | TryAllMCum -> tryOnAllMCumulativeHypsT tac
  | TryAllMHyps -> tryOnAllMHypsT tac | TryAllMClauses -> tryOnAllMClausesT tac

let lshow l = "[" ^ String.concat "," (List.map string_of_int l) ^ "]"
let oshow = function None -> "refused" | Some l -> Printf.sprintf "%d: %s" (List.length l) (String.concat " " l)
let eshow es = String.concat ";" (List.map (function H k -> Printf.sprintf "x%d" k | X k -> Printf.sprintf "J%d" k) es)
let fshow eff = String.concat "" (Array.to_list (Array.map (function Id -> "i" | Fail -> "f" | Cut -> "c") eff))

let () =
  let n = 1000 and good = ref 0 and refused = ref 0 and visits = ref 0 and subgoals = ref 0 in
  for _ = 1 to n do
    let len = pick 6 in
    let es = List.init len (fun k -> if pick 4 = 0 then X k else H k) in
    let eff = Array.init (len + 1) (fun _ -> match pick 8 with 0 -> Fail | 1 | 2 -> Cut | _ -> Id) in
    let cl () = List.init (pick 4) (fun _ -> pick (len + 1)) in
    let w = match pick 14 with
      | 0 -> Clauses (cl ()) | 1 -> MClauses (cl ()) | 2 -> TryClauses (cl ()) | 3 -> AllHyps | 4 -> AllCum
      | 5 -> AllClauses | 6 -> TryAllHyps | 7 -> TryAllCum | 8 -> TryAllClauses | 9 -> AllMHyps | 10 -> AllMCum
      | 11 -> TryAllMCum | 12 -> TryAllMHyps | _ -> TryAllMClauses in
    let goal = mkseq es in
    let want_log, want = model eff (steps_of es w, phase2_of w) in
    reallog := [];
    let got = match TacticInternal.refine (build (recorder eff goal) w) (arg goal) with
      | gs, _ -> Some (List.map (fun (g : TacticInternalType.tactic_arg) -> g.ref_label) gs)
      | exception RefineError.RefineError _ -> None in
    let got_log = List.rev !reallog in
    if got = want && got_log = want_log then begin
      incr good; visits := !visits + List.length got_log;
      match got with None -> incr refused | Some l -> subgoals := !subgoals + List.length l
    end else
      Printf.printf "MISMATCH %s on [%s] effects %s: got %s log %s, model %s log %s\n" (tshow w) (eshow es) (fshow eff)
        (oshow got) (lshow got_log) (oshow want) (lshow want_log)
  done;
  Printf.printf "random: %d/%d agree with the model (%d refused, %d clause visits, %d subgoals in all)\n" !good n !refused !visits !subgoals
