(* Tacticals_boot.Tacticals, the tactic combinators every proof script is
   written in, which no unit test named (coverage recount 11-10).  The base
   tactics need no logic: idT, failT, cutT B (from goal C with assumptions
   as, the subgoals "assertion" B with as and "main" C with as @ [B]) and
   nthAssumT i (closes the goal when assumption i is its conclusion).  Random
   combinations of these with thenT, thenLT, orelseT, tryT, firstT,
   progressT, completeT, repeatForT, seqT, thenMT, thenAT, thenLabLT, ifLabT,
   then_OnFirstT, then_OnLastT and repeatT are run with TacticInternal.refine
   on random goals (a conclusion, 0-2 assumptions and a label), and the
   subgoals (label, conclusion, assumptions, in order) are compared with a
   model read from tacticals_boot.ml and tactic_boot.ml:
     thenLT t [t1..tn]  t, then ti on subgoal i; refused unless n subgoals
     progressT t        refused when ANY subgoal equals the goal (conclusion
                        and assumptions; the label is not compared), not
                        only a single one as its comment says
     completeT t        refused unless t leaves no subgoal
     thenMT / thenAT    t1 run under the label "", t2 on the subgoals whose
                        label is "" or a main label (thenMT) or any other
                        label (thenAT); a subgoal left at "" gets the goal's
                        label back
     thenLabLT t l      t1 under "", then the tactic l gives the subgoal's
                        label (idT when none), then "" gets the goal's label
     repeatT t          tryT t, then again on every subgoal whose conclusion
                        differs from the goal it came from
   thenLT whose first tactic is idT itself (idT, seqT [], repeatForT 0 t,
   thenT idT idT, tryT idT, orelseT idT t, firstT (idT :: l), ...) is checked when the tactic is BUILT: a list of any
   length but one is refused before any goal is seen, so a combination is
   modelled as refused at build when it contains one.  repeatT bodies are
   drawn from the base tactics, tryT and orelseT, and a case the model does
   not finish in 30 steps is not run (none at this seed).
   The generator is a fixed linear congruential sequence, not Random. *)
open Refiner.Refiner
open Tactic_boot
open Tacticals_boot.Tacticals

let state = ref 1112
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

let atoms = [| "A"; "B"; "C" |]
let labels = [| "main"; "assertion"; ""; "wf"; "upcase" |]

type c = Id | Fail | Cut of int | Nth of int | Then of c * c | ThenL of c * c list | Else of c * c | Try of c
       | First of c list | Progress of c | Complete of c | RepeatFor of int * c | Seq of c list | ThenM of c * c
       | ThenA of c * c | ThenLab of c * (string * c) list | IfLab of string * c * c | OnFirst of c * c
       | OnLast of c * c | Repeat of c

let rec grep_body depth =
  if depth = 0 || pick 2 = 0 then [| Id; Fail; Cut (pick 3); Nth (1 + pick 3) |].(pick 4)
  else if pick 2 = 0 then Try (grep_body (depth - 1)) else Else (grep_body (depth - 1), grep_body (depth - 1))

let rec gc depth =
  let base () = [| Id; Fail; Cut (pick 3); Cut (pick 3); Nth (1 + pick 3) |].(pick 5) in
  if depth = 0 then base () else
  let sub () = gc (depth - 1) in
  let subs () = List.init (pick 4) (fun _ -> sub ()) in
  match pick 20 with
  | 0 | 1 | 2 -> base ()
  | 3 -> Then (sub (), sub ()) | 4 -> ThenL (sub (), subs ()) | 5 -> Else (sub (), sub ()) | 6 -> Try (sub ())
  | 7 -> First (List.init (1 + pick 3) (fun _ -> sub ())) | 8 -> Progress (sub ()) | 9 -> Complete (sub ())
  | 10 -> RepeatFor (pick 3, sub ()) | 11 -> Seq (subs ()) | 12 -> ThenM (sub (), sub ()) | 13 -> ThenA (sub (), sub ())
  | 14 -> ThenLab (sub (), List.init (pick 3) (fun _ -> labels.(pick 5), sub ()))
  | 15 -> IfLab (labels.(pick 5), sub (), sub ()) | 16 -> OnFirst (sub (), sub ()) | 17 -> OnLast (sub (), sub ())
  | 18 -> Repeat (grep_body 2)
  | _ -> ThenL (Cut (pick 3), [ sub (); sub () ])

let rec cshow = function
  | Id -> "id" | Fail -> "fail" | Cut i -> "cut " ^ atoms.(i) | Nth i -> Printf.sprintf "nthAssum %d" i
  | Then (a, b) -> "(" ^ cshow a ^ " then " ^ cshow b ^ ")"
  | ThenL (a, l) -> "(" ^ cshow a ^ " thenL " ^ lshow l ^ ")"
  | Else (a, b) -> "(" ^ cshow a ^ " orelse " ^ cshow b ^ ")" | Try a -> "try " ^ cshow a
  | First l -> "first " ^ lshow l | Progress a -> "progress " ^ cshow a | Complete a -> "complete " ^ cshow a
  | RepeatFor (n, a) -> Printf.sprintf "repeatFor %d %s" n (cshow a) | Seq l -> "seq " ^ lshow l
  | ThenM (a, b) -> "(" ^ cshow a ^ " thenM " ^ cshow b ^ ")" | ThenA (a, b) -> "(" ^ cshow a ^ " thenA " ^ cshow b ^ ")"
  | ThenLab (a, l) -> "(" ^ cshow a ^ " thenLab [" ^ String.concat "; " (List.map (fun (s, t) -> Printf.sprintf "%S, %s" s (cshow t)) l) ^ "])"
  | IfLab (s, a, b) -> Printf.sprintf "ifLab %S %s %s" s (cshow a) (cshow b)
  | OnFirst (a, b) -> "(" ^ cshow a ^ " then_OnFirst " ^ cshow b ^ ")" | OnLast (a, b) -> "(" ^ cshow a ^ " then_OnLast " ^ cshow b ^ ")"
  | Repeat a -> "repeat " ^ cshow a
and lshow l = "[" ^ String.concat "; " (List.map cshow l) ^ "]"

(* A goal of the model: conclusion, assumptions, label. *)
type g = { gc : string; ga : string list; gl : string }

exception Diverge
let main_labels = [ "main"; "upcase"; "downcase"; "basecase"; "truecase"; "falsecase"; "base"; "step"; "subterm" ]
let ( >>= ) = Option.bind
let rec all f = function [] -> Some [] | x :: r -> f x >>= fun a -> all f r >>= fun b -> Some (a @ b)
let relabel l = List.map (fun s -> if s.gl = "" then { s with gl = l } else s)

(* Is the built tactic idT itself?  (prefix_thenT and the list tacticals return idT unchanged.) *)
let rec phys = function
  | Id -> true | Seq l -> List.for_all phys l | Then (a, b) -> phys a && phys b
  | RepeatFor (0, _) -> true | RepeatFor (_, a) -> phys a
  | Else (a, _) | Try a | First (a :: _) -> phys a  (* prefix_orelseT idT t is idT *)
  | ThenL (a, [ b ]) -> phys a && phys b | _ -> false
let rec builds = function
  | Id | Fail | Cut _ | Nth _ -> true
  | ThenL (a, l) -> (not (phys a) || List.length l = 1) && builds a && List.for_all builds l
  | Then (a, b) | Else (a, b) | ThenM (a, b) | ThenA (a, b) | OnFirst (a, b) | OnLast (a, b) | IfLab (_, a, b) -> builds a && builds b
  | Try a | Progress a | Complete a | RepeatFor (_, a) | Repeat a -> builds a
  | First l | Seq l -> List.for_all builds l
  | ThenLab (a, l) -> builds a && List.for_all (fun (_, t) -> builds t) l

let rec model fuel r g =
  if fuel = 0 then raise Diverge;
  let m = model (fuel - 1) in
  match r with
  | Id -> Some [ g ] | Fail -> None
  | Cut i -> Some [ { gc = atoms.(i); ga = g.ga; gl = "assertion" }; { g with ga = g.ga @ [ atoms.(i) ]; gl = "main" } ]
  | Nth i -> if i >= 1 && i <= List.length g.ga && List.nth g.ga (i - 1) = g.gc then Some [] else None
  | Then (a, b) -> m a g >>= all (m b)
  | ThenL (a, l) -> m a g >>= fun gs -> if List.length gs <> List.length l then None
                     else List.fold_right2 (fun s t acc -> acc >>= fun rest -> m t s >>= fun x -> Some (x @ rest)) gs l (Some [])
  | Else (a, b) -> (match m a g with Some x -> Some x | None -> m b g)
  | Try a -> m (Else (a, Id)) g
  | First l -> List.fold_left (fun acc t -> match acc with Some _ -> acc | None -> m t g) None l
  | Progress a -> m a g >>= fun gs -> if List.exists (fun s -> s.gc = g.gc && s.ga = g.ga) gs then None else Some gs
  | Complete a -> m a g >>= fun gs -> if gs = [] then Some [] else None
  | RepeatFor (n, a) -> if n = 0 then Some [ g ] else m (Then (a, RepeatFor (n - 1, a))) g
  | Seq l -> (match l with [] -> Some [ g ] | [ a ] -> m a g | a :: r -> m (Then (a, Seq r)) g)
  | ThenM (a, b) -> m a { g with gl = "" } >>= all (fun s -> if s.gl = "" || List.mem s.gl main_labels then m b s else Some [ s ]) >>= fun x -> Some (relabel g.gl x)
  | ThenA (a, b) -> m a { g with gl = "" } >>= all (fun s -> if s.gl = "" || List.mem s.gl main_labels then Some [ s ] else m b s) >>= fun x -> Some (relabel g.gl x)
  | ThenLab (a, l) -> m a { g with gl = "" } >>= all (fun s -> match List.assoc_opt s.gl l with Some t -> m t s | None -> Some [ s ]) >>= fun x -> Some (relabel g.gl x)
  | IfLab (s, a, b) -> if g.gl = s then m a g else m b g
  | OnFirst (a, b) -> m a g >>= (function [] -> Some [] | s :: r -> m b s >>= fun x -> Some (x @ r))
  | OnLast (a, b) -> m a g >>= fun gs -> (match List.rev gs with [] -> Some [] | s :: r -> m b s >>= fun x -> Some (List.rev r @ x))
  | Repeat a -> let rec rep fuel g = if fuel = 0 then raise Diverge;
                  model fuel (Try a) g >>= all (fun s -> if s.gc = g.gc then Some [ s ] else rep (fuel - 1) s) in rep fuel g

let t name = Term.mk_simple_term (Opname.make_opname [ name ]) []
let rec build = function
  | Id -> idT | Fail -> failT | Cut i -> cutT (t atoms.(i)) | Nth i -> nthAssumT i
  | Then (a, b) -> prefix_thenT (build a) (build b) | ThenL (a, l) -> prefix_thenLT (build a) (List.map build l)
  | Else (a, b) -> prefix_orelseT (build a) (build b) | Try a -> tryT (build a) | First l -> firstT (List.map build l)
  | Progress a -> progressT (build a) | Complete a -> completeT (build a) | RepeatFor (n, a) -> repeatForT n (build a)
  | Seq l -> seqT (List.map build l) | ThenM (a, b) -> prefix_thenMT (build a) (build b)
  | ThenA (a, b) -> prefix_thenAT (build a) (build b)
  | ThenLab (a, l) -> prefix_thenLabLT (build a) (List.map (fun (s, x) -> s, build x) l)
  | IfLab (s, a, b) -> ifLabT s (build a) (build b) | OnFirst (a, b) -> prefix_then_OnFirstT (build a) (build b)
  | OnLast (a, b) -> prefix_then_OnLastT (build a) (build b) | Repeat a -> repeatT (build a)

let arg g = { TacticInternalType.ref_goal = Refine.mk_msequent (t g.gc) (List.map t g.ga); ref_label = g.gl;
              ref_attributes = TacticInternal.attribute_info_of_raw_attributes [];
              ref_bookmark = Mp_resource.empty_bookmark; ref_sentinal = Tactic.null_sentinal }
let s t = Simple_print.SimplePrint.string_of_term t
let back (p : TacticInternalType.tactic_arg) =
  let c, a = Refine.dest_msequent p.ref_goal in { gc = s c; ga = List.map s a; gl = p.ref_label }

(* What the real tactic does: Some subgoals, None refused, or Error for anything else. *)
type r = Got of g list | Refused | Unbuilt | Other of string
let real r g =
  match build r with
  | exception RefineError.RefineError _ -> Unbuilt
  | tac -> (match TacticInternal.refine tac (arg g) with
            | gs, _ -> Got (List.map back gs)
            | exception RefineError.RefineError _ -> Refused
            | exception e -> Other (Printexc.to_string e))
let expect r g = if not (builds r) then Unbuilt else match model 30 r g with Some x -> Got x | None -> Refused
let gshow g = Printf.sprintf "%S:%s[%s]" g.gl g.gc (String.concat "," g.ga)
let rshow = function
  | Got l -> Printf.sprintf "%d: %s" (List.length l) (String.concat " | " (List.map gshow l))
  | Refused -> "refused" | Unbuilt -> "refused at build" | Other e -> "EXCEPTION " ^ e

let () =
  let n = 600 and good = ref 0 and diverged = ref 0 and refused = ref 0 and unbuilt = ref 0 and subgoals = ref 0 in
  for _ = 1 to n do
    let r = gc 3 in
    let g = { gc = atoms.(pick 3); ga = List.init (pick 3) (fun _ -> atoms.(pick 3)); gl = labels.(pick 5) } in
    match expect r g with
    | exception Diverge -> incr diverged
    | want ->
       let got = real r g in
       if got = want then begin
         incr good;
         (match got with Refused -> incr refused | Unbuilt -> incr unbuilt | Got l -> subgoals := !subgoals + List.length l | Other _ -> ())
       end else
         Printf.printf "MISMATCH %s on %s: got %s, model %s\n" (cshow r) (gshow g) (rshow got) (rshow want)
  done;
  Printf.printf "random: %d/%d agree with the model (%d refused, %d refused at build, %d subgoals in all); %d not run (model over 30 steps)\n"
    !good n !refused !unbuilt !subgoals !diverged;
  (* Fixed cases: the behaviours the model's comments name. *)
  let c = { gc = "C"; ga = []; gl = "main" } in
  List.iter (fun (what, r, g) -> Printf.printf "%s: %s on %s -> %s\n" what (cshow r) (gshow g) (rshow (real r g)))
    [ "progressT, two subgoals, one equal to the goal", Progress (Cut 2), c;
      "progressT, two subgoals, neither equal", Progress (Cut 1), c;
      "thenLT after idT, list of two", ThenL (Id, [ Id; Id ]), c;
      "thenLT after idT, list of one", ThenL (Id, [ Cut 0 ]), c;
      "thenLT after cutT, list of one", ThenL (Cut 0, [ Id ]), c;
      "thenLT after idT in an unreached branch", Else (Id, ThenL (Seq [], [])), c;
      "repeatT cutT stops on the conclusions it made", Repeat (Cut 1), c;
      "nthAssumT closes on an equal assumption", Then (Cut 2, Try (Nth 1)), c;
      "thenMT restores the goal's label", ThenM (Id, Id), { c with gl = "wf" };
      "thenLabLT on the main subgoal", ThenLab (Cut 0, [ "main", Cut 1 ]), { c with gl = "upcase" } ]
