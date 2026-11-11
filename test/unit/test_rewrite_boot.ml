(* Rewrite_boot.Rewrite applied as a TACTIC: rw conv i addr, which no unit
   test named (coverage recount 11-10; test_conversionals reaches the same
   module only through apply_rewrite, which is rw at 0 and the empty
   address).  Goals are msequents over f{_;_}, g{_} and the atoms a, b, c
   with 0-2 assumptions, run with the any-sentinel argument debug_arg.  Two
   input forms, swap f{'a;'b} --> f{'b;'a} and ung g{'a} --> 'a, are combined
   with idC, thenC, orelseC, higherC, allSubC, addrC, addrLiteralC, foldC,
   termC and funC, and rw puts the result at assumption i (0 is
   the goal) and a random address.  The subgoals are compared with a model:
     rw c i addr     rewrites the subterm at addr of the goal (i = 0) or of
                     assumption i; refused when i is past the assumptions, the
                     address is missing or c fails
     foldC t c       c must turn t into the term; the term becomes t
     termC h, funC h the conversion h picks from the term (from the env's term)
     cutC t          two subgoals: "assertion", the target with the subterm
                     replaced by t, and "main", the goal unchanged with that
                     assertion appended to the assumptions
   Measured and printed as fixed cases, not modelled:
     - an assumption number past the last: a rewrite is refused (rwtactic),
       idC succeeds without looking, and a conversion that reads the term
       first (funC, termC, higherC, allSubC) raises Failure "nth";
     - a NEGATIVE assumption number raises Invalid_argument "List.nth";
     - forceC lets RefineForceError out instead of RefineError;
     - makeFoldC on a single rewrite, and thenTC / tacticC at the goal.
   makeFoldC is checked when it is BUILT (it unfolds its term then, and
   refuses a conversion that is not a single rewrite, printing to stderr),
   so it is not in the random part.  The random part uses assumption
   numbers 0 to the last, and foldC only at assumption 0: foldC is a cut
   whose second half rewrites the new last assumption and closes it against
   the GOAL, so at an assumption i > 0 it succeeds only when the goal is the
   unfolded assumption (a fixed case below).
   An address the term lacks is not modelled either (as in
   test_conversionals): rw and addrC look it up only when a rewrite runs
   there, so idC at a missing address succeeds and a rewrite is refused;
   under higherC the outcome depends on where the lookup happens.  rw's own
   address is drawn from the target's subterms; a case whose conversion
   reaches a missing address is counted and not run, and three are fixed
   cases.
   The generator is a fixed linear congruential sequence, not Random. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Tactic_boot
open Rewrite_boot.Rewrite

let state = ref 1114
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

type d = A | B | C | G of d | F of d * d
let rec gen depth = if depth = 0 || pick 3 = 0 then [| A; B; C |].(pick 3)
  else if pick 2 = 0 then G (gen (depth - 1)) else F (gen (depth - 1), gen (depth - 1))
let rec dshow = function A -> "a" | B -> "b" | C -> "c" | G x -> "g{" ^ dshow x ^ "}" | F (x, y) -> "f{" ^ dshow x ^ "; " ^ dshow y ^ "}"

type c = Swap | Ung | Id | Then of c * c | Else of c * c | Higher of c | AllSub of c | Addr of int list * c
       | AddrLit of int list * c | Fold of d * c | TermC | FunC
let rec gc ?(fold = true) depth =
  let base () = [| Swap; Ung; Id; TermC; FunC |].(pick 5) in
  if depth = 0 then base () else
  let sub () = gc ~fold (depth - 1) in
  match pick 12 with
  | 0 | 1 | 2 -> base () | 3 -> Then (sub (), sub ()) | 4 -> Else (sub (), sub ()) | 5 -> Higher (sub ())
  | 6 -> AllSub (sub ()) | 7 -> Addr (List.init (1 + pick 2) (fun _ -> 1 + pick 2), sub ())
  | 8 -> AddrLit (List.init (1 + pick 2) (fun _ -> 1 + pick 2), sub ())
  | 9 | 10 when fold -> Fold (gen 2, sub ()) | _ -> base ()
let pshow p = "[" ^ String.concat ";" (List.map string_of_int p) ^ "]"
let rec cshow = function
  | Swap -> "swap" | Ung -> "ung" | Id -> "idC" | TermC -> "termC" | FunC -> "funC"
  | Then (a, b) -> "(" ^ cshow a ^ " thenC " ^ cshow b ^ ")" | Else (a, b) -> "(" ^ cshow a ^ " orelseC " ^ cshow b ^ ")"
  | Higher a -> "higherC " ^ cshow a | AllSub a -> "allSubC " ^ cshow a
  | Addr (p, a) -> "addrC " ^ pshow p ^ " " ^ cshow a | AddrLit (p, a) -> "addrLiteralC " ^ pshow p ^ " " ^ cshow a
  | Fold (t, a) -> "foldC " ^ dshow t ^ " " ^ cshow a

let kids = function F (x, y) -> [ x; y ] | G x -> [ x ] | _ -> []
let rebuild t ks = match t, ks with F _, [ x; y ] -> F (x, y) | G _, [ x ] -> G x | t, [] -> t | _ -> assert false
let ( >>= ) = Option.bind
exception Miss  (* an address the term lacks: not modelled, see the header *)
let rec at t = function [] -> Some t | i :: r -> (match List.nth_opt (kids t) (i - 1) with Some k -> at k r | None -> raise Miss)
let rec put t p x = match p with
  | [] -> x
  | i :: r -> rebuild t (List.mapi (fun j k -> if j = i - 1 then put k r x else k) (kids t))

(* termC: f -> swap, g -> ung, an atom -> idC.  funC: g -> ung, otherwise idC. *)
let rec model r t =
  match r with
  | Swap -> (match t with F (a, b) -> Some (F (b, a)) | _ -> None)
  | Ung -> (match t with G a -> Some a | _ -> None)
  | Id -> Some t
  | TermC -> model (match t with F _ -> Swap | G _ -> Ung | _ -> Id) t
  | FunC -> model (match t with G _ -> Ung | _ -> Id) t
  | Then (a, b) -> model a t >>= model b
  | Else (a, b) -> (match model a t with Some x -> Some x | None -> model b t)
  | Higher a -> (match model a t with Some x -> Some x | None -> Some (rebuild t (List.map (fun k -> Option.get (model (Higher a) k)) (kids t))))
  | AllSub a -> List.fold_right (fun k acc -> acc >>= fun ks -> model a k >>= fun x -> Some (x :: ks)) (kids t) (Some []) >>= fun ks -> Some (rebuild t ks)
  | Addr (p, a) | AddrLit (p, a) -> at t p >>= fun s -> model a s >>= fun x -> Some (put t p x)
  | Fold (u, a) -> model a u >>= fun x -> if x = t then Some u else None

let op s = Opname.make_opname [ s ]
let sov x = TermMan.mk_so_var_term (Lm_symbol.add x) [] []
let rec build = function
  | A -> mk_simple_term (op "a") [] | B -> mk_simple_term (op "b") [] | C -> mk_simple_term (op "c") []
  | G x -> mk_simple_term (op "g") [ build x ] | F (x, y) -> mk_simple_term (op "f") [ build x; build y ]
let rec back t =
  let o = Opname.string_of_opname (opname_of_term t) in
  match subterms_of_term t with
  | [] -> (match o with "a" -> A | "b" -> B | _ -> C)
  | [ x ] -> G (back x)
  | [ x; y ] -> F (back x, back y)
  | _ -> assert false
let swap = create_iform "swap" false (mk_simple_term (op "f") [ sov "a"; sov "b" ]) (mk_simple_term (op "f") [ sov "b"; sov "a" ])
let ung = create_iform "ung" false (mk_simple_term (op "g") [ sov "a" ]) (sov "a")
let addr p = TermAddr.make_address (List.map (fun i -> Term_addr_sig.Subterm i) p)
let is name t = Opname.eq (opname_of_term t) (op name)
let rec real = function
  | Swap -> swap | Ung -> ung | Id -> idC
  | TermC -> termC (fun t -> if is "f" t then swap else if is "g" t then ung else idC)
  | FunC -> funC (fun e -> if is "g" (env_term e) then ung else idC)
  | Then (a, b) -> prefix_thenC (real a) (real b) | Else (a, b) -> prefix_orelseC (real a) (real b)
  | Higher a -> higherC (real a) | AllSub a -> allSubC (real a)
  | Addr (p, a) -> addrC (List.map (fun i -> Term_addr_sig.Subterm i) p) (real a)
  | AddrLit (p, a) -> addrLiteralC (addr p) (real a)
  | Fold (u, a) -> foldC (build u) (real a)

type g = { gc : d; ga : d list; gl : string }
let p0 = TacticInternal.debug_arg Mp_resource.empty_bookmark (build A)
let arg g = { p0 with TacticInternalType.ref_goal = Refine.mk_msequent (build g.gc) (List.map build g.ga) }
let gback (p : TacticInternalType.tactic_arg) = let c, a = Refine.dest_msequent p.ref_goal in { gc = back c; ga = List.map back a; gl = p.ref_label }
let gshow g = Printf.sprintf "%s:%s [%s]" g.gl (dshow g.gc) (String.concat ", " (List.map dshow g.ga))
type r = Got of g list | Refused | Other of string
let rshow = function Got l -> String.concat " || " (List.map gshow l) | Refused -> "refused" | Other e -> "EXCEPTION " ^ e
let run tac g = match TacticInternal.refine tac (arg g) with
  | gs, _ -> Got (List.map gback gs)
  | exception RefineError.RefineError _ -> Refused
  | exception e -> Other (Printexc.to_string e)

let target g i = if i = 0 then Some g.gc else List.nth_opt g.ga (i - 1)
let retarget g i x = if i = 0 then { g with gc = x } else { g with ga = List.mapi (fun j y -> if j = i - 1 then x else y) g.ga }
let expect_rw r g i p = match target g i >>= fun tt -> at tt p >>= fun s -> model r s >>= fun x -> Some (put tt p x) with
  | Some x -> Got [ retarget g i x ] | None -> Refused
let expect_cut u g i p = match target g i >>= fun tt -> at tt p >>= fun _ -> Some (put tt p u) with
  | Some x -> Got [ { gc = x; ga = g.ga; gl = "assertion" }; { g with ga = g.ga @ [ x ]; gl = "main" } ] | None -> Refused

let () =
  let n = 1500 and good = ref 0 and refused = ref 0 and cuts = ref 0 and missed = ref 0 in
  for _ = 1 to n do
    let g = { gc = gen 3; ga = List.init (pick 3) (fun _ -> gen 2); gl = "main" } in
    let i = pick (List.length g.ga + 1) in
    let rec path t k = if k = 0 then [] else match kids t with [] -> [] | ks -> let j = pick (List.length ks) in (j + 1) :: path (List.nth ks j) (k - 1) in
    let p = path (Option.get (target g i)) (pick 3) in
    let cut = pick 6 = 0 and u = gen 2 and r = gc ~fold:(i = 0) 3 in
    match (if cut then expect_cut u g i p else expect_rw r g i p) with
    | exception Miss -> incr missed
    | want ->
       let what, tac = if cut then (incr cuts; Printf.sprintf "cutC %s" (dshow u), rw (cutC (build u)) i (addr p))
                       else cshow r, rw (real r) i (addr p) in
       let got = run tac g in
       if got = want then (incr good; if got = Refused then incr refused)
       else Printf.printf "MISMATCH rw (%s) %d %s on %s: got %s, model %s\n" what i (pshow p) (gshow g) (rshow got) (rshow want)
  done;
  Printf.printf "random: %d/%d agree with the model (%d refused, %d cutC); %d not run (an address the term lacks)\n" !good (n - !missed) !refused !cuts !missed;
  let g = { gc = F (G A, B); ga = [ F (A, B) ]; gl = "main" } in
  List.iter (fun (what, tac) -> Printf.printf "%s on %s -> %s\n" what (gshow g) (rshow (run tac g)))
    [ "rw ung at assumption 2 (one assumption)", rw ung 2 (addr []);
      "rw idC at assumption 2", rw idC 2 (addr []);
      "rw termC at assumption 2", rw (real TermC) 2 (addr []);
      "rw ung at assumption -1", rw ung (-1) (addr []);
      "rw idC at the missing address [2]", rw idC 0 (addr [ 2 ]);
      "rw ung at the missing address [2]", rw ung 0 (addr [ 2 ]);
      "rw (higherC (addrC [2] ung)) at [1]", rw (higherC (addrC [ Term_addr_sig.Subterm 2 ] ung)) 0 (addr [ 1 ]);
      "rw (foldC g{f{a; b}} ung) at assumption 1", rw (foldC (build (G (F (A, B)))) ung) 1 (addr []);
      "rw (makeFoldC f{b; g{a}} swap) at 0", rw (makeFoldC (build (F (B, G A))) swap) 0 (addr []);
      "rw (forceC \"x\" swap) at [1]", rw (forceC "x" swap) 0 (addr [ 1 ]);
      "rw (swap thenTC cutT c) at 0", rw (prefix_thenTC swap (Tacticals_boot.Tacticals.cutT (build C))) 0 (addr []);
      "rw (tacticC (fun _ -> cutT c)) at 0", rw (tacticC (fun _ -> Tacticals_boot.Tacticals.cutT (build C))) 0 (addr []) ];
  let g' = { gc = F (A, B); ga = [ F (A, B) ]; gl = "main" } in
  Printf.printf "rw (foldC g{f{a; b}} ung) at assumption 1 on %s (goal = the assumption) -> %s\n" (gshow g')
    (rshow (run (rw (foldC (build (G (F (A, B)))) ung) 1 (addr [])) g'))
