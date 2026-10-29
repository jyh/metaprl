(* Match_seq.match_hyps matches the hypotheses of a smaller sequent into a
   bigger one (the proof editor uses it to re-attach a sub-proof when only
   hypotheses were added).  It returns, for each hypothesis of the big
   sequent, the index of the small hypothesis matched to it, if any; it may
   skip big hypotheses, and the conclusions must agree.  It never skips a
   big context while small hypotheses remain, but once they are all
   matched it skips whatever is left of the big sequent, contexts too
   (big <K>; x: B matches small with no hypotheses).  The model below
   records that as the behaviour; it is a heuristic for re-attaching
   proofs, which the refiner checks again.
   This test checks it against a model on 20,000 pairs of sequents over a
   small alphabet (so that a matcher has to backtrack): hypotheses x: A or
   x: B, contexts <J> and <K>, the conclusion C.  Half of the small
   sequents are made by deleting hypotheses from the big one, the other
   half at random.  For each pair it checks that match_hyps succeeds
   exactly when the model says a match exists, and that every mapping it
   returns is one: each small hypothesis used once, in order, each matched
   to a big one of the same kind and type or name, and every big context
   before the last matched one matched.  The generator is a fixed linear congruential sequence. *)
open Lm_symbol
open Term_sig
open Refiner.Refiner
open Term
open TermType

let state = ref 4242
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

type h = H of string | C of string        (* x: A  /  <J> *)

let gen_hyps () = List.init (pick 6) (fun _ -> match pick 6 with 0 -> C "J" | 1 -> C "K" | 2 | 3 -> H "A" | _ -> H "B")

(* The model: small is big with some x: T hypotheses deleted, and any tail of big. *)
let rec model big small =
  match big, small with
  | _, [] -> true   (* once small is exhausted, the rest of big is skipped, contexts too *)
  | [], _ :: _ -> false
  | b :: bs, s :: ss -> (b = s && model bs ss) || (match b with H _ -> model bs small | C _ -> false)

let op s = Opname.make_opname [ s ]
let esequent prefix hs =
  { sequent_args = mk_simple_term (op "sequent_arg") [];
    sequent_hyps = SeqHyp.of_list (List.mapi (fun i -> function
        | H t -> Hypothesis (add (Printf.sprintf "%s%d" prefix i), mk_simple_term (op t) [])
        | C k -> Context (add k, [], [])) hs);
    sequent_concl = mk_simple_term (op "C") [] }

(* Is r a valid matching of small into big? *)
let valid big small r =
  let big = Array.of_list big and small = Array.of_list small in
  Array.length r = Array.length big
  && (let used = List.filter_map (fun x -> x) (Array.to_list r) in
      used = List.init (Array.length small) (fun i -> i))
  && (let ok = ref true in
      let last_used = (let l = ref (-1) in Array.iteri (fun i x -> if x <> None then l := i) r; !l) in
      Array.iteri (fun i -> function
          | Some j -> if big.(i) <> small.(j) then ok := false
          | None -> (match big.(i) with C _ -> if i < last_used then ok := false | H _ -> ())) r;
      !ok)

let () =
  let n = 20000 in
  let agree = ref 0 and matched = ref 0 and invalid = ref 0 and first_bad = ref None and first_disagree = ref None in
  for i = 1 to n do
    let big = gen_hyps () in
    let small = if pick 2 = 0 then List.filter (function H _ -> pick 2 = 0 | C _ -> true) big else gen_hyps () in
    let expect = model big small in
    let got = try Some (Match_seq.match_hyps TermSubst.alpha_equal (esequent "b" big) (esequent "s" small)) with _ -> None in
    if (got <> None) = expect then incr agree
    else if !first_disagree = None then first_disagree := Some (i, big, small, expect);
    match got with
    | Some r -> incr matched; if not (valid big small r) then (incr invalid; if !first_bad = None then first_bad := Some (i, big, small, r))
    | None -> ()
  done;
  let show hs = "[" ^ String.concat "; " (List.map (function H t -> "x: " ^ t | C k -> "<" ^ k ^ ">") hs) ^ "]" in
  Printf.printf "%d pairs: match_hyps agrees with the model on %d (it matched %d)\n" n !agree !matched;
  (match !first_disagree with
   | None -> ()
   | Some (i, b, s, e) -> Printf.printf "  first disagreement, pair %d: big %s small %s, model %b\n" i (show b) (show s) e);
  Printf.printf "of the %d mappings it returned, %d are not a valid matching\n" !matched !invalid;
  match !first_bad with
  | None -> ()
  | Some (i, b, s, r) ->
      Printf.printf "  first, pair %d: big %s small %s mapping [%s]\n" i (show b) (show s)
        (String.concat "; " (Array.to_list (Array.map (function Some j -> string_of_int j | None -> "-") r)))
