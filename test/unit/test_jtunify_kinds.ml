(* Jtunify's position kinds other than Var and Const: NewVar i (the fresh
   variables rule R9 introduces), NewVarQ i (first-order Q variables) and
   GammaPos k (a position that jtunify reads as k), on test_jtunify_s4's
   problems and systems.  jtunify treats each of these as the kind it
   stands for: is_var, is_const, var_le, compatible_vars and sort_of take
   NewVar i and NewVarQ i as Var i and look through GammaPos, and positions
   are compared by number only.  So each problem is solved again in four
   variants (every Var i as NewVar i; as NewVarQ i; every variable under
   GammaPos; every position under GammaPos), and the unifier, with the
   kinds of both sides mapped back (NewVar, NewVarQ and GammaPos erased),
   must be the base problem's: the line reads "same in 4 variants" or names
   each variant that differs, with its unifier.  This reaches the NewVar,
   NewVarQ and GammaPos alternatives of sort_of, var_le and compatible_vars,
   which test_jtunify_s4 (Var and Const only) does not.
   Then six of the problems are solved with jtunify's debug trace on (each
   equation and the rule applied to it, "failure" where a rule was tried
   and failed), pinning the order in which the rules fire: R1, R2 and R4 to
   R11, and R15 (which the trace prints as "r13").
   Not reached here, stated: apply_r3 (do_stringunify and apply_subst strip
   equal first positions with shorten before any rule runs, and prefixes
   are paths, so the same position never meets itself later); apply_r13,
   whose condition is `never`; sort_of's and var_le's and
   compatible_vars' refusals (R9 calls sort_of only after compatible_vars
   holds, and prefixes hold no Atom, Dummy or EigenVar positions).
   The expected file is the output of the code as written, never typed. *)
open Jlogic_sig
open Jtypes
open Jordering

module L = struct
  let is_all_term _ = false
  let dest_all _ = invalid_arg "dest_all"
  let is_exists_term _ = false
  let dest_exists _ = invalid_arg "dest_exists"
  let is_and_term _ = false
  let dest_and _ = invalid_arg "dest_and"
  let is_or_term _ = false
  let dest_or _ = invalid_arg "dest_or"
  let is_implies_term _ = false
  let dest_implies _ = invalid_arg "dest_implies"
  let is_not_term _ = false
  let dest_not _ = invalid_arg "dest_not"
  let is_box_term _ = false
  let dest_box _ = invalid_arg "dest_box"
  type inference = unit
  let empty_inf = ()
  let append_inf () _ _ _ = ()
end
module U = Jtunify.JTUnifyProp (L)


let v i n = (Var i, n) and c i n = (Const i, n)
let show l = "[" ^ String.concat " " (List.map pos_to_string l) ^ "]"
let rec erase_k = function NewVar i | NewVarQ i -> Var i | GammaPos k -> erase_k k | k -> k
let erase (k, n) = (erase_k k, n)
let variants = [
  "NewVar", (function (Var i, n) -> (NewVar i, n) | p -> p);
  "NewVarQ", (function (Var i, n) -> (NewVarQ i, n) | p -> p);
  "GammaPos var", (function (Var i, n) -> (GammaPos (Var i), n) | p -> p);
  "GammaPos all", (fun (k, n) -> (GammaPos k, n));
]
let norm sigma = List.sort compare (List.map (fun (x, l) -> erase x, List.map erase l) sigma)
let render sigma = "{" ^ String.concat ", " (List.map (fun (x, l) -> pos_to_string x ^ " := " ^ show l) (List.sort compare sigma)) ^ "}"
let solve1 us ut = try let (_, s), _, _, _ = U.do_stringunify S4 us ut (Atom, 100) (Atom, 101) [] [] PMap.empty Set.empty [] 0 in Some s with Failed _ -> None
let rshow = function None -> "no unifier" | Some s -> render s

let problems = [
  true, [ v 1 1 ], [ c 1 2 ];
  true, [ v 1 1 ], [];
  true, [ v 1 1; v 1 3 ], [ c 1 2 ];
  true, [ v 0 1 ], [ c 1 2; c 2 3 ];
  false, [ v 1 1 ], [ c 2 2 ];
  true, [ c 1 9; v 1 1 ], [ c 1 9; c 1 4; v 2 5 ];
  true, [ v 1 1; v 1 3 ], [ c 1 2; c 1 4 ];
  true, [ v 1 1 ], [ v 1 2 ];
  false, [ v 1 1; c 1 2 ], [ c 1 3 ];
  true, [ v 0 1 ], [ v 1 2 ];
  true, [ v 1 1 ], [ v 0 2 ];
  true, [ v 2 1; v 1 3 ], [ c 1 4 ];
  false, [ c 1 2 ], [ c 1 3 ];
  true, [ v 1 1 ], [ v 0 2; c 1 3 ];
  true, [ v 1 1 ], [ v 2 2; c 1 3 ];
  true, [ v 1 1; v 1 5 ], [ v 0 2; c 1 3 ];
  false, [ v 1 1 ], [ v 2 2; c 2 3 ];
  true, [ v 1 1; c 1 2 ], [ v 2 3; v 1 4 ];
  false, [ v 1 1; c 1 2 ], [ c 2 3; v 1 4 ];
  true, [ v 0 1; c 1 2 ], [ c 2 3; v 1 4 ];
  false, [ c 1 9; c 2 8; v 2 1 ], [ c 1 9; v 1 2; c 2 3 ];
  false, [ v 1 1; c 1 2 ], [ v 1 3; c 1 4 ];
  true, [ v 1 1; c 1 2 ], [ v 1 3; v 1 4 ];
  true, [ v 1 1; v 1 2 ], [ v 1 3; v 1 4 ];
  true, [ v 1 1; c 1 2; v 1 5 ], [ v 1 3; c 1 4; v 1 6 ];
  false, [ v 1 1; c 1 2 ], [ c 1 3; v 1 4; c 1 5 ];
  true, [ v 1 1; c 1 2; v 1 7 ], [ c 1 3; v 1 4; c 1 5 ];
  true, [ v 2 1; v 1 2; c 1 3 ], [ v 1 4; c 1 5; v 1 6 ];
  false, [ v 0 1; c 2 2; v 1 3 ], [ v 1 4; c 1 5 ];
  false, [ v 1 1; c 2 2 ], [ v 1 3; c 1 4 ];
  true, [ v 1 1; v 2 2; c 1 3 ], [ v 2 4; v 1 5 ];
]

let systems = [
  `U, [ [ v 1 1 ], [ v 2 2; c 1 3 ]; [ v 2 2 ], [ c 2 4 ] ];
  `U, [ [ v 1 1 ], [ v 2 2; c 1 3 ]; [ v 2 2; c 2 4 ], [ c 2 5; v 2 6 ] ];
  `U, [ [ v 1 1; c 1 2 ], [ v 1 3; v 1 4 ]; [ v 1 4 ], [ c 1 5 ] ];
  `U, [ [ v 1 1; c 1 2 ], [ v 1 3; v 1 4 ]; [ v 1 4 ], [ c 2 5 ] ];
  `U, [ [ v 1 1 ], [ v 0 2 ]; [ v 0 2 ], [ c 2 3 ] ];
  `U, [ [ v 1 1 ], [ v 0 2; c 1 3 ]; [ v 0 2 ], [ c 2 4 ] ];
  `R, [ [ v 1 1 ], [ v 2 2; c 1 3 ]; [ v 2 2 ], [ v 2 5 ] ];
  `S, [ [ v 2 2 ], [ v 2 5 ]; [ v 1 1 ], [ v 2 2; c 1 3 ] ];
  `R, [ [ v 1 1 ], [ v 2 2; c 1 3 ]; [ v 2 5 ], [ v 2 2 ] ];
  `S, [ [ v 1 1 ], [ v 2 2; c 1 3 ]; [ v 2 2 ], [ v 1 5 ] ];
  `S, [ [ v 1 1; c 1 2 ], [ v 1 3; v 1 4 ]; [ v 1 4 ], [ v 1 5 ] ];
  `S, [ [ v 1 1 ], [ v 0 2 ]; [ v 0 2 ], [ c 1 3 ] ];
  `S, [ [ v 1 1 ], [ v 1 2; c 1 3 ]; [ v 1 2 ], [ c 1 4 ]; [ v 1 1 ], [ c 1 4; c 1 3 ] ];
  `U, [ [ v 1 1 ], [ v 1 2; c 1 3 ]; [ v 1 2 ], [ c 1 4 ]; [ v 1 1 ], [ c 1 3 ] ];
]

let solve_system eqs =
  let rec go k eql = function
    | [] -> assert false
    | (us, ut) :: rest ->
        let (_, sigma), eql, _, _ =
          U.do_stringunify S4 us ut (Atom, 100 + 2 * k) (Atom, 101 + 2 * k) eql [] PMap.empty Set.empty [] k in
        if rest = [] then sigma else go (k + 1) eql rest
  in
  try Some (go 0 [] eqs) with Failed _ -> None

let compare_variants base f =
  let nb = Option.map norm base in
  let diffs = List.filter_map (fun (name, m) ->
      let r = f m in
      if Option.map norm r = nb then None else Some (name ^ ": " ^ rshow r)) variants in
  if diffs = [] then "same in 4 variants" else "DIFFERS in " ^ String.concat "; " diffs

let () =
  List.iteri (fun k (_, us, ut) ->
      let base = solve1 us ut in
      Printf.printf "%2d %s =? %s\n   %s\n   %s\n%!" k (show us) (show ut) (rshow base)
        (compare_variants base (fun m -> solve1 (List.map m us) (List.map m ut)))) problems;
  List.iteri (fun k (_, eqs) ->
      let base = solve_system eqs in
      Printf.printf "system %d: %s\n   %s\n%!" k (rshow base)
        (compare_variants base (fun m -> solve_system (List.map (fun (us, ut) -> List.map m us, List.map m ut) eqs)))) systems

let () =
  Lm_debug.set_debug "jtunify" true;
  List.iter (fun (us, ut) ->
      Printf.printf "trace %s =? %s\n%!" (show us) (show ut);
      let r = solve1 us ut in
      Printf.printf "   %s\n%!" (rshow r))
    [ [ v 1 1; v 1 3 ], [ c 1 2; c 1 4 ]; [ v 1 1 ], [ v 2 2; c 2 3 ]; [ c 1 9; c 2 8; v 2 1 ], [ c 1 9; v 1 2; c 2 3 ];
      [ v 1 1; v 1 2 ], [ v 1 3; v 1 4 ]; [ v 1 1; c 1 2 ], [ v 1 3; v 1 4 ]; [ v 1 1 ], [ v 0 2; v 0 3 ] ];
  Lm_debug.set_debug "jtunify" false
