(* Jtunify (refiner/reflib), the T-string (prefix) unification behind
   JProver's S4 calculus, called directly on hand-built prefixes, so that
   the unifier itself is seen: the JProver tests print proofs, and a
   different but valid unifier leaves a proof unchanged.  A prefix is a
   list of positions; Const i (a box on the right, sort i) is fixed and
   Var i (a box on the left, sort i) may be replaced by a string;
   NewVar i is a fresh variable of sort i that unification introduces.
   pos_to_string prints Var 0 at position n as vn, Var i as vi_n.  Each
   problem unifies two prefixes with JTUnifyProp.do_stringunify in S4 and
   prints the unifier, or "no unifier".  Every unifier is then checked
   here, independently of jtunify's rules:
     - substituted, the two prefixes are the same string;
     - each variable's image respects its sort: Var 0 takes any position,
       Var i (and NewVar i) only positions of sort i (jtunify's var_le);
     - no variable is bound twice.
   A line ends "<- BAD" when a check fails, and "<- DIFFERS" when a
   problem marked solvable has no unifier or one marked unsolvable has. *)
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

let sort = function (Var i | Const i | NewVar i | NewVarQ i), _ -> Some i | _ -> None
let image sigma x = try List.assoc x sigma with Not_found -> [ x ]
let subst sigma l = List.concat_map (image sigma) l
let checks sigma us ut =
  let bad = ref [] in
  if subst sigma us <> subst sigma ut then bad := "not equal" :: !bad;
  List.iter (fun ((k, _) as x, img) ->
      match k with
      | Var 0 | NewVar 0 | NewVarQ 0 -> ()
      | Var i | NewVar i | NewVarQ i -> if List.exists (fun y -> sort y <> Some i) img then bad := ("sort of " ^ pos_to_string x) :: !bad
      | _ -> bad := ("binds " ^ pos_to_string x) :: !bad) sigma;
  let vars = List.map fst sigma in
  if List.length (List.sort_uniq compare vars) <> List.length vars then bad := "bound twice" :: !bad;
  List.rev !bad

(* solvable?, us, ut.  Prefixes are paths from the formula tree's root,
   so two prefixes share a position only in a common initial segment
   (which jtunify's rule R3 removes first); every pair here is so. *)
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

(* Systems: JProver unifies the prefixes of each new connection together
   with the equations of the connections before it (do_stringunify's
   equations argument, the list the previous call returned), so a variable
   bound for one equation is substituted into the others.  Each system is
   solved one equation at a time, as JProver does; the last unifier is
   checked against every equation.  Status: S solvable, U unsolvable, and
   R solvable but refused, PINNED AS FOUND (2026-11-11): the call solves
   the newest equation first and substitutes its unifier into the older
   ones, and apply_subst_list then refuses any equation whose two first
   positions are not ordered by var_le, which includes two variables of
   different sorts ([v1_1] =? [v2_5 c1_3] after v2_2 := [v2_5]) although
   either may become empty.  So the same equations are solved in one order
   (system 7) and refused in the other (6, 8).  Measured the same day:
   narrowing that check to two constants solves 6 and 8 and changes no
   outcome of the JProver tests, nor of 12,000 random S4 formulas with two
   modalities at multiplicity 2.  Whether any proof is lost is not shown,
   so the behaviour is recorded here, not changed. *)
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

let () =
  List.iteri (fun k (ok, us, ut) ->
      let res =
        try
          let (_, sigma), _, _, _ = U.do_stringunify S4 us ut (Atom, 100) (Atom, 101) [] [] PMap.empty Set.empty [] 0 in
          Some sigma
        with Failed _ -> None
      in
      let line = match res with
        | None -> "no unifier" ^ (if ok then "  <- DIFFERS" else "")
        | Some sigma ->
            let s = String.concat ", " (List.map (fun (x, l) -> pos_to_string x ^ " := " ^ show l) (List.sort compare sigma)) in
            let bad = checks sigma us ut in
            "{" ^ s ^ "}" ^ (if ok then "" else "  <- DIFFERS")
            ^ (if bad = [] then "" else "  <- BAD (" ^ String.concat "; " bad ^ ")")
      in
      Printf.printf "%2d %s =? %s\n   %s\n%!" k (show us) (show ut) line) problems
;;
let () =
  List.iteri (fun k (st, eqs) ->
      let ok = st = `S in
      let all = String.concat ", " (List.map (fun (us, ut) -> show us ^ " =? " ^ show ut) eqs) in
      let line = match solve_system eqs with
        | None -> "no unifier" ^ (if st = `R then " (solvable: refused, pinned)" else "") ^ (if ok then "  <- DIFFERS" else "")
        | Some sigma ->
            let s = String.concat ", " (List.map (fun (x, l) -> pos_to_string x ^ " := " ^ show l) (List.sort compare sigma)) in
            let bad = List.concat_map (fun (us, ut) -> checks sigma us ut) eqs in
            let bad = List.sort_uniq compare bad in
            "{" ^ s ^ "}" ^ (if ok then "" else "  <- DIFFERS")
            ^ (if bad = [] then "" else "  <- BAD (" ^ String.concat "; " bad ^ ")")
      in
      Printf.printf "system %d: %s\n   %s\n%!" k all line) systems
