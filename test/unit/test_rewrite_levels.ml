(* Rewrite rules over universe levels (Rewrite_match_redex.match_redex_level,
   reached by no unit test before, 2026-11-02 profile).  A level is
   max(c, v1+o1, ..., vn+on).  Three rules move a level parameter from u to
   v; each is applied, in term_std and term_ds, to 300 random levels (c in
   0..3, variables k and m with offsets 0..2):
     u[l]{'a}   --> v[l]{'a}     returns the level unchanged;
     u[l+1]{'a} --> v[l+1]{'a}   is refused exactly when a variable has
                                 offset 0 (no l makes l+1 equal to k), and
                                 otherwise returns a level equal to the
                                 input;
     u[l+1]{'a} --> v[l]{'a}     is refused in the same cases, and
                                 otherwise returns a level one below.
   Two levels are equal when they are equal for every value of their
   variables (all >= 0): the same largest offset for each variable, and the
   same max(c, largest offset) (TermMan.level_le does not use v >= 0, so
   it reads max(1, k+1) and max(0, k+1) as different).
   Recorded as it is, not endorsed: the constant level 0 (no variables)
   matches l+1 with l = 0, so the second rule gives 1 and the third 0; those
   are counted apart.  The generator is a fixed linear congruential
   sequence, not Random. *)
open Term_sig

let state = ref 1717
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

let gen () =
  let c = pick 4 in
  let vs = List.filter_map (fun v -> if pick 2 = 0 then Some (v, pick 3) else None) [ "k"; "m" ] in
  c, vs
(* The value of max(c, v+o, ...) over all v >= 0, as a normal form. *)
let norm (c, vs) =
  let vars = List.sort_uniq compare (List.map fst vs) in
  let off v = List.fold_left (fun m (w, o) -> if w = v then max m o else m) 0 vs in
  let offs = List.map (fun v -> v, off v) vars in
  (if offs = [] then c else max c (List.fold_left (fun m (_, o) -> max m o) 0 offs)), offs
let succ_level (c, vs) = c + 1, List.map (fun (v, o) -> v, o + 1) vs
let show_l (c, vs) = Printf.sprintf "%d[%s]" c (String.concat "," (List.map (fun (v, o) -> Printf.sprintf "%s+%d" v o) vs))

module Rw (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermMan
  let op s = Opname.make_opname [ s ]
  let lv (c, vs) = mk_level c (List.map (fun (v, o) -> mk_level_var (Lm_symbol.add v) o) vs)
  let t o l a = mk_term (mk_op (op o) [ make_param (MLevel l) ]) [ mk_simple_bterm a ]
  let c = mk_simple_term (op "c") []
  let a = mk_so_var_term (Lm_symbol.add "a") [] []
  let level_of r = match dest_param (List.hd (dest_op (dest_term r).term_op).op_params) with MLevel l -> l | _ -> failwith "level_of"
  let show_level l =
    let { le_const; le_vars } = dest_level l in
    show_l (le_const, List.map (fun v -> let { le_var; le_offset } = dest_level_var v in Lm_symbol.string_of_symbol le_var, le_offset) le_vars)
  let rule pl cl = R.Rewrite.term_rewrite Rewrite_sig.Strict R.Rewrite.empty_args_spec [ t "u" (lv pl) a ] [ t "v" (lv cl) a ]
  let apply rw l = try Some (level_of (List.hd (R.Rewrite.apply_rewrite rw R.Rewrite.empty_args (t "u" (lv l) c) []))) with _ -> None
  let parts l =
    let { le_const; le_vars } = dest_level l in
    le_const, List.map (fun v -> let { le_var; le_offset } = dest_level_var v in Lm_symbol.string_of_symbol le_var, le_offset) le_vars
  let shown = function None -> "refused" | Some l -> show_level l
end

module Std = Rw (Refiner_std.Refiner)
module Ds = Rw (Refiner_ds.Refiner)

let () =
  let n = 300 in
  let levels = List.init n (fun _ -> gen ()) in
  let rules = [
    "u[l]{'a} --> v[l]{'a}", (0, [ "l", 0 ]), (0, [ "l", 0 ]), `Same;
    "u[l+1]{'a} --> v[l+1]{'a}", (0, [ "l", 1 ]), (0, [ "l", 1 ]), `Same;
    "u[l+1]{'a} --> v[l]{'a}", (0, [ "l", 1 ]), (0, [ "l", 0 ]), `Below;
  ] in
  List.iter (fun (name, pl, cl, kind) ->
      let s_rw = Std.rule pl cl and d_rw = Ds.rule pl cl in
      let agree = ref 0 and model = ref 0 and rewrote = ref 0 and zero = ref 0 and first = ref None and firstm = ref None in
      List.iter (fun l ->
          let s = Std.apply s_rw l and d = Ds.apply d_rw l in
          if Std.shown s = Ds.shown d then incr agree
          else if !first = None then first := Some (show_l l, Std.shown s, Ds.shown d);
          if d <> None then incr rewrote;
          let refuse = List.exists (fun (_, o) -> o < snd (List.hd (snd pl))) (snd l) in
          let ok =
            match d with
            | None -> refuse
            | Some out ->
                not refuse
                && (match kind with
                    | `Same -> norm (Ds.parts out) = norm l
                    | `Below -> norm (succ_level (Ds.parts out)) = norm l) in
          if l = (0, []) && not ok then incr zero
          else if ok then incr model
          else if !firstm = None then firstm := Some (show_l l, Ds.shown d))
        levels;
      Printf.printf "%s\n  std and ds agree on %d of %d (rewrote %d)\n" name !agree n !rewrote;
      (match !first with None -> () | Some (l, s, d) -> Printf.printf "    first difference, %s: std %s, ds %s\n" l s d);
      Printf.printf "  the model holds on %d; the constant level 0 is apart on %d\n" !model !zero;
      (match !firstm with None -> () | Some (l, d) -> Printf.printf "    first model difference, %s: %s\n" l d))
    rules;
  let rw = Ds.rule (0, [ "l", 1 ]) (0, [ "l", 1 ]) in
  Printf.printf "u[l+1] --> v[l+1] on the level 0: %s\n" (Ds.shown (Ds.apply rw (0, [])))
