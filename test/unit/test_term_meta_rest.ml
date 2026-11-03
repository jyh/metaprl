(* The rest of Term_meta (refiner/term_gen/term_meta_gen, shared by both
   term implementations): the functions test_term_meta leaves out.  On 600
   generated meta terms (theorems, implications, meta-functions, iffs and
   labels over small terms with binders), in term_std and term_ds, each
   against a model computed on the description:
     - is_meta_term holds for term_of_meta_term m, and not for a plain term
       or for the encoding of an implication whose part is a plain term;
     - iter_mterm visits the description's terms in order (a
       meta-function's variable term before its parts), and map_mterm
       applies f at the same places and keeps the structure;
     - all_vars_mterm is the union of all_vars over those terms;
     - strip_mfunction turns every meta-function into an implication, keeps
       iffs and labels, and refuses a label on a theorem or an iff;
     - unzip_mrewrite takes a rewrite (implications of theorems ending in an
       iff of two theorems, labels anywhere above) to its hypotheses, redex
       and contractum, and refuses anything else;
     - zip_mlabeled gives implications of labeled hypotheses, which
       unfold_mlabeled takes back to the hypothesis terms.
   Meta terms are compared with meta_alpha_equal (test_term_meta).  The
   generator is a fixed linear congruential sequence, not Random. *)
open Term_sig

let state = ref 8181
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

type d = Var of string | Op of string * d list | Bind of string * d
let rec gen env depth =
  match pick (if depth = 0 then 2 else 4) with
  | 0 -> if env = [] || pick 2 = 0 then Var [| "z"; "w" |].(pick 2) else Var (List.nth env (pick (List.length env)))
  | 1 -> Op ([| "c"; "e" |].(pick 2), [])
  | 2 -> Op ("f", List.init (1 + pick 2) (fun _ -> gen env (depth - 1)))
  | _ -> let x = [| "x"; "y" |].(pick 2) in Bind (x, gen (x :: env) (depth - 1))

type md = MT of d | MI of md * md | MF of d * md * md | MIff of md * md | ML of string * md
let rec gm depth =
  match pick (if depth = 0 then 1 else 6) with
  | 0 | 1 -> MT (gen [] 2)
  | 2 -> MI (gm (depth - 1), gm (depth - 1))
  | 3 -> MF (Var [| "u"; "v" |].(pick 2), gm (depth - 1), gm (depth - 1))
  | 4 -> MIff (gm (depth - 1), gm (depth - 1))
  | _ -> ML ([| "intro"; "elim" |].(pick 2), gm (depth - 1))
(* a rewrite: implications of theorems, ending in an iff of theorems, labels sprinkled *)
let rec grw depth =
  let lab m = if pick 3 = 0 then ML ("rw", m) else m in
  if depth = 0 || pick 2 = 0 then lab (MIff (MT (gen [] 2), MT (gen [] 2)))
  else lab (MI (MT (gen [] 2), grw (depth - 1)))

(* models *)
let rec terms = function MT t -> [ t ] | MI (a, b) | MIff (a, b) -> terms a @ terms b | MF (t, a, b) -> t :: terms a @ terms b | ML (_, a) -> terms a
exception Refused
let rec strip = function
  | MT _ as t -> t | MI (a, t) | MF (_, a, t) -> MI (a, strip t) | MIff (a, b) -> MIff (strip a, strip b)
  | ML (_, (MT _ | MIff _)) -> raise Refused | ML (l, t) -> ML (l, strip t)
let rec unzip_rw = function
  | MIff (MT r, MT c) -> [], r, c
  | MI (MT a, t) -> let l, r, c = unzip_rw t in a :: l, r, c
  | ML (_, t) -> unzip_rw t
  | _ -> raise Refused

module S (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermMan
  open R.TermSubst
  open R.TermMeta
  let op s = Opname.make_opname [ s ]
  let rec build = function
    | Var v -> mk_var_term (Lm_symbol.add v)
    | Op (o, ts) -> mk_simple_term (op o) (List.map build ts)
    | Bind (x, t) -> mk_term (mk_op (op "lam") []) [ mk_bterm [ Lm_symbol.add x ] (build t) ]
  let rec mbuild = function
    | MT t -> MetaTheorem (build t) | MI (a, b) -> MetaImplies (mbuild a, mbuild b)
    | MF (t, a, b) -> MetaFunction (build t, mbuild a, mbuild b) | MIff (a, b) -> MetaIff (mbuild a, mbuild b)
    | ML (l, a) -> MetaLabeled (l, mbuild a)
  let same l1 l2 = List.length l1 = List.length l2 && List.for_all2 alpha_equal l1 l2
  let refused f = try ignore (f ()); false with R.RefineError.RefineError _ -> true | _ -> false
  let wrap t = mk_simple_term (op "w") [ t ]
  let run name ms rws =
    let n = List.length ms in
    let c = Array.make 8 0 in
    let chk i b = if b then c.(i) <- c.(i) + 1 in
    List.iter (fun md ->
        let m = mbuild md in
        chk 0 (is_meta_term (term_of_meta_term m));
        let seen = ref [] in
        iter_mterm (fun t -> seen := t :: !seen) m;
        chk 1 (same (List.rev !seen) (List.map build (terms md)));
        let mm = map_mterm wrap m in
        let rec wrapd = function
          | MT t -> MT (Op ("w", [ t ])) | MI (a, b) -> MI (wrapd a, wrapd b) | MF (t, a, b) -> MF (Op ("w", [ t ]), wrapd a, wrapd b)
          | MIff (a, b) -> MIff (wrapd a, wrapd b) | ML (l, a) -> ML (l, wrapd a) in
        chk 2 (meta_alpha_equal mm (mbuild (wrapd md)));
        chk 3 (Lm_symbol.SymbolSet.equal (all_vars_mterm m) (List.fold_left (fun s t -> Lm_symbol.SymbolSet.union s (all_vars (build t))) Lm_symbol.SymbolSet.empty (terms md)));
        chk 4 (match (try Some (strip md) with Refused -> None) with
            | Some sm -> (try meta_alpha_equal (strip_mfunction m) (mbuild sm) with _ -> false)
            | None -> refused (fun () -> strip_mfunction m));
        chk 5 (match (try Some (unzip_rw md) with Refused -> None) with
            | Some (hs, r, c') -> (try let hs', r', c'' = unzip_mrewrite m in same hs' (List.map build hs) && alpha_equal r' (build r) && alpha_equal c'' (build c') with _ -> false)
            | None -> refused (fun () -> unzip_mrewrite m))) ms;
    List.iter (fun md ->
        chk 6 (match unzip_rw md with
            | hs, r, c' -> (try let hs', r', c'' = unzip_mrewrite (mbuild md) in same hs' (List.map build hs) && alpha_equal r' (build r) && alpha_equal c'' (build c') with _ -> false))) rws;
    let names = [| "is_meta_term of term_of_meta_term"; "iter_mterm visits the terms in order"; "map_mterm = the model";
                   "all_vars_mterm = union of all_vars"; "strip_mfunction = the model (or refused)";
                   "unzip_mrewrite = the model (or refused)"; "unzip_mrewrite on generated rewrites" |] in
    Array.iteri (fun i nm -> Printf.printf "%-50s %4d of %d\n" (name ^ ": " ^ nm) c.(i) (if i = 6 then List.length rws else n)) names;
    let plain = mk_simple_term (op "c") [] in
    (* the encoding's own implication operator, with plain terms as its parts *)
    let enc = term_of_meta_term (MetaImplies (MetaTheorem plain, MetaTheorem plain)) in
    let bad = mk_term (dest_term enc).term_op [ mk_simple_bterm plain; mk_simple_bterm plain ] in
    Printf.printf "%-50s %b, %b\n" (name ^ ": is_meta_term of c, of a broken implication") (is_meta_term plain) (is_meta_term bad);
    (* zip_mlabeled / unfold_mlabeled *)
    let hs = [ [ "a"; "b"; "d" ], build (Op ("c", [])); [], build (Var "z"); [ "k" ], build (Op ("f", [ Var "w" ])) ] in
    let g = build (Op ("e", [])) in
    let rec walk acc = function
      | MetaImplies (a, rest) -> walk (a :: acc) rest
      | MetaTheorem t -> List.rev acc, Some t
      | _ -> List.rev acc, None in
    let rec labels = function MetaLabeled (l, a) -> l :: labels a | _ -> [] in
    let parts, goal = walk [] (zip_mlabeled hs g) in
    Printf.printf "%-50s %b\n" (name ^ ": zip_mlabeled: labels, unfold_mlabeled, goal")
      (List.length parts = 3
       && List.for_all2 (fun p (ls, h) -> labels p = ls && alpha_equal (unfold_mlabeled "t" p) h) parts hs
       && (match goal with Some t -> alpha_equal t g | None -> false));
    Printf.printf "%-50s %b\n" (name ^ ": unfold_mlabeled refuses an implication")
      (refused (fun () -> unfold_mlabeled "t" (MetaImplies (MetaTheorem g, MetaTheorem g))))
end

module Std = S (Refiner_std.Refiner)
module Ds = S (Refiner_ds.Refiner)

let () =
  let ms = List.init 600 (fun _ -> gm 3) and rws = List.init 300 (fun _ -> grw 3) in
  let count p = List.length (List.filter p ms) in
  Printf.printf "600 meta terms (%d strip-refused, %d rewrites among them), 300 generated rewrites\n"
    (count (fun m -> try ignore (strip m); false with Refused -> true))
    (count (fun m -> try ignore (unzip_rw m); true with Refused -> false));
  Std.run "std" ms rws;
  Ds.run "ds" ms rws
