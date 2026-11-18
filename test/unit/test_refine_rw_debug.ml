(* Refine.create_rewrite under the "refine" and "rewrites" debug flags
   (refiner/refiner/refine.ml), which no unit test turned on (2026-11-15
   profile: the flags' arms unvisited, the plain arms 504 times).
   A rewrite  swap  f{'a; 'b} --> f{'b; 'a}  is created in a null refiner
   and applied, through rwtactic and refine, to a term it rewrites and to
   one it does not, with each flag off and on.  Each refusal is printed as
   the tree of its refine_error constructors, so the test pins:
     both flags off    the rewriter's own error, unwrapped
     "refine" on       the same error, wrapped in
                       PairError ("Refiner: Rewrite swap failed on term\n\t",
                                  TermError <the term>, "reason", <it>)
     "rewrites" on     a trace line per application on stderr; the error
                       is not wrapped
   The "refine" flag also prints "Refiner.create_rewrite: <name>" when a
   rewrite is created. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError

(* Linking Simple_print installs the term printer the "rewrites" trace uses. *)
module P = Simple_print.SimplePrint
let _ = P.string_of_term

let op s = Opname.make_opname [ s ]
let c = mk_simple_term (op "c") []
let g a = mk_simple_term (op "g") [ a ]
let f a b = mk_simple_term (op "f") [ a; b ]

let rec show t =
  let { Term_sig.term_op; term_terms } = dest_term t in
  let name = String.concat "." (Opname.dest_opname (dest_op term_op).Term_sig.op_name) in
  match List.map (fun b -> show (dest_bterm b).Term_sig.bterm) term_terms with
  | [] -> name
  | args -> name ^ "{" ^ String.concat "; " args ^ "}"

let rec tree = function
  | PairError (s1, e1, s2, e2) -> Printf.sprintf "PairError (%S, %s, %S, %s)" s1 (tree e1) s2 (tree e2)
  | TermError t -> "TermError " ^ show t
  | StringError s -> Printf.sprintf "StringError %S" s
  | StringTermError (s, t) -> Printf.sprintf "StringTermError (%S, %s)" s (show t)
  | StringWrapError (s, e) -> Printf.sprintf "StringWrapError (%S, %s)" s (tree e)
  | SubgoalError (i, s, e) -> Printf.sprintf "SubgoalError (%d, %S, %s)" i s (tree e)
  | RewriteBadMatch _ -> "RewriteBadMatch _"
  | RewriteStringError s -> Printf.sprintf "RewriteStringError %S" s
  | RewriteAddressError (_, s, e) -> Printf.sprintf "RewriteAddressError (_, %S, %s)" s (tree e)
  | TermMatchError (t, s) -> Printf.sprintf "TermMatchError (%s, %S)" (show t) s
  | _ -> "(another constructor)"

let sov x = mk_so_var_term (Lm_symbol.add x) [] []

let say s = print_string s; print_newline ()

let create () =
  match create_rewrite (null_refiner "test_refine_rw_debug") "swap" (f (sov "a") (sov "b")) (f (sov "b") (sov "a")) with
  | PrimRW r -> r
  | CondRW _ -> failwith "cond"

let apply r t =
  flush stdout;
  let result =
    match refine any_sentinal (rwtactic 0 r) (mk_msequent t []) with
    | [ m ], _ -> "rewrote to " ^ show (msequent_goal m)
    | l, _ -> Printf.sprintf "%d subgoals" (List.length l)
    | exception RefineError (loc, e) -> Printf.sprintf "refused at %S: %s" loc (tree e)
  in
  flush stderr;
  say ("  " ^ show t ^ ": " ^ result)

let case title flags =
  say title;
  List.iter (fun (n, v) -> Lm_debug.set_debug n v) flags;
  flush stdout;
  let r = create () in
  flush stderr;
  apply r (f c (g c));
  apply r (g c);
  List.iter (fun (n, _) -> Lm_debug.set_debug n false) flags

let () =
  case "both flags off" [];
  case "\"refine\" on" [ "refine", true ];
  case "\"rewrites\" on" [ "rewrites", true ];
  case "both on" [ "refine", true; "rewrites", true ]
