(* unit-link: filter *)
(* Filter_ocaml's camlp5 extension nodes (ExXtr, PaXtr, SgXtr, StXtr,
   MtXtr, MeXtr, CeXtr), which OCaml's own syntax cannot write, so no
   round-trip test reached them (2026-11-15 rank: mk_module_expr's MeXtr
   arm and its "antiquotations" refusal).  Each node is built as camlp5
   syntax, turned into a term (term_of_expr, term_of_patt with a tail,
   term_of_sig_item, term_of_str_item, term_of_module_type,
   term_of_module_expr; CeXtr inside a class declaration) and back; each
   line prints the term and what comes back.  (CtXtr is
   test_filter_ocaml_camlp5's.)
   Pinned as found (2026-11-16): every one of the seven is REFUSED on the
   way back ("bad arity"): each encoder writes the extension's name as the
   term's string and its optional body as ONE subterm, and each decoder
   reads two subterms.  The decoders' FormatError messages are printed by
   the *_of_term functions themselves, before the line.
   Also read from the output: an antiquoted body, and camlp5 8's coercion
   in (val x :> s), are both refused as "antiquotations are not supported".
   The expected file is the output of the code as written, never typed. *)
open MLast
module F = Filter_ocaml.FilterOCaml (Refiner.Refiner)

let loc = Ploc.dummy
let v x = Ploc.VaVal x
let flat t = String.concat " " (List.filter (( <> ) "") (String.split_on_char ' ' (String.map (fun c -> if c = '\n' then ' ' else c) (Simple_print.SimplePrint.string_of_term t))))
let opt f = function None -> "" | Some (Ploc.VaVal x) -> " (" ^ f x ^ ")" | Some (Ploc.VaAnt a) -> " $" ^ a ^ "$"
let e_s = function ExLid (_, Ploc.VaVal s) -> s | ExXtr (_, s, _) -> "ExXtr " ^ s | _ -> "<expr>"
let p_s = function PaLid (_, Ploc.VaVal s) -> s | PaXtr (_, s, _) -> "PaXtr " ^ s | _ -> "<patt>"
let mt_s = function MtLid (_, Ploc.VaVal s) -> s | MtXtr (_, s, _) -> "MtXtr " ^ s | _ -> "<module_type>"
let me_s = function MeUid (_, Ploc.VaVal s) -> s | MeXtr (_, s, _) -> "MeXtr " ^ s | _ -> "<module_expr>"
let ce_s = function CeXtr (_, s, _) -> "CeXtr " ^ s | _ -> "<class_expr>"
let si_s = function
  | SgVal (_, Ploc.VaVal s, _, _) -> "val " ^ s
  | SgXtr (_, s, o) -> "SgXtr " ^ s ^ opt (function SgVal (_, Ploc.VaVal s, _, _) -> "val " ^ s | _ -> "<sig_item>") o
  | _ -> "<sig_item>"
let st_s = function
  | StXtr (_, s, o) -> "StXtr " ^ s ^ opt (function StExp (_, e, _) -> e_s e | _ -> "<str_item>") o
  | StCls (_, Ploc.VaVal [ ci ]) -> "class " ^ (match ci.ciNam with Ploc.VaVal n -> n | _ -> "$") ^ " = " ^ ce_s ci.ciExp
  | StExp (_, e, _) -> e_s e
  | _ -> "<str_item>"
let back show f t = match f t with
  | x -> show x
  | exception Filter_ocaml.FormatError (m, _) -> "FormatError " ^ m
  | exception e -> "raises " ^ Printexc.to_string e
let case name mk show dest =
  let r = match mk () with
    | exception Refiner.Refiner.RefineError.RefineError (n, Refiner.Refiner.RefineError.StringError m) -> "refused (" ^ n ^ ": " ^ m ^ ")"
    | exception e -> "raises " ^ Printexc.to_string e
    | t -> flat t ^ "\n      back: " ^ back show dest t in
  Printf.printf "%-22s %s\n%!" name r

let x = ExLid (loc, v "x")
let () =
  case "ExXtr e" (fun () -> F.term_of_expr [] (ExXtr (loc, "e", None))) e_s F.expr_of_term;
  case "ExXtr e (x)" (fun () -> F.term_of_expr [] (ExXtr (loc, "e", Some (v x)))) (fun e -> e_s e ^ (match e with ExXtr (_, _, o) -> opt e_s o | _ -> "")) F.expr_of_term;
  case "PaXtr p" (fun () -> F.term_of_patt [] (PaXtr (loc, "p", None)) (fun _ -> F.term_of_expr [] x)) (fun (p, t) -> p_s p ^ " / tail " ^ flat t) F.patt_of_term;
  case "PaXtr p (y)" (fun () -> F.term_of_patt [] (PaXtr (loc, "p", Some (v (PaLid (loc, v "y"))))) (fun _ -> F.term_of_expr [] x))
    (fun (p, t) -> p_s p ^ (match p with PaXtr (_, _, o) -> opt p_s o | _ -> "") ^ " / tail " ^ flat t) F.patt_of_term;
  case "SgXtr s" (fun () -> F.term_of_sig_item (SgXtr (loc, "s", None))) si_s F.sig_item_of_term;
  case "SgXtr s (val y)" (fun () -> F.term_of_sig_item (SgXtr (loc, "s", Some (v (SgVal (loc, v "y", TyLid (loc, v "int"), v [])))))) si_s F.sig_item_of_term;
  case "StXtr t" (fun () -> F.term_of_str_item [] (StXtr (loc, "t", None))) st_s F.str_item_of_term;
  case "StXtr t (x)" (fun () -> F.term_of_str_item [] (StXtr (loc, "t", Some (v (StExp (loc, x, v [])))))) st_s F.str_item_of_term;
  case "MtXtr m" (fun () -> F.term_of_module_type (MtXtr (loc, "m", None))) mt_s F.module_type_of_term;
  case "MtXtr m (s)" (fun () -> F.term_of_module_type (MtXtr (loc, "m", Some (v (MtLid (loc, v "s")))))) (fun m -> mt_s m ^ (match m with MtXtr (_, _, o) -> opt mt_s o | _ -> "")) F.module_type_of_term;
  case "MeXtr n" (fun () -> F.term_of_module_expr [] (MeXtr (loc, "n", None))) me_s F.module_expr_of_term;
  case "MeXtr n (M)" (fun () -> F.term_of_module_expr [] (MeXtr (loc, "n", Some (v (MeUid (loc, v "M")))))) (fun m -> me_s m ^ (match m with MeXtr (_, _, o) -> opt me_s o | _ -> "")) F.module_expr_of_term;
  let cls ce = StCls (loc, v [ { ciLoc = loc; ciVir = v false; ciPrm = (loc, v []); ciNam = v "c"; ciExp = ce; ciAttributes = v [] } ]) in
  case "class c = CeXtr k" (fun () -> F.term_of_str_item [] (cls (CeXtr (loc, "k", None)))) st_s F.str_item_of_term;
  case "MeXtr n $a$" (fun () -> F.term_of_module_expr [] (MeXtr (loc, "n", Some (Ploc.VaAnt "a")))) me_s F.module_expr_of_term;
  case "(val x :> s)" (fun () -> F.term_of_module_expr [] (MeUnp (loc, x, None, Some (MtLid (loc, v "s"))))) me_s F.module_expr_of_term
