(* unit-link: filter *)
(* Filter_cache_fun.mk_opname_kind, the opname lookup the term parser uses
   (a cache's parsing state), in a fresh cache set up as in
   test_filter_cache_decl (typeclass K, types T and U, term a : T).  Nothing
   reached its refusals (2026-11-16 rank): no names, an undeclared name, a
   name declared with another kind (a token), and a module path that names
   no module.  Each line prints the opname found or the exception (the
   parsing state wraps it in Ploc.Exc; this prints the inner one).
   Not reached, stated: a module path that does name one (expand_path
   needs an inlined parent module; the theory build reaches it).
   The expected file is the output of the code as written (2026-11-16),
   never typed. *)
open Filter_type
open Refiner.Refiner.Term

module C = Filter_cache.MakeCaches (Proof_convert.Convert)
module S = C.StrFilterCache

let op s = Opname.make_opname [ s; "Fcd" ]
let t s = mk_simple_term (op s) []
let ty term ty = { Term_ty_sig.ty_term = term; ty_opname = Refiner.Refiner.Term.opname_of_term term; ty_params = []; ty_bterms = []; ty_type = ty }
let try_s f = try f (); "ok" with Failure s -> "Failure " ^ String.concat " " (String.split_on_char '\n' s) | e -> "raised " ^ Printexc.to_string e
let say name f = Printf.printf "%-34s %s\n%!" name (try_s f)

let fresh () =
  let info = S.create_cache (S.create [ "." ]) "m" ImplementationType in
  S.set_mode info InteractiveSummary; info

let setup () =
  let info = fresh () in
  S.declare_typeclass info Filter_shape.shape_normal (op "K") Term_ty_infer.type_opname ParentNone;
  S.declare_type info Filter_shape.shape_normal (ty (t "T") (t "K")) (op "K");
  S.declare_type info Filter_shape.shape_normal (ty (t "U") (t "K")) (op "K");
  info

let so = function None -> "-" | Some o -> Opname.string_of_opname o
let name names kind info =
  let ps = S.get_parsing_state info in
  let rec ex = function Ploc.Exc (_, e) -> ex e | Failure m -> "Failure " ^ m | Invalid_argument m -> "Invalid_argument " ^ m | e -> Printexc.to_string e in
  try "opname " ^ Opname.string_of_opname (ps.mk_opname_kind Ploc.dummy kind names [] []) with e -> ex e
let () =
  let info = setup () in
  S.declare_term info Filter_shape.shape_normal (ty (t "a") (t "T"));
  ignore so;
  List.iter (fun (lbl, names, kind) -> Printf.printf "%-28s %s\n%!" lbl (name names kind info))
    [ "[] ", [], NormalKind;
      "[a]", [ "a" ], NormalKind;
      "[a] as a token", [ "a" ], TokenKind;
      "[T]", [ "T" ], NormalKind;
      "[K]", [ "K" ], NormalKind;
      "[b] (undeclared)", [ "b" ], NormalKind;
      "[Fcd; a]", [ "Fcd"; "a" ], NormalKind;
      "[M; a]", [ "M"; "a" ], NormalKind;
      "[m; a]", [ "m"; "a" ], NormalKind ]
