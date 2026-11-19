(* unit-link: filter *)
(* Filter_cache_fun's declarations in a fresh cache, through the exported
   declare_typeclass, declare_type, declare_term, declare_type_rewrite and
   hash.  The theory build reaches these only on success; nothing reached
   (2026-11-15 rank: unit tests, theory build, proof census) a term
   declared twice (check_redeclaration's "redefining term"), a term whose
   type was never declared (declare_term_env's "type not found"), or a
   cache holding a type rewrite (hash_typereductions: no theory declares
   one).  Here K is a typeclass under the builtin Ty, T and U are types in
   K, a is a term of type T; each declaration prints ok or its Failure.
   Then hashes are compared, never printed: the same declarations give the
   same hash, and a rewrite T <--> U changes it (against none, and against
   U <--> T).
   Not reached, stated: check_redeclaration's "shape class does not match
   the interface" (every exported declaration watches, so a second one
   fails as a redefinition first; only an inlined parent declares without
   watching).
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

let () =
  let info = fresh () in
  say "typeclass K : Ty" (fun () -> S.declare_typeclass info Filter_shape.shape_normal (op "K") Term_ty_infer.type_opname ParentNone);
  say "type T : K" (fun () -> S.declare_type info Filter_shape.shape_normal (ty (t "T") (t "K")) (op "K"));
  say "type U : K" (fun () -> S.declare_type info Filter_shape.shape_normal (ty (t "U") (t "K")) (op "K"));
  say "term a : T" (fun () -> S.declare_term info Filter_shape.shape_normal (ty (t "a") (t "T")));
  say "term a : T again" (fun () -> S.declare_term info Filter_shape.shape_normal (ty (t "a") (t "T")));
  say "term b : Missing" (fun () -> S.declare_term info Filter_shape.shape_normal (ty (t "b") (t "Missing")));
  let h0 = S.hash info in
  say "type rewrite T <--> U" (fun () -> S.declare_type_rewrite info (t "T") (t "U"));
  let h1 = S.hash info in
  Printf.printf "hash changed by the type rewrite: %b\n" (h0 <> h1)

let () =
  let a = setup () and b = setup () and c = setup () and d = setup () in
  S.declare_type_rewrite a (t "T") (t "U");
  S.declare_type_rewrite b (t "T") (t "U");
  S.declare_type_rewrite c (t "U") (t "T");
  Printf.printf "same declarations, same hash: %b\n" (S.hash a = S.hash b);
  Printf.printf "the rewrite reversed, a different hash: %b\n" (S.hash a <> S.hash c);
  Printf.printf "no rewrite, a different hash: %b\n" (S.hash a <> S.hash d)
