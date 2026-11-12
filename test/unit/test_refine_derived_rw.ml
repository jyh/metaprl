(* Derived and delayed rewrites in the refiner (refiner/refiner/refine.ml
   mk_rewrite_hack, delayed_rewrite / derived_rewrite and their extract
   check, delayed_cond_rewrite / derived_cond_rewrite, find_sentinal of a
   rewrite), which only the proof census reached (2026-11-11: 20 lines of
   refine.ml reached by the census and by no unit test, the open PRs'
   tests included).
   A rewrite  k --> c  is proved, as MetaPRL proves one, by a proof of its
   goal  mk_rewrite_hack (xrewrite{k; c})  (a sequent with the context H);
   here a primitive axiom whose goal is exactly that closes it.  A derived
   rewrite's proof is checked lazily, when compute_dependencies (or an
   extract) asks for it.  Every outcome printed is the code's own
   (measured 2026-11-11).
   Fixed cases:
     - mk_rewrite_hack adds the context H to every second-order variable;
     - a derived rewrite with a proof of its goal: its dependencies are the
       axiom; with a proof of another goal it is accepted, and refused when
       its dependencies are asked for; a delayed rewrite whose proof
       raises is Incomplete; a proof made under any_sentinal is refused;
     - a derived conditional rewrite: the proof's assumptions must be the
       conditions, each under mk_rewrite_hack;
     - find_sentinal of a rewrite and of a conditional rewrite is the
       refiner as they found it.
   Not covered: a condition with a variable that is bound where the
   rewrite applies (create_cond_rewrite's free-variable refusal). *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.Refine

let op s = Opname.make_opname [ s ]
let mk s ts = mk_simple_term (op s) ts
let k = mk "k" [] and c = mk "c" [] and d = mk "d" [] and q = mk "q" []
let sov x = mk_so_var_term (Lm_symbol.add x) [] []
let flat s = String.concat " " (List.filter (( <> ) "") (List.map String.trim (String.split_on_char '\n' s)))
let sp t = flat (Simple_print.SimplePrint.string_of_term t)
let hack redex contractum = mk_rewrite_hack (mk_xrewrite_term redex contractum)

let name = "test_refine_derived_rw"
let build = null_refiner name
let opname n = Opname.mk_opname n (op name)
let sentinel () = sentinal_of_refiner (refiner_of_build build)
let deps n = String.concat " " (List.sort compare (List.map (fun (_, o) -> List.hd (Opname.dest_opname o)) (compute_dependencies (refiner_of_build build) (opname n))))
let attempt label fn =
  Printf.printf "%-56s %s\n%!" label
    (try fn () with
     | RefineError.RefineError (n, RefineError.StringError s) -> "refused (" ^ n ^ ": " ^ s ^ ")"
     | RefineError.RefineError (n, _) -> "refused (" ^ n ^ ")"
     | Refine_sig.Incomplete o -> "Incomplete " ^ Opname.string_of_opname o
     | Invalid_argument s -> "Invalid_argument " ^ s
     | Failure s -> "Failure " ^ s)

(* an axiom whose goal is [goal], no subgoals *)
let axiom n goal =
  let mt = Term_sig.MetaTheorem goal in
  let tac = create_rule build n Rewrite.empty_args_spec [] mt in
  prim_rule build n Rewrite.empty_args_spec [] mt [] c;
  tac
(* a proof of the goal [goal] with assumptions [assums], by [tac] *)
let prove sent tac goal assums = snd (refine sent (tac Rewrite.empty_rw_args []) (mk_msequent goal assums))

let () =
  Printf.printf "%-56s %s\n" "mk_rewrite_hack (xrewrite{f{'a; 'b}; 'a})" (sp (hack (mk "f" [ sov "a"; sov "b" ]) (sov "a")));
  let ax = axiom "ax_kc" (hack k c) in
  let ax2 = axiom "ax_kd" (hack k d) in
  ignore (create_rewrite build "kc" k c);
  attempt "derived_rewrite k --> c, proved by ax_kc" (fun () ->
      derived_rewrite build "kc" k c (prove (sentinel ()) ax (hack k c) []); "accepted, depends on " ^ deps "kc");
  ignore (create_rewrite build "kc2" k c);
  attempt "derived_rewrite k --> c, proved by ax_kd (k --> d)" (fun () ->
      derived_rewrite build "kc2" k c (prove (sentinel ()) ax2 (hack k d) []); "accepted");
  attempt "  its dependencies" (fun () -> deps "kc2");
  ignore (create_rewrite build "kc3" k c);
  attempt "delayed_rewrite whose proof raises" (fun () ->
      delayed_rewrite build "kc3" k c (fun () -> failwith "no proof"); "accepted");
  attempt "  its dependencies" (fun () -> deps "kc3");
  ignore (create_rewrite build "kc4" k c);
  attempt "derived_rewrite proved under any_sentinal" (fun () ->
      derived_rewrite build "kc4" k c (prove any_sentinal ax (hack k c) []); "accepted");
  attempt "  its dependencies" (fun () -> deps "kc4");
  (* conditional: k --> c if q *)
  ignore (create_cond_rewrite build "ckc" Rewrite.empty_args_spec [] [ q ] k c);
  attempt "derived_cond_rewrite k --> c if q, assumption hack(q)" (fun () ->
      derived_cond_rewrite build "ckc" [] [ q ] k c (prove (sentinel ()) ax (hack k c) [ mk_rewrite_hack q ]); "accepted, depends on " ^ deps "ckc");
  ignore (create_cond_rewrite build "ckc2" Rewrite.empty_args_spec [] [ q ] k c);
  attempt "derived_cond_rewrite k --> c if q, assumption q (no hack)" (fun () ->
      derived_cond_rewrite build "ckc2" [] [ q ] k c (prove (sentinel ()) ax (hack k c) [ q ]); "accepted");
  attempt "  its dependencies" (fun () -> deps "ckc2");
  ignore (create_cond_rewrite build "ckc3" Rewrite.empty_args_spec [] [ q ] k c);
  attempt "delayed_cond_rewrite whose proof raises" (fun () ->
      delayed_cond_rewrite build "ckc3" [] [ q ] k c (fun () -> failwith "no proof"); "accepted, depends on " ^ deps "ckc3");
  (* find_sentinal of a rewrite: the refiner as it found it *)
  let applies sent tac goal = match refine sent (tac Rewrite.empty_rw_args []) (mk_msequent goal []) with _ -> "accepted" | exception RefineError.RefineError _ -> "refused" in
  let ax3 = axiom "ax_late" (hack d c) in
  attempt "find_sentinal kc: ax_kc (before kc)" (fun () -> applies (find_sentinal (refiner_of_build build) (opname "kc")) ax (hack k c));
  attempt "find_sentinal kc: ax_late (after kc)" (fun () -> applies (find_sentinal (refiner_of_build build) (opname "kc")) ax3 (hack d c));
  attempt "find_sentinal ckc: ax_kd (before ckc)" (fun () -> applies (find_sentinal (refiner_of_build build) (opname "ckc")) ax2 (hack k d));
  attempt "find_sentinal ckc: ax_late (after ckc)" (fun () -> applies (find_sentinal (refiner_of_build build) (opname "ckc")) ax3 (hack d c))
