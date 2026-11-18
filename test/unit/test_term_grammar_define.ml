(* unit-link: filter *)
(*
 * Term_grammar's parse_define and parse_type_rewrite (what a theory's
 * "define" and type-rewrite declarations go through, filter_parse.ml) and
 * mk_type_term's named-binder arm (x: A -> B, x: A * B, x: A isect B),
 * which no unit test reached (bisect at a45cd0437).  The grammar and its
 * permissive parsing state are test_term_grammar_forms' (every opname
 * accepted as written, no type checked), so what is checked here is the
 * grammar's own work and the refiner's (Refine.check_definition,
 * Refine.check_rewrite).  Each line prints the term(s) or the exception.
 * The expected file is the output of the code as written, never typed.
 *)
open Filter_type
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermOp

let the_state = ref None

module Before : TermGrammarSig =
struct
   let parsing_state _ = match !the_state with Some s -> s | None -> failwith "no parsing state"
   let gram              = Pcaml.gram
   let opname            = Grammar.Entry.create gram "opname"
   let opname_name       = Grammar.Entry.create gram "opname_name"
   let term_eoi          = Grammar.Entry.create gram "term_eoi"
   let term              = Grammar.Entry.create gram "term"
   let parsed_term       = Grammar.Entry.create gram "parsed_term"
   let quote_term        = Grammar.Entry.create gram "quote_term"
   let mterm             = Grammar.Entry.create gram "mterm"
   let bmterm            = Grammar.Entry.create gram "mterm"
   let singleterm        = Grammar.Entry.create gram "singleterm"
   let parsed_bound_term = Grammar.Entry.create gram "bound_term"
   let xdform            = Grammar.Entry.create gram "xdform"
   let term_con_eoi      = Grammar.Entry.create gram "term_con_eoi"
end

module TG = Term_grammar.MakeTermGrammar (Before)

let () =
   the_state := Some {
      opname_prefix = (fun _ -> Opname.nil_opname);
      mk_opname_kind = (fun _ _ names _ _ -> Opname.make_opname names);
      find_shape_class = (fun _ _ -> Filter_shape.shape_normal);
      mk_var_contexts = (fun _ _ _ -> None);
      infer_term = (fun _ t -> t);
      check_rule = (fun _ _ _ -> ());
      check_rewrite = (fun _ _ _ -> ());
      check_type_rewrite = (fun _ _ _ -> ());
      check_dform = (fun _ _ _ -> ());
      check_iform = (fun _ _ -> ());
      check_production = (fun _ _ _ -> ());
      check_input_term = (fun _ _ -> ());
      check_input_mterm = (fun _ _ -> ());
      allow_seq_bindings = (fun _ _ -> true);
      apply_iforms = (fun _ _ t -> t);
      apply_iforms_mterm = (fun _ _ mt args -> mt, args);
      term_of_string = (fun _ _ _ _ -> failwith "term_of_string");
   }

module P = Simple_print.SimplePrint

let rec exn_string = function
   Ploc.Exc (_, e) -> exn_string e
 | Refiner.Refiner.RefineError.RefineError (s, (Refiner.Refiner.RefineError.StringTermError (m, _) | Refiner.Refiner.RefineError.StringError m)) -> "RefineError " ^ s ^ " (" ^ m ^ ")"
 | Refiner.Refiner.RefineError.RefineError (s, _) -> "RefineError " ^ s
   (* By name: OCaml 4.14 prints the stdlib's as Stdlib.Stream.Error, 5.x camlp-streams' as Stream.Error. *)
 | Stream.Error s -> Printf.sprintf "Stream.Error(%S)" s
 | e -> Printexc.to_string e

let show s =
   match Grammar.Entry.parse Before.term_eoi (Stream.of_string s) with
      t -> Printf.printf "  %-24s %s\n" s (P.string_of_term t)
    | exception e -> Printf.printf "  %-24s refused: %s\n" s (exn_string e)

(* A parsed term, as a "term" quotation in a theory gives one. *)
let pt s = TG.parse_quotation Ploc.dummy "top" "term" s

let show s =
   match Grammar.Entry.parse Before.term_eoi (Stream.of_string s) with
      t -> Printf.printf "  %-34s %s\n" s (P.string_of_term t)
    | exception e -> Printf.printf "  %-34s refused: %s\n" s (exn_string e)

let pair name f r c =
   Printf.printf "  %-34s %s\n" name
      (match f (pt r) (pt c) with
          (a, b) -> P.string_of_term a ^ "  ==  " ^ P.string_of_term b
        | exception e -> "refused: " ^ exn_string e)

let () =
   Grammar.error_verbose := false;
   print_endline "mk_type_term (named binder, then plain):";
   List.iter show [ "x: A -> B"; "A -> B"; "x: A * B"; "A * B"; "x: A isect B"; "A isect B" ];
   let loc = Ploc.dummy in
   print_endline "parse_define:";
   pair "d{'a} <--> f{'a; 'a}" (TG.parse_define loc "d") "d{'a}" "f{'a; 'a}";
   pair "d{'a} <--> g{d{'a}} (recursive)" (TG.parse_define loc "d") "d{'a}" "g{d{'a}}";
   pair "d{'a} <--> 'b (free variable)" (TG.parse_define loc "d") "d{'a}" "'b";
   pair "'a <--> c (a variable redex)" (TG.parse_define loc "d") "'a" "c";
   pair "d{f{'a}} <--> 'a (a nested redex)" (TG.parse_define loc "d") "d{f{'a}}" "'a";
   print_endline "parse_type_rewrite:";
   pair "Opt{'a} <--> List{'a}" (TG.parse_type_rewrite loc) "Opt{'a}" "List{'a}";
   pair "Opt{'a} <--> 'b (free variable)" (TG.parse_type_rewrite loc) "Opt{'a}" "'b"
