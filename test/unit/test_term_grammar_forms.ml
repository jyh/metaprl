(* unit-link: filter *)
(*
 * Term_grammar's quotation syntax, the forms no theory reaches: on a bisect
 * build at 008a9607e (unit tests at a59ded9a5) the theory build and the
 * proof census reach none of the productions below, and the coverage
 * rank (STATUS row 595) put the grammar after parse_quoted_term first.
 * The operator spellings (^< ^> ^<= ^>= ^<> ^+ ^- ^* ^/ ^^ ^@ <- In
 * forany thereis), the algebraic forms on a named structure (t1 <[g] t2,
 * t1 -[g] t2, ...), "open e1 in e2", "e2 where x = e1", the bounded
 * quantifiers (all x In A. B), and the meta arrows with a named premise
 * (x: A --> B, B <-- x: A, A <--> B).
 *
 * Read from the output, pinned as written:
 * - no "open" text tried parses: its e1 is SELF, which reads "e1 in e2"
 *   as a membership and then wants another "in" (let's e1 is NEXT);
 * - a plain "a / b" is refused: "/" has only the "/[g]" form;
 * - "a +: f b" and "a *: f b" drop the operator name (union, prod): the
 *   name is used only by the [g] forms;
 * - the existential's keyword is "exst", so "exists x In A. B" is refused.
 * The meta-terms are parsed by mterm, which has no end-of-input check.
 *
 * The grammar is instantiated with its own entries and the permissive
 * parsing state of test_term_grammar_params (every opname accepted as
 * written, no type checked).  Each line prints the term the text gives
 * (Simple_print) or the exception.  The expected file is the output of
 * the code as written, never typed.
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
 | Refiner.Refiner.RefineError.RefineError (s, _) -> "RefineError " ^ s
   (* By name: OCaml 4.14 prints the stdlib's as Stdlib.Stream.Error, 5.x camlp-streams' as Stream.Error. *)
 | Stream.Error s -> Printf.sprintf "Stream.Error(%S)" s
 | e -> Printexc.to_string e

let show s =
   match Grammar.Entry.parse Before.term_eoi (Stream.of_string s) with
      t -> Printf.printf "  %-24s %s\n" s (P.string_of_term t)
    | exception e -> Printf.printf "  %-24s refused: %s\n" s (exn_string e)

(* The meta-term's structure, constructor by constructor. *)
let rec mstr = function
   Term_sig.MetaTheorem t -> "Theorem(" ^ P.string_of_term t ^ ")"
 | MetaImplies (a, b) -> "Implies(" ^ mstr a ^ ", " ^ mstr b ^ ")"
 | MetaFunction (v, a, b) -> "Function(" ^ P.string_of_term v ^ ", " ^ mstr a ^ ", " ^ mstr b ^ ")"
 | MetaIff (a, b) -> "Iff(" ^ mstr a ^ ", " ^ mstr b ^ ")"
 | MetaLabeled (l, a) -> "Labeled(" ^ l ^ ", " ^ mstr a ^ ")"

let show_m s =
   match Grammar.Entry.parse Before.mterm (Stream.of_string s) with
      t -> Printf.printf "  %-24s %s\n" s (mstr t)
    | exception e -> Printf.printf "  %-24s refused: %s\n" s (exn_string e)

let () =
   (* camlp5 also prints each parse error's rule on stderr: the exception is what this test reads. *)
   Grammar.error_verbose := false;
   print_endline "relations and operations on self:";
   List.iter show [ "a ^= b"; "a ^< b"; "a ^> b"; "a ^<= b"; "a ^>= b"; "a ^<> b";
                    "a ^+ b"; "a ^- b"; "a ^* b"; "a ^/ b"; "a ^^ b" ];
   print_endline "on a named structure g:";
   List.iter show [ "a =[g] b"; "a <>[g] b"; "a <[g] b"; "a >=[g] b"; "a +[g] b"; "a -[g] b";
                    "a *[g] b"; "a /[g] b"; "a ^[g] b" ];
   print_endline "integer and other operators:";
   List.iter show [ "a ^@ b"; "a <- b"; "a In b"; "a +: f b"; "a *: f b"; "a *. b"; "a / b";
                    "a =@ b"; "a <>@ b"; "a %@ b"; "a :: b"; "a +: f [g] b"; "a *: f [g] b" ];
   print_endline "records:";
   List.iter show [ "r ^ lab"; "r ^ lab := t"; "^ lab"; "^ lab := t"; "a := b" ];
   print_endline "binders:";
   List.iter show [ "open e1 in e2"; "open a in T in e2"; "open (e1) in e2"; "(open e1) in e2"; "e2 where x = e1"; "let x = e1 in e2";
                    "all x In A. B"; "exst x In A. B"; "exists x In A. B"; "all x. B"; "forany A. B"; "thereis A. B" ];
   print_endline "meta-terms:";
   List.iter show_m [ "A --> B"; "x: A --> B"; "B <-- A"; "B <-- x: A"; "A <--> B"; "[l] A --> B"; "x: A --> y: B --> C" ]
