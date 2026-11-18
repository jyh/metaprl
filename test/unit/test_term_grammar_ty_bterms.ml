(* unit-link: filter *)
(*
 * Term_grammar's typed subterms of a declaration (ty_bterm, make_ty_term
 * and make_ty_bvar), through the quote_term entry: foo{x}, foo{x : T},
 * foo{x. t}, foo{. t}.  No case reached make_ty_term (2026-11-16 rank:
 * unit tests, theory build, proof census).  The grammar is instantiated
 * as in test_term_grammar_ty_params.  Each line prints the declared term
 * and each subterm's type (with its bound variables' types before a
 * "."), or the refusal.
 * Read from the output: two heads with no body (foo{x, y}) are refused as
 * "illegal bterm"; an untyped subterm has $unknown!type and an untyped
 * bound variable $unknown!bvar; a constraint after a body ("x. bar : U")
 * is refused by the term parser.
 * The expected file is the output of the code as written (2026-11-16),
 * never typed.
 *)
open Filter_type
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Term_ty_sig

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

let rec exn_string = function
   Ploc.Exc (_, e) -> exn_string e
 | Refiner.Refiner.RefineError.RefineError (s, _) -> "RefineError " ^ s
 | Stream.Error s -> Printf.sprintf "Stream.Error(%S)" s
 | e -> Printexc.to_string e

let st t = String.concat " " (String.split_on_char '\n' (Simple_print.SimplePrint.string_of_term t))
let show s =
   match Grammar.Entry.parse Before.quote_term (Stream.of_string s) with
      { ty_term = t; ty_bterms = bs; _ } ->
         Printf.printf "  %-26s %s : [%s]\n" s (st t)
           (String.concat "; " (List.map (fun b -> (if b.ty_bvars = [] then "" else String.concat ", " (List.map st b.ty_bvars) ^ ". ") ^ st b.ty_bterm) bs))
    | exception e -> Printf.printf "  %-26s refused: %s\n" s (exn_string e)

let () =
   Grammar.error_verbose := false;
   List.iter show [
      "foo{x}"; "foo{'x}"; "foo{\"s\"}"; "foo{bar}"; "foo{bar{x}}"; "foo{x : T}"; "foo{'x : T}"; "foo{x; y : T}";
      "foo{x, y}"; "foo{x : T, y}"; "foo{x. bar}"; "foo{x : T. bar}"; "foo{. bar}"; "foo{x. bar : U}"
   ]
