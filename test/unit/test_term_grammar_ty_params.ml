(* unit-link: filter *)
(*
 * Term_grammar.ty_param_of_param: the class a declaration gives a
 * parameter written without a cast (declare foo[3], foo["s"], foo[x]),
 * through the quote_term entry (ty_param).  No case reached it (the
 * 2026-11-15 rank: unit tests, theory build and proof census): the
 * theories cast every parameter they declare ([i:n], [s:s], ...).
 *
 * The grammar is instantiated as in test_term_grammar_params, with its
 * permissive parsing state.  Each line prints the parameter classes of
 * the declaration, or the exception.  The text can give a number, a
 * negative number, a string, a word (a meta-string: x and x' are both
 * one identifier), a token (a!b, which makes the unknown token class),
 * a level (x | y) and the quote (written "[ @ ]": "[@" is refused by
 * the lexer).  A cast parameter goes through cast_ty_param instead
 * (foo[3:n, x], foo[x, y:t]).
 *
 * Not reached, and why: the MNumber, MToken, Var, Shape, MShape,
 * Operator, MOperator, ObId and ParamList arms.  param_const makes only
 * Number, String, MString, Token, MLevel and Quote; the others come
 * from casts or from the Nuprl-5 link, never from this rule.
 *
 * The expected file is the output of the code as written (2026-11-15),
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

let ty_param = function
   TyNumber -> "TyNumber"
 | TyString -> "TyString"
 | TyToken t -> "TyToken " ^ Simple_print.SimplePrint.string_of_term t
 | TyShape -> "TyShape"
 | TyOperator -> "TyOperator"
 | TyLevel -> "TyLevel"
 | TyVar -> "TyVar"
 | TyQuote -> "TyQuote"

let rec exn_string = function
   Ploc.Exc (_, e) -> exn_string e
 | Refiner.Refiner.RefineError.RefineError (s, _) -> "RefineError " ^ s
 | Stream.Error s -> Printf.sprintf "Stream.Error(%S)" s
 | e -> Printexc.to_string e

let show s =
   match Grammar.Entry.parse Before.quote_term (Stream.of_string s) with
      { ty_params = ps; _ } ->
         Printf.printf "  %-22s [%s]\n" s (String.concat "; " (List.map ty_param ps))
    | exception e -> Printf.printf "  %-22s refused: %s\n" s (exn_string e)

let () =
   Grammar.error_verbose := false;
   List.iter show [
      "foo[3]"; "foo[-3]"; "foo[\"s\"]"; "foo[x]"; "foo[a!b]"; "foo[x']"; "foo[x | y]"; "foo[3 | x]";
      "foo[ @ ]"; "foo[1, @]"; "foo[3; x]"; "foo[3, x, \"s\"]"; "foo[3:n, x]"; "foo[x, y:t]"; "foo"
   ]
