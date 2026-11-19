(* unit-link: filter *)
(*
 * Term_grammar: a token cast to a shape or an operator (cast_shape and
 * cast_operator's Token arms), the successor of a constant parameter
 * (param_const "'", where a word cannot reach it: x' is one identifier),
 * and a sequent's argument written [| arg |], which nothing reached
 * (2026-11-18 rank737: term grammar arms missed by the unit tests, the
 * theory build and the census; briefs list).  The grammar and parsing
 * state are test_term_grammar_params', its parameter printer naming a
 * shape's and an operator's opname.  Each line prints the parameters (or
 * the sequent's argument), or the exception.
 * Read from the output: a token a!b cast to a shape or an operator keeps
 * its opname (printed innermost first, b!a); a number cast to a shape is
 * refused; 3' is the level 4, and "s"' is refused; [| arg |] wraps the
 * argument in sequent_arg{...}, where [ arg ] uses it as written.
 * The expected file is the output of the code as written (2026-11-18),
 * never typed.  Mutants (2026-11-18, each rebuilt and relinked; an
 * identity control unchanged): the two Token arms refused, the successor
 * not incremented, the [| |] argument dropped: 4 of 4 RED.
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

let level l =
   let { Term_sig.le_const = c; Term_sig.le_vars = vars } = dest_level l in
   let var v =
      let { Term_sig.le_var = x; Term_sig.le_offset = k } = dest_level_var v in
         Lm_symbol.string_of_symbol x ^ (if k = 0 then "" else "+" ^ string_of_int k)
   in
      "max(" ^ String.concat ", " (string_of_int c :: List.map var vars) ^ ")"

let kind p =
   match dest_param p with
      Number n -> "Number " ^ Lm_num.string_of_num n
    | String s -> "String " ^ s
    | Token t -> "Token " ^ Opname.string_of_opname t
    | Var v -> "Var " ^ Lm_symbol.string_of_symbol v
    | MNumber v -> "MNumber " ^ Lm_symbol.string_of_symbol v
    | MString v -> "MString " ^ Lm_symbol.string_of_symbol v
    | MToken v -> "MToken " ^ Lm_symbol.string_of_symbol v
    | MLevel l -> "MLevel " ^ level l
    | MShape v -> "MShape " ^ Lm_symbol.string_of_symbol v
    | MOperator v -> "MOperator " ^ Lm_symbol.string_of_symbol v
    | Shape sh -> "Shape " ^ Opname.string_of_opname sh.Term_sig.shape_opname
    | Operator op -> "Operator " ^ Opname.string_of_opname op.Term_sig.opparam_name
    | Quote -> "Quote"
    | ObId _ | ParamList _ -> "Nuprl5"

let rec exn_string = function
   Ploc.Exc (_, e) -> exn_string e
 | Refiner.Refiner.RefineError.RefineError (s, _) -> "RefineError " ^ s
   (* By name: OCaml 4.14 prints the stdlib's as Stdlib.Stream.Error, 5.x camlp-streams' as Stream.Error. *)
 | Stream.Error s -> Printf.sprintf "Stream.Error(%S)" s
 | e -> Printexc.to_string e

let show s =
   match Grammar.Entry.parse Before.term_eoi (Stream.of_string s) with
      t ->
         let ps = (dest_op (dest_term t).Term_sig.term_op).Term_sig.op_params in
            Printf.printf "  %-20s [%s]\n" s (String.concat "; " (List.map kind ps))
    | exception e -> Printf.printf "  %-20s refused: %s\n" s (exn_string e)

let () =
   Grammar.error_verbose := false;
   print_endline "a token, an operator and a shape cast:";
   List.iter show [ "foo[a!b:sh]"; "foo[a!b:op]"; "foo[a!b!c:sh]"; "foo[a!b:t]"; "foo[3:sh]" ];
   print_endline "the successor of a constant:";
   List.iter show [ "foo[3']"; "foo[3'']"; "foo[\"s\"']"; "foo[3' | x:l]" ];
   print_endline "a sequent with an argument:";
   List.iter (fun s ->
      match Grammar.Entry.parse Before.term_eoi (Stream.of_string s) with
         t -> Printf.printf "  %-26s %s\n" s (Simple_print.SimplePrint.string_of_term (explode_sequent t).sequent_args)
       | exception e -> Printf.printf "  %-26s refused: %s\n" s (exn_string e))
      [ "sequent [arg] { >- a }"; "sequent [f{x}] { y: b >- a }"; "sequent [|arg|] { >- a }"; "sequent [|f{x}|] { y: b >- a }"; "sequent { >- a }" ]
