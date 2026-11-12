(* unit-link: filter *)
(*
 * Term_grammar's parameters: the [value:kind] casts of the quotation
 * syntax, and dest_xparam on the terms base_grammar's generic term
 * parser builds (theories/meta/base/base_grammar.mli, xterm_param).
 *
 * The grammar is instantiated here with its own entries and a permissive
 * parsing state: every opname is accepted as written, so a token class
 * that does not exist is not refused (the filter's own state checks
 * that), and no type is checked.  Each line prints the parameters the
 * text or the term gives, or the exception (inside Ploc.Exc).
 *
 * On a bisect build at 008a9607e the theory build and the proof census
 * reach none of the casts from a number or a string, and no xparam
 * succ or max.
 *
 * The expected file is the output of the code.  Before the fix that
 * followed this test, Term_grammar named xparam_succ_opname
 * "xparam_string", so the term xparam_succ{p} that base_grammar builds
 * for p' was refused as "not a parameter" (i', i'', 2', i' | 2).
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
    | Shape _ -> "Shape"
    | Operator _ -> "Operator"
    | Quote -> "Quote"
    | ObId _ | ParamList _ -> "Nuprl5"

let rec exn_string = function
   Ploc.Exc (_, e) -> exn_string e
 | Refiner.Refiner.RefineError.RefineError (s, _) -> "RefineError " ^ s
 | e -> Printexc.to_string e

let show s =
   match Grammar.Entry.parse Before.term_eoi (Stream.of_string s) with
      t ->
         let ps = (dest_op (dest_term t).Term_sig.term_op).Term_sig.op_params in
            Printf.printf "  %-20s [%s]\n" s (String.concat "; " (List.map kind ps))
    | exception e -> Printf.printf "  %-20s refused: %s\n" s (exn_string e)

let () =
   print_endline "casts in quotation text:";
   List.iter show [
      "foo[3:n]"; "foo[x:n]"; "foo[\"s\":n]";
      "foo[3:s]"; "foo[\"s\":s]"; "foo[x:s]";
      "foo[3:t]"; "foo[\"s\":t]"; "foo[x:t]";
      "foo[3:v]"; "foo[\"s\":v]"; "foo[x:v]";
      "foo[3:l]"; "foo[x:l]"; "foo[x':l]"; "foo[x'':l]"; "foo[\"s\":l]";
      "foo[x:sh]"; "foo[\"s\":sh]";
      "foo[x:op]"; "foo[3:op]";
      "foo[x:cls]"; "foo[3:cls]";
   ]

(* dest_xparam on the terms base_grammar's generic term parser builds. *)
let perv = Opname.mk_opname "Perv" Opname.nil_opname
let xop s = Opname.mk_opname s perv
let x_int n = mk_number_term (xop "xparam_int") (Lm_num.num_of_int n)
let x_neg n = mk_number_term (xop "xparam_neg") (Lm_num.num_of_int n)
let x_str s = mk_string_term (xop "xparam_string") s
let x_id s = mk_string_term (xop "xparam_id") s
let x_succ t = mk_dep0_term (xop "xparam_succ") t
let x_max a b = mk_dep0_dep0_term (xop "xparam_max") a b
let xparam t = mk_dep0_term (xop "xparam") t

let showx name t =
   match TG.dest_xparam Ploc.dummy t with
      p -> Printf.printf "  %-14s %s\n" name (kind p)
    | exception e -> Printf.printf "  %-14s refused: %s\n" name (exn_string e)

let () =
   print_endline "dest_xparam on base_grammar's terms:";
   showx "3" (xparam (x_int 3));
   showx "-3" (xparam (x_neg 3));
   showx "\"s\"" (xparam (x_str "s"));
   showx "i" (xparam (x_id "i"));
   showx "i'" (xparam (x_succ (x_id "i")));
   showx "i''" (xparam (x_succ (x_succ (x_id "i"))));
   showx "2'" (xparam (x_succ (x_int 2)));
   showx "i | j" (xparam (x_max (x_id "i") (x_id "j")));
   showx "i' | 2" (xparam (x_max (x_succ (x_id "i")) (x_int 2)));
   showx "i | 3" (xparam (x_max (x_id "i") (x_int 3)))
