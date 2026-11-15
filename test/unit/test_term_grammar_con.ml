(* unit-link: filter *)
(*
 * Term_grammar's term-constructor quotation (term_con_eoi, con_term: the
 * "bytecode" of Filter_type.term_constructor that the filter compiles to
 * OCaml), which no theory reaches on a bisect build at 008a9607e, nor any
 * unit test before this one.  On test_term_grammar_params's harness each
 * text is parsed by term_con_eoi and the constructor printed: the Con
 * constructors as written, an OCaml expression by a small printer of the
 * forms these productions build (a string, an identifier, a module path,
 * an application), anything else as <expr>.
 *
 * Read from the output, pinned as written:
 * - the constant-term form "!" term "!" (ConTerm) is refused in every
 *   shape tried: inside the term, the closing "!" is read as an opname
 *   separator (foo!bar) or as the start of the term form "!" var, so no
 *   text reaches its closing "!";
 * - "foo!bar" constructs the opname printed bar!foo (the opname's own
 *   order, innermost first);
 * - a cast to an unknown kind (foo[x:zz]) raises BadParamCast;
 * - a context with an empty argument list (<J[]>) is refused.
 *
 * Not reached here, a declared limit: the antiquotation forms ($e$,
 * '$v$, $v$. t, [$n$:n], [$int:n$], $h$: t, $list:hs$).  Their arms parse
 * an OCaml expression, and this harness does not load camlp5's OCaml
 * parser, so Pcaml.expr is empty and each is refused (two are printed).  The expected file is the
 * output of the code as written, never typed.
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

let rec longid = function
   MLast.LiUid (_, Ploc.VaVal s) -> s
 | MLast.LiAcc (_, l, Ploc.VaVal s) -> longid l ^ "." ^ s
 | _ -> "<longid>"

let rec ex = function
   MLast.ExStr (_, Ploc.VaVal (_, Ploc.VaVal s)) -> "\"" ^ s ^ "\""
 | MLast.ExLid (_, Ploc.VaVal s) -> s
 | MLast.ExInt (_, Ploc.VaVal s, _) -> s
 | MLast.ExLong (_, l) -> longid l
 | MLast.ExFle (_, e, Ploc.VaVal (None, Ploc.VaVal s)) -> ex e ^ "." ^ s
 | MLast.ExFle (_, e, Ploc.VaVal (Some (Ploc.VaVal l), Ploc.VaVal s)) -> ex e ^ "." ^ longid l ^ "." ^ s
 | MLast.ExApp (_, a, b) -> "(" ^ ex a ^ " " ^ ex b ^ ")"
 | _ -> "<expr>"

let shape = let open Term_sig in function
   ShapeNumber -> "n" | ShapeString -> "s" | ShapeLevel -> "l" | ShapeToken -> "t"
 | ShapeVar -> "v" | ShapeShape -> "sh" | ShapeOperator -> "op"

let param (p, sh) =
   (match p with
       ConPStr s -> "Str " ^ s
     | ConPMeta v -> "Meta " ^ Lm_symbol.string_of_symbol v
     | ConPNum n -> "Num " ^ Lm_num.string_of_num n
     | ConPInt e -> "Int " ^ ex e
     | ConPExpr e -> "Expr " ^ ex e
     | ConPToken o -> "Token " ^ Opname.string_of_opname o) ^ ":" ^ shape sh

let rec con = function
   ConTerm t -> "Term(" ^ P.string_of_term t ^ ")"
 | ConExpr e -> "Expr(" ^ ex e ^ ")"
 | ConVar e -> "Var(" ^ ex e ^ ")"
 | ConConstruct (o, ps, bts) ->
      "Construct(" ^ Opname.string_of_opname o ^ "; [" ^ String.concat ", " (List.map param ps) ^ "]; {"
      ^ String.concat "; " (List.map bterm bts) ^ "})"
 | ConSequent (a, hs, c) -> "Sequent(" ^ con a ^ "; " ^ String.concat "; " (List.map hyp hs) ^ " >- " ^ con c ^ ")"
and bterm (bvs, t) =
   String.concat "," (List.map (function ConBVarConst s -> s | ConBVarExpr e -> "$" ^ ex e) bvs)
   ^ (if bvs = [] then "" else ". ") ^ con t
and hyp = function
   ConContext (e, ts) -> "Context(" ^ ex e ^ "; " ^ String.concat ", " (List.map con ts) ^ ")"
 | ConHypList e -> "HypList(" ^ ex e ^ ")"
 | ConHypothesis (e, t) -> "Hyp(" ^ ex e ^ ": " ^ con t ^ ")"

let show s =
   match Grammar.Entry.parse Before.term_con_eoi (Stream.of_string s) with
      c -> Printf.printf "  %-34s %s\n" s (con c)
    | exception e -> Printf.printf "  %-34s refused: %s\n" s (exn_string e)

let () =
   Grammar.error_verbose := false;
   print_endline "terms:";
   List.iter show [ "!x!"; "! x !"; "!(x + y)!"; "!1!"; "!\"s\"!"; "!x{}!"; "!lam{x. x}!"; "!'x!"; "!(x)!"; "foo"; "foo!bar"; "foo[]"; "foo{}"; "foo{a; b}"; "foo{x. a}"; "foo{x, y. a}";
                    "foo[3]"; "foo[\"s\"]"; "foo[x:s]"; "foo[x:t]"; "foo[x:v]"; "foo[x:l]"; "foo[x:sh]"; "foo[x:op]";
                    "foo[x:zz]"; "foo[3]{a}" ];
   print_endline "antiquotations:";
   List.iter show [ "$e$"; "foo{$v$. a}" ];
   print_endline "sequents:";
   List.iter show [ "sequent { >- a }"; "sequent { x: a >- b }"; "sequent [arg] { a; b >- c }"; "sequent (arg) { >- }";
                    "sequent { <H> >- a }"; "sequent { <H>; <J[a; b]> >- c }"; "sequent { <J[]> >- c }";
                    "sequent { foo[3]{a} >- b }"; "sequent { foo >- b }" ]
