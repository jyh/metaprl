(* Refine_exn, the printer of every refusal in the proof editor and the
   toploop: format_refine_error on each refine_error constructor that no
   test prints (2026-11-11 reach census: 191 of refine_exn.ml's 278 points
   reached by nothing; test_refine_exn_format covers StringIntError,
   StringStringError, StringVarError, StringTermError and RewriteBadMatch),
   the wrapped forms nested, format_exn on each exception kind it names,
   and print_exn / stderr_exn.
   Each error is printed with Dform.null_base at width 200; the nesting
   forms also at width 30, to show the layout.  print_exn and stderr_exn
   print to stderr and then re-raise: the exception itself when
   OCAMLRUNPARAM holds 'b' (Refine_exn.backtrace), otherwise a
   ToploopIgnoreError / ToploopIgnoreExn wrapper; the line says whether
   the raise is the documented one, so it does not depend on the
   environment.  The text is the code's own (measured 2026-11-11). *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError

let op s = Opname.make_opname [ s ]
let v = Lm_symbol.add
let a = mk_simple_term (op "a") []
let g x = mk_simple_term (op "g") [ x ]
let num n = make_param (Term_sig.Number (Lm_num.num_of_int n))
let shape = { Term_sig.shape_opname = op "g"; shape_params = [ Term_sig.ShapeNumber ]; shape_arities = [ 0 ] }
let addr = TermAddr.make_address [ Term_addr_sig.Subterm 1; Term_addr_sig.Subterm 2 ]
let mt = Term_sig.MetaImplies (Term_sig.MetaTheorem a, Term_sig.MetaTheorem (g a))
let print w f = let buf = Lm_rformat.new_buffer () in match f buf with () -> Lm_rformat_text.print_text_string w buf | exception e -> "raised " ^ Printexc.to_string e
let say fmt = Printf.ksprintf (fun s -> print_string s; flush stdout) fmt

let flat = [
  "GenericError", GenericError;
  "ToploopIgnoreError", ToploopIgnoreError;
  "StringError", StringError "no rule applies";
  "IntError", IntError 4;
  "TermError", TermError (g a);
  "AddressError", AddressError (addr, g a);
  "TermMatchError", TermMatchError (g a, "not a lambda");
  "TermPairError", TermPairError (a, g a);
  "MetaTermMatchError", MetaTermMatchError mt;
  "RewriteFreeSOVar", RewriteFreeSOVar (v "B");
  "RewriteSOVarArity", RewriteSOVarArity (v "B");
  "RewriteBoundParamVar", RewriteBoundParamVar (v "n");
  "RewriteFreeParamVar", RewriteFreeParamVar (v "n");
  "RewriteBadRedexParam", RewriteBadRedexParam (num 3);
  "RewriteNoRuleOperator", RewriteNoRuleOperator;
  "RewriteAllSOInstances", RewriteAllSOInstances (v "B");
  "RewriteMissingContextArg", RewriteMissingContextArg (v "H");
  "RewriteStringError", RewriteStringError "bad redex";
  "RewriteStringOpnameOpnameError", RewriteStringOpnameOpnameError ("mismatch", op "f", op "g");
  "RewriteFreeContextVar", RewriteFreeContextVar (v "H", v "x");
  "VarError", VarError (v "x");
  "OpnameError", OpnameError (op "f");
  "Opname2Error", Opname2Error (op "f", op "g");
  "ParamError", ParamError (num 3);
  "Param2Error", Param2Error (num 3, num 4);
  "ParamTyParamError", ParamTyParamError (num 3, Term_ty_sig.TyString);
  "ShapeError", ShapeError shape;
  "Shape2Error", Shape2Error (shape, { shape with Term_sig.shape_arities = [ 1 ] });
  "Term2Error", Term2Error (a, g a);
  "VarTermError", VarTermError (v "x", g a);
  "IntTermError", IntTermError (2, g a);
]

let inner = StringError "inner"
let nested = [
  "StringWrapError", StringWrapError ("outer", inner);
  "SubgoalError", SubgoalError (2, "subgoal", inner);
  "PairError", PairError ("left", StringError "l", "right", IntError 7);
  "NodeError", NodeError ("node", g a, [ "first", StringError "one"; "second", IntError 2 ]);
  "NodeError with no children", NodeError ("node", g a, []);
  "RewriteAddressError", RewriteAddressError (addr, "at", inner);
  "StringErrorError", StringErrorError ("outer", inner);
  "VarErrorError", VarErrorError (v "x", inner);
  "IntErrorError", IntErrorError (3, inner);
  "TermErrorError", TermErrorError (g a, inner);
  "OpnameErrorError", OpnameErrorError (op "f", inner);
  "ShapeErrorError", ShapeErrorError (shape, inner);
  "ParamErrorError", ParamErrorError (num 3, inner);
  "MetaTermErrorError", MetaTermErrorError (mt, inner);
  "three deep", StringErrorError ("a", IntErrorError (1, VarErrorError (v "y", StringError "bottom")));
]

let () =
  List.iter (fun (name, e) -> say "%-32s %S\n" name (print 200 (fun buf -> Refine_exn.format_refine_error Dform.null_base buf "fn" e))) flat;
  say "== nested\n";
  List.iter (fun (name, e) ->
      say "%-32s %S\n%-32s %S\n" name (print 200 (fun buf -> Refine_exn.format_refine_error Dform.null_base buf "fn" e))
        "  at width 30" (print 30 (fun buf -> Refine_exn.format_refine_error Dform.null_base buf "fn" e))) nested;
  say "== format_exn\n";
  let loc = Lm_location.bogus_loc "test" in
  List.iter (fun (name, x) -> say "%-32s %S\n" name (print 200 (fun buf -> Refine_exn.format_exn Dform.null_base buf x))) [
    "RefineError", RefineError ("fn", IntError 1);
    "RefineForceError", RefineForceError ("debug info", "fn", IntError 1);
    "Incomplete", Refine_sig.Incomplete (Opname.make_opname [ "thm"; "theory" ]);
    "Invalid_argument", Invalid_argument "bad";
    "Failure", Failure "failed";
    "Lm_parser.ParseError", Lm_parser.ParseError (loc, "unexpected token");
    "Not_found", Not_found;
    "ToploopIgnoreExn", Refine_exn.ToploopIgnoreExn Not_found;
  ];
  say "== print_exn and stderr_exn (the message goes to stderr)\n";
  let check name f x =
    let documented = function
      | RefineError (s, ToploopIgnoreError) when not Refine_exn.backtrace -> (match x with RefineError (s', _) -> s = s' | _ -> false)
      | Refine_exn.ToploopIgnoreExn e when not Refine_exn.backtrace -> e == x
      | e -> Refine_exn.backtrace && e == x in
    (match f x with
     | _ -> say "%-32s returned\n" name
     | exception e -> prerr_string ""; flush stderr; say "%-32s re-raised as documented: %b\n" name (documented e)) in
  check "print_exn, RefineError" (fun x -> Refine_exn.print_exn Dform.null_base (fun () -> raise x) ()) (RefineError ("fn", StringError "s"));
  check "print_exn, Failure" (fun x -> Refine_exn.print_exn Dform.null_base (fun () -> raise x) ()) (Failure "f");
  check "stderr_exn, RefineError" (fun x -> Refine_exn.stderr_exn x) (RefineError ("fn", IntError 2));
  check "stderr_exn, Not_found" (fun x -> Refine_exn.stderr_exn x) Not_found;
  say "%-32s %d\n" "print_exn, no exception" (Refine_exn.print_exn Dform.null_base (fun x -> x + 1) 41)
