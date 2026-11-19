(* Rewrite_build_contractum.build_contractum_param (refiner/rewrite): a
   parameter matched in the redex as one kind and used in the contractum
   as another, which nothing reached (2026-11-18 rank737: 26 points).
   Each case is the rewrite f[x:A] --> g[x:B], A one of string, number,
   token, shape, operator or a meta-string, B one of number, string,
   token, shape, operator, applied (Relaxed) to f with a concrete
   parameter of kind A.  Each line prints the result and the constructor
   of its parameter, or the refusal.
   Pinned as found (not changed): a string of digits used as a number is
   that Number, any other string a meta-number (MNumber); a concrete
   string used as a token, shape or operator becomes a META-parameter
   named by the string (MToken, MShape, MOperator), not a concrete one;
   a number may be used as a string but not as a token, shape or
   operator, and a token as a shape or operator but not as a string
   (Invalid_argument "stack entry is not valid").
   The expected file is the output of the code as written (2026-11-18),
   never typed.  Mutants (2026-11-18, each rebuilt and relinked; an
   identity control unchanged): the digit test off, and six conversions
   refused (number and shape to string, string to token, token to shape
   and to operator, operator to shape): 7 of 7 RED.  The first was
   invisible until the parameter's constructor was printed: Number 17 and
   MNumber 17 print alike. *)
open Term_sig
open Refiner.Refiner
open TermType
open Term
open RefineError
open Rewrite_sig

let op s = Opname.make_opname [ s; "Rpk" ]
let v = Lm_symbol.add
let p1 o prm = mk_term (mk_op (op o) [ make_param prm ]) []
let sp = Simple_print.SimplePrint.string_of_term
let shp = { shape_opname = op "sh"; shape_params = [ ShapeNumber ]; shape_arities = [ 0 ] }
let opp = { opparam_name = op "oo"; opparam_params = []; opparam_arities = [ 1 ] }

(* the redex's meta-parameter kinds and a concrete parameter of each *)
let redex_kinds = [
  "string \"17\"", (fun x -> MString x), String "17";
  "string \"ab\"", (fun x -> MString x), String "ab";
  "number 42", (fun x -> MNumber x), Number (Lm_num.num_of_int 42);
  "token t", (fun x -> MToken x), Token (op "t");
  "shape", (fun x -> MShape x), Shape shp;
  "operator", (fun x -> MOperator x), Operator opp;
  "meta-string y", (fun x -> MString x), MString (v "y");
]
let contractum_kinds = [
  "number", (fun x -> MNumber x);
  "string", (fun x -> MString x);
  "token", (fun x -> MToken x);
  "shape", (fun x -> MShape x);
  "operator", (fun x -> MOperator x);
]

let () =
  List.iter (fun (rname, rmk, concrete) ->
      List.iter (fun (cname, cmk) ->
          let redex = p1 "f" (rmk (v "x")) and contractum = p1 "g" (cmk (v "x")) in
          let r =
            try
              let rw = Rewrite.term_rewrite Relaxed Rewrite.empty_args_spec [ redex ] [ contractum ] in
              match Rewrite.apply_rewrite rw (Rewrite.empty_rw_args, Lm_symbol.SymbolSet.empty) (p1 "f" concrete) [] with
              | [ t ] ->
                 let kind = match (dest_op (dest_term t).term_op).op_params with
                   | [ p ] -> (match dest_param p with
                       | Number _ -> "Number" | String _ -> "String" | Token _ -> "Token" | Shape _ -> "Shape" | Operator _ -> "Operator"
                       | MNumber _ -> "MNumber" | MString _ -> "MString" | MToken _ -> "MToken" | MShape _ -> "MShape" | MOperator _ -> "MOperator"
                       | _ -> "other")
                   | _ -> "?" in
                 sp t ^ " (" ^ kind ^ ")"
              | l -> Printf.sprintf "%d results" (List.length l)
            with
            | RefineError (s, e) -> "REFUSED: " ^ s ^ (match e with StringError m -> " (" ^ m ^ ")" | RewriteStringError m -> " (" ^ m ^ ")" | _ -> "")
            | Invalid_argument s -> "INVALID_ARGUMENT: " ^ s
            | e -> "raised " ^ Printexc.to_string e
          in
          Printf.printf "%-16s as %-9s %s\n%!" rname cname r) contractum_kinds) redex_kinds
