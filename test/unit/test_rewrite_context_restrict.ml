(* Rewrite_match_redex (refiner/rewrite): restrict_context_vars on a term
   context already matched (its StackContext arm), the refusal "Variable
   appears free where it is not allowed to" for a context's own bound
   variables.  The redex f{C[g{'b<||>}]} places the second-order variable
   'b inside the hole of the term context C (passed as an address
   argument) and lets it see no context, so under Strict compilation 'b
   carries a restriction naming C (RWSOFreeVarsVar).  C is matched first;
   when 'b is matched, every variable free in its term that C binds is
   refused.  Cases: the hole's term mentions C's binder (refused under
   Strict), mentions none (matches), 'b<|C|> that may see C (matches), and
   the hole at the top, where C binds nothing (matches); then the same
   four under Relaxed, which compiles no restriction, so all match.  The
   expected file is the output of the code as written (2026-11-18), never
   typed.  Mutants (2026-11-18, each rebuilt and relinked; an identity
   control survives): the arm never refusing, the arm always refusing,
   and the so-variable's restriction dropped are each RED; dropping the
   restriction a context records for itself (RWSOFreeVarsContext) is NOT
   seen, as no case gives C itself a restriction. *)
open Term_sig
open Term_addr_sig
open Refiner.Refiner
open TermType
open Term
open TermMan
open RefineError
open Rewrite_sig

let op s = Opname.make_opname [ s; "Rcr" ]
let v = Lm_symbol.add
let app o ts = mk_term (mk_op (op o) []) (List.map (fun t -> mk_bterm [] t) ts)
let c0 o = app o []
let so name conts args = mk_so_var_term (v name) (List.map v conts) args
let var x = mk_var_term (v x)
let lam x t = mk_term (mk_op (op "lam") []) [ mk_bterm [ v x ] t ]
let sp = Simple_print.SimplePrint.string_of_term
let ctx name conts body = mk_context_term (v name) body (List.map v conts) []

let show_item = function
  | RewriteTerm t -> sp t
  | RewriteString _ | RewriteToken _ | RewriteNum _ -> "param"
  | RewriteLevel _ -> "level" | RewriteShape _ -> "shape" | RewriteOperator _ -> "operator"
  | RewriteUnsupported -> "-"

let at path = [| TermAddr.make_address (List.map (fun i -> Subterm i) path) |]

let case name strict redex target path =
  let r =
    try
      let rx = Rewrite.compile_redices strict { spec_ints = [||]; spec_addrs = [| v "C" |] } [ redex ] in
      let items = Rewrite.apply_redex rx { arg_ints = [||]; arg_addrs = at path } target [] in
      "MATCH [" ^ String.concat "; " (List.map show_item items) ^ "]"
    with
    | RefineError (s, e) ->
        "REFUSED: " ^ s
        ^ (match e with
           | StringVarError (m, x) -> " (" ^ m ^ ": " ^ Lm_symbol.to_string x ^ ")"
           | StringError m -> " (" ^ m ^ ")"
           | _ -> "")
    | Invalid_argument s -> "INVALID_ARGUMENT: " ^ s
  in
  Printf.printf "%-58s %s\n" name r

let () =
  List.iter (fun strict ->
    let sn = match strict with Strict -> "Strict" | Relaxed -> "Relaxed" in
    Printf.printf "== %s\n" sn;
    let r_none = app "f" [ ctx "C" [] (app "g" [ so "b" [] [] ]) ] in
    let r_c = app "f" [ ctx "C" [] (app "g" [ so "b" [ "C" ] [] ]) ] in
    let t_y = app "f" [ lam "y" (app "g" [ var "y" ]) ] in
    let t_c = app "f" [ lam "y" (app "g" [ c0 "c" ]) ] in
    case "f{C[g{'b<||>}]} on f{lam y. g{y}}, hole at 1" strict r_none t_y [ 1 ];
    case "f{C[g{'b<||>}]} on f{lam y. g{c}}, hole at 1" strict r_none t_c [ 1 ];
    case "f{C[g{'b<|C|>}]} on f{lam y. g{y}}, hole at 1" strict r_c t_y [ 1 ];
    case "f{C[g{'b<||>}]} on f{g{c}}, hole at the top" strict r_none (app "f" [ app "g" [ c0 "c" ] ]) [])
    [ Strict; Relaxed ]
