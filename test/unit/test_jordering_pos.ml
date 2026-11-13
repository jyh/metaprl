(* Jordering's position names (refiner/reflib/jordering.ml): how JProver
   writes a position (a kind and an index) as a string and as a symbol, and
   reads a symbol back.  kind_to_string, pos_to_string, pos_to_symbol,
   symbol_to_pos (through string_to_kind), gamma_to_simple and
   simple_to_gamma, on every kind: sort 0 and a nonzero sort (the modal
   positions, Var i and Const i, that jall makes from Nu_0 i and Pi_0 i),
   and GammaPos one and two deep.  No test, theory build or proof replay
   reached kind_to_string's nonzero sorts, symbol_to_pos's GammaPos or
   gamma_to_simple's refusal (bisect at c013b0579 and 008a9607e).

   Each line prints the string, the symbol's name and what symbol_to_pos
   reads back, or the exception.  The expected file is the output of the
   code as written.  Pinned as found: a symbol of a nonzero sort ("c3_",
   "v3_", "n3_", "q3_") does not read back: string_to_kind takes any name
   longer than one character for a GammaPos and cuts the 8 characters of
   "_jprover" from it, so a shorter name raises Invalid_argument from
   String.sub.  The source says modal positions are "not supposed to be
   converted to symbols or strings" (a commented-out refusal); JProver's
   S4 runs (test_jprover_s4) never convert one.  Also: EmptyVar and Root
   read back with index 0 whatever their symbol's index ("_5", "w5"). *)
open Jtypes
open Jordering

let rec kind = function
  | EmptyVar -> "EmptyVar" | Atom -> "Atom" | Const i -> Printf.sprintf "Const %d" i | Dummy -> "Dummy"
  | EigenVar -> "EigenVar" | Var i -> Printf.sprintf "Var %d" i | NewVar i -> Printf.sprintf "NewVar %d" i
  | NewVarQ i -> Printf.sprintf "NewVarQ %d" i | GammaPos k -> "GammaPos (" ^ kind k ^ ")" | Root -> "Root"

let pos (k, i) = Printf.sprintf "(%s, %d)" (kind k) i
let attempt f = try f () with e -> "raises " ^ Printexc.to_string e

let kinds = [ EmptyVar; Atom; Const 0; Const 3; Dummy; EigenVar; Var 0; Var 3; NewVar 0; NewVar 3;
              NewVarQ 0; NewVarQ 3; Root; GammaPos Atom; GammaPos (Var 0); GammaPos (GammaPos (Const 0));
              GammaPos (Var 3) ]

let () =
  List.iter (fun k ->
      let p = (k, 5) in
      Printf.printf "%-34s string %-24s symbol %-24s back %s\n" (pos p)
        (attempt (fun () -> "\"" ^ pos_to_string p ^ "\""))
        (attempt (fun () -> "\"" ^ Lm_symbol.string_of_symbol (pos_to_symbol p) ^ "\""))
        (attempt (fun () -> pos (symbol_to_pos (pos_to_symbol p))))) kinds;
  print_endline "gamma_to_simple / simple_to_gamma:";
  List.iter (fun p ->
      Printf.printf "  %-32s simple %s  gamma %s\n" (pos p)
        (attempt (fun () -> pos (gamma_to_simple p))) (pos (simple_to_gamma p)))
    [ (GammaPos Atom, 2); (GammaPos (GammaPos Atom), 2); (Atom, 2); (Root, 0) ]
