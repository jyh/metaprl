(* Ascii_io, the parts no test reached (2026-11-11 reach census: 169 of
   439 points reached by neither the proof census nor a unit test):
   (1) every parameter kind written and read back; (2) the readers kept
   for old .prla formats (<= 1.0.5, 1.0.6, 1.0.7, 1.0.10, 1.0.14), each
   fed a hand-made line; (3) what the filter does on save
   (filter/base/filter_cache.ml writes a proof against the table read
   from the old file): a file with an entry duplicated by hand, the
   duplicate referenced from each kind of line that names another entry;
   (4) the same save after the term changed, where the old entries are
   reused.  Each case prints the lines written and the term read back
   (Simple_print), or the exception.  Pinned as it reads today, including
   two behaviours worth knowing: a save fails when a duplicated opname or
   term is named by a Token, Shape or Operator parameter (the reader
   accepts the same file), and read_table stops at a line with fewer than
   two fields, so the lines after it are dropped with only a message on
   stderr. *)
open Term_sig
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
module A = Ascii_io.AsciiIO
module P = Simple_print.SimplePrint

let v = Lm_symbol.add
let op s = Opname.make_opname [ s ]
let c s = mk_simple_term (op s) []
let p x = make_param x
let num n = Number (Lm_num.num_of_int n)
let file = "test_ascii_io_compat.prla"

let lines_of f = let ic = open_in_bin f in
  let rec go acc = match input_line ic with l -> go (l :: acc) | exception End_of_file -> List.rev acc in
  let l = go [] in close_in ic; l
let write_lines f l = let oc = open_out_bin f in List.iter (fun s -> output_string oc s; output_char oc '\n') l; close_out oc
let table_of l = write_lines file l; let ic = open_in_bin file in
  Fun.protect ~finally:(fun () -> close_in ic) (fun () -> A.read_table ic)
let show f = try P.string_of_term (f ()) with e -> "raised " ^ Printexc.to_string e
let say fmt = Printf.ksprintf (fun s -> print_string s; flush stdout) fmt
let write_fresh t = let oc = open_out_bin file in A.write_term oc (A.initialize ()) t; close_out oc; lines_of file

(* Write [t] against the table read from [l] (the save), print the file, read it back. *)
let save name l t =
  say "== save: %s\n" name;
  match table_of l with
  | exception e -> say "   read_table raised %s\n" (Printexc.to_string e)
  | tbl ->
      let oc = open_out_bin file in
      match Fun.protect ~finally:(fun () -> close_out oc) (fun () -> A.write_term oc tbl t) with
      | exception e -> say "   write_term raised %s\n" (Printexc.to_string e)
      | () ->
          let out = lines_of file in
          List.iter (say "   %s\n") out;
          let back = show (fun () -> A.get_term (table_of out)) in
          say "   read back: %s\n   alpha-equal to the term saved: %b\n" back
            (try Refiner.Refiner.TermSubst.alpha_equal t (A.get_term (table_of out)) with _ -> false)

let read name l = say "%-44s %s\n" (name ^ ":") (show (fun () -> A.get_term (table_of l)))

let () =
  (* (1) every parameter kind *)
  let t = mk_term (mk_op (op "f") [
    p (num 7); p (String "s t"); p (Token (op "tok")); p (Var (v "x"));
    p (Shape { shape_opname = op "g"; shape_params = [ ShapeNumber; ShapeToken ]; shape_arities = [ 0; 1 ] });
    p (Operator { opparam_name = op "h"; opparam_params = [ p (num 3) ]; opparam_arities = [ 2 ] });
    p Quote; p (MNumber (v "n")); p (MString (v "s")); p (MToken (v "k")); p (MShape (v "sh")); p (MOperator (v "o"));
    p (MLevel (mk_level 1 [ mk_level_var (v "i") 0; mk_level_var (v "j") 2 ])) ]) [] in
  say "== every parameter kind\n";
  let l = write_fresh t in
  List.iter (say "   %s\n") l;
  let back = A.get_term (table_of l) in
  say "   read back: %s\n   alpha-equal: %b\n" (P.string_of_term back) (Refiner.Refiner.TermSubst.alpha_equal t back);

  (* (2) old formats, one hand-made file each *)
  say "== old formats (read_table + get_term; the last line is the term read)\n";
  let a = [ "Na\ta\ta NIL"; "O\to1\ta"; "T\tt1\to1" ] in
  let sa = [ "Nsa\tsa\tsa NIL"; "O\to\tsa"; "T\tt\to" ] in
  read "current: sequent x: a >- a" ((sa @ a @ [ "H\th1\tx t1"; "S\ts\tt\\\\ h1\\\\ t1" ]));
  read "<= 1.0.10: hypothesis with no variable" ((sa @ a @ [ "H\th1\tt1"; "S\ts\tt\\\\ h1\\\\ t1" ]));
  read "<= 1.0.7: context as v::terms" ((sa @ a @ [ "C\th\tH t1"; "S\ts\tt\\\\ h\\\\ t1" ]));
  read "<= 1.0.6: S args::hyps, then G" ((sa @ a @ [ "H\th1\tx t1"; "S\ts\tt h1"; "G\ts\tt1" ]));
  read "<= 1.0.6: G with no S before it" ((sa @ a @ [ "G\ts\tt1" ]));
  read "<= 1.0.14: two conclusions (the first kept)" ((sa @ a @ [ "S\ts\tt\\\\ \\\\ t1 t" ]));
  read "<= 1.0.14: no conclusion, no t4" ((sa @ a @ [ "S\ts\tt\\\\ \\\\ " ]));
  read "<= 1.0.14: no conclusion, t4 defined" ((sa @ a @ [ "T\tt4\to1"; "S\ts\tt\\\\ \\\\ " ]));
  read "<= 1.0.7: var opname with subterms" ((a @ [ "Nvar\tvar\tvar NIL"; "P\tp\tVar x"; "O\to2\tvar p"; "B\tb\tt1"; "T\tt5\to2 b" ]));
  read "<= 1.0.7: var opname, bound subterm" ((a @ [ "Nvar\tvar\tvar NIL"; "P\tp\tVar x"; "O\to2\tvar p"; "B\tb\tt1 y"; "T\tt5\to2 b" ]));
  read "<= 1.0.5: MVar parameter" ((a @ [ "P\tp\tMVar x"; "O\to2\ta p"; "T\tt5\to2" ]));
  read "a parameter kind that does not exist" ((a @ [ "P\tp\tFloat 1"; "O\to2\ta p"; "T\tt5\to2" ]));
  read "MLevel with an odd variable list" ((a @ [ "P\tp\tMLevel 1 i"; "O\to2\ta p"; "T\tt5\to2" ]));


  (* (2b) malformed lines, one per reader, and the line-level syntax *)
  say "== malformed lines (the term is the last line)\n";
  List.iter (fun (name, l) -> read name (a @ l)) [
    "O with no fields", [ "O\to9"; "T\tt9\to9" ];
    "N with three fields", [ "Nz\tz\tz NIL extra"; "O\to9\tz"; "T\tt9\to9" ];
    "B with no fields", [ "B\tb9"; "T\tt9\to1 b9" ];
    "H with three fields", [ "H\th9\tx t1 t1"; "S\ts9\tt1\\\\ h9\\\\ t1" ];
    "C with an empty field list", [ "C\th9"; "S\ts9\tt1\\\\ h9\\\\ t1" ];
    "S with four groups", [ "S\ts9\tt1\\\\ \\\\ t1\\\\ t1" ];
    "V with one group", [ "VC\tC\tC t1" ];
    "var opname, a Number parameter", [ "Nvar\tvar\tvar NIL"; "P\tp\tNumber 1"; "O\to2\tvar p"; "B\tb\tt1"; "T\tt5\to2 b" ];
    "a comment and a blank line", [ "# a comment"; ""; "T\tt9\to1" ];
    "a line with one field, then a term z", [ "T"; "Nz\tz\tz NIL"; "O\to9\tz"; "T\tt9\to9" ];
    "a name defined twice", [ "T\tt9\to1"; "T\tt9\to1" ];
  ];
  say "== get_named_term on a <= 1.0.7 file: %s\n"
    (show (fun () -> A.get_named_term (table_of (sa @ a @ [ "C\th\tH t1"; "S\ts\tt\\\\ h\\\\ t1" ])) "s"));
  Lm_debug.set_debug "ascii_io" true;
  say "== with the ascii_io debug flag on (each item is printed on stderr)\n";
  read "debug: a well-formed file" (a @ [ "B\tb\tt1"; "T\tt9\to1 b" ]);
  read "debug: a reference to an undefined name" (a @ [ "B\tb\tt8"; "T\tt9\to1 b" ]);
  Lm_debug.set_debug "ascii_io" false;

  (* (3) a save against a file with an entry duplicated by hand *)
  let ft = mk_term (mk_op (op "f") [ p (Token (op "tok")); p (Shape { shape_opname = op "g"; shape_params = []; shape_arities = [] }) ])
      [ mk_simple_bterm (c "c") ] in
  let base = write_fresh ft in
  say "== the file the saves below start from\n";
  List.iter (say "   %s\n") base;
  let after line extra l = List.concat_map (fun s -> if s = line then s :: extra else [ s ]) l in
  let swap a b l = List.map (fun s -> if s = a then b else s) l in
  let name_of kind = List.find (fun s -> String.length s > 0 && s.[0] = kind) base in
  ignore name_of;
  save "as written" base ft;
  let dn = after "Ntok\ttok\ttok NIL" [ "Ntok\ttok2\ttok NIL" ] base in
  save "N tok2 duplicates tok, unreferenced" dn ft;
  save "N tok2 duplicates tok, a Token parameter names it" (swap "P\tp\tToken tok" "P\tp\tToken tok2" dn) ft;
  let dg = after "Ng\tg\tg NIL" [ "Ng\tg2\tg NIL" ] base in
  save "N g2 duplicates g, an operator names it" (swap "O\to\tg" "O\to\tg2" dg) ft;
  let dt = after "T\tt\to" [ "T\ttdup\to" ] base in
  save "T tdup duplicates t, a Shape parameter names it" (swap "P\tp1\tShape t" "P\tp1\tShape tdup" dt) ft;
  let dc = after "T\tt2\to2" [ "T\ttc\to2" ] base in
  save "T tc duplicates t2, a bound term names it" (swap "B\tb\tt2" "B\tb\ttc" dc) ft;
  save "a line of an unknown kind X" (base @ [ "X\tx1\tsomething" ]) ft;
  save "P p7 Number 007 (the value of 7, another spelling)" (after "P\tp1\tShape t" [ "P\tp7\tNumber 007"; "O\to7\tg p7"; "T\tt7\to7" ] base)
    (mk_term (mk_op (op "g") [ p (num 7) ]) []);


  (* (3b) dedupe through hypothesis, context, second-order variable and nested opname lines *)
  let sq = mk_sequent_term { sequent_args = c "sa";
    sequent_hyps = SeqHyp.of_list [ Hypothesis (v "x", c "a"); Context (v "J", [], [ c "a" ]) ];
    sequent_concl = mk_so_var_term (v "C") [] [ c "a" ] } in
  let ql = write_fresh sq in
  say "== the sequent file the saves below start from\n";
  List.iter (say "   %s\n") ql;
  let field2 l = match String.split_on_char '\t' l with _ :: n :: _ -> n | _ -> "" in
  let dup_named n n2 l = List.concat_map (fun s -> if field2 s = n then [ s; String.concat "\t" (match String.split_on_char '\t' s with k :: _ :: r -> k :: n2 :: r | x -> x) ] else [ s ]) l in
  let rename_ref old nw l = List.map (fun s -> match String.split_on_char '\t' s with
      | [ k; n; r ] when field2 s <> old -> k ^ "\t" ^ n ^ "\t" ^ String.concat " " (List.map (fun w -> if w = old then nw else w) (String.split_on_char ' ' r))
      | _ -> s) l in
  save "H hdup duplicates h, the sequent names it" (rename_ref "h" "hdup" (dup_named "h" "hdup" ql)) sq;
  save "T t1dup duplicates t1, the context and the variable name it" (rename_ref "t1" "t1dup" (dup_named "t1" "t1dup" ql)) sq;
  save "the hypothesis in the <= 1.0.10 form (no variable)" (List.map (fun s -> if field2 s = "h" then "H\th\tt1" else s) ql) sq;
  save "the context in the <= 1.0.7 form (v::terms)" (List.map (fun s -> if field2 s = "h1" then "C\th1\tJ t1" else s) ql) sq;
  let nested = mk_simple_term (Opname.make_opname [ "x"; "y" ]) [] in
  let nl = write_fresh nested in
  say "== a nested opname's file\n";
  List.iter (say "   %s\n") nl;
  save "N ydup duplicates the inner opname y, the outer N names it" (rename_ref "y" "ydup" (dup_named "y" "ydup" nl)) nested;
  save "N ydup duplicates y, the outer N still names y" (dup_named "y" "ydup" nl) nested;
  let before n n2 l = List.concat_map (fun s -> if field2 s = n then [ String.concat "\t" (match String.split_on_char '\t' s with k :: _ :: r -> k :: n2 :: r | x -> x); s ] else [ s ]) l in
  save "N ydup before y, the outer N names y" (before "y" "ydup" nl) nested;
  save "N ydup before y, the outer N names ydup" (rename_ref "y" "ydup" (before "y" "ydup" nl)) nested;

  (* (4) the save after the term changed *)
  let ft2 = mk_term (mk_op (op "f") [ p (Token (op "tok")); p (Shape { shape_opname = op "g"; shape_params = []; shape_arities = [] }) ])
      [ mk_simple_bterm (c "d") ] in
  save "the term changed (c -> d)" base ft2;
  save "a different term" base (c "e");
  let st = mk_sequent_term { sequent_args = c "sa"; sequent_hyps = SeqHyp.of_list [ Hypothesis (v "x", c "a") ];
                             sequent_concl = mk_so_var_term (v "C") [] [ mk_var_term (v "x") ] } in
  let sl = write_fresh st in
  save "a sequent, unchanged" sl st;
  let sg = List.concat_map (fun s -> if s = "S\ts\tt\\\\ h\\\\ C" then [ "S\ts\tt h"; "G\ts\tC" ] else [ s ]) sl in
  say "   (the S line replaced by: S s t h / G s C)\n";
  save "a sequent, its file in the <= 1.0.6 S/G form" sg st;
  save "a sequent, the <= 1.0.6 form with G first" (List.concat_map (fun s -> if s = "S\ts\tt h" then [] else if s = "G\ts\tC" then [ s; "S\ts\tt h" ] else [ s ]) sg) st;
  Sys.remove file
