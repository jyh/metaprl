(* unit-link: filter *)
(*
 * Free_vars (filter/base), against a model.
 *
 * Free_vars.free_vars gives the free variables of a camlp5 MLast
 * expression and patt_vars the variables a pattern binds; new_vars picks
 * names not free in an expression.  Each expression below is built
 * directly from MLast constructors (no quotations), and the result is
 * compared, as a set, with an independent model over the same small
 * language: variables, application, tuples, sequences, if, fun, match and
 * try with guards, and let / let rec with one or two bindings.
 *
 * The expected file is the output of the code.  Before the fix that
 * followed this test, the body of a let was not examined (the last
 * right-hand side was examined in its place, so `let x = a in b` gave
 * [a]), a `when` guard was not examined, and a let rec's right-hand sides
 * did not see its names; the hand cases and the model now agree on all
 * of them.
 *)

let loc = Ploc.dummy
let v s = Ploc.VaVal s
let lid s = MLast.ExLid (loc, v s)
let plid s = MLast.PaLid (loc, v s)
let app f a = MLast.ExApp (loc, f, a)
let tup l = MLast.ExTup (loc, v l)
let seq l = MLast.ExSeq (loc, v l)
let ifte a b c = MLast.ExIfe (loc, a, b, c)
let int n = MLast.ExInt (loc, v (string_of_int n), "")
let case ?guard p e = (p, v guard, e)
let fn cases = MLast.ExFun (loc, v cases)
let mat e cases = MLast.ExMat (loc, e, v cases)
let try_ e cases = MLast.ExTry (loc, e, v cases)
let let_ ?(rc = false) binds body =
   MLast.ExLet (loc, v rc, v (List.map (fun (p, e) -> (p, e, v [])) binds), body)

let sorted l = List.sort_uniq compare l
let show l = "[" ^ String.concat "," (sorted l) ^ "]"

let fv e =
   match Free_vars.free_vars e with
      l -> show l
    | exception ex -> "ERROR " ^ Printexc.to_string ex

(* The hand cases: name, expression, the free variables OCaml gives it. *)
let hand = [
   "a", lid "a", ["a"];
   "a b", app (lid "a") (lid "b"), ["a"; "b"];
   "(a, b, a)", tup [lid "a"; lid "b"; lid "a"], ["a"; "b"];
   "1", int 1, [];
   "fun x -> x y", fn [case (plid "x") (app (lid "x") (lid "y"))], ["y"];
   "if a then b else c", ifte (lid "a") (lid "b") (lid "c"), ["a"; "b"; "c"];
   "do { a; b }", seq [lid "a"; lid "b"], ["a"; "b"];
   "let x = a in b", let_ [plid "x", lid "a"] (lid "b"), ["a"; "b"];
   "let x = a in x", let_ [plid "x", lid "a"] (lid "x"), ["a"];
   "let x = a in x b", let_ [plid "x", lid "a"] (app (lid "x") (lid "b")), ["a"; "b"];
   "let x = a and y = x in y", let_ [plid "x", lid "a"; plid "y", lid "x"] (lid "y"), ["a"; "x"];
   "let rec f = f in f", let_ ~rc:true [plid "f", lid "f"] (lid "f"), [];
   "let rec f = g in b", let_ ~rc:true [plid "f", lid "g"] (lid "b"), ["b"; "g"];
   "match a with x when g -> b", mat (lid "a") [case ~guard:(lid "g") (plid "x") (lid "b")], ["a"; "b"; "g"];
   "match a with x when x -> x", mat (lid "a") [case ~guard:(lid "x") (plid "x") (lid "x")], ["a"];
   "try a with x -> b", try_ (lid "a") [case (plid "x") (lid "b")], ["a"; "b"];
   "fun x when g -> x", fn [case ~guard:(lid "g") (plid "x") (lid "x")], ["g"];
]

let () =
   print_endline "hand cases (code vs OCaml's free variables):";
   List.iter (fun (name, e, want) ->
         let got = fv e in
         let want = show want in
            Printf.printf "  %-30s %-10s %s\n" name got
               (if got = want then "agree" else "DIFFER, OCaml gives " ^ want)) hand

(* patt_vars on the patterns the model uses, and a tuple. *)
let () =
   print_endline "patt_vars:";
   List.iter (fun (name, p) ->
         let got = match Free_vars.patt_vars p with
               l -> show l
             | exception ex -> "ERROR " ^ Printexc.to_string ex in
            Printf.printf "  %-30s %s\n" name got)
      [ "x", plid "x";
        "_", MLast.PaAny loc;
        "(x, y, x)", MLast.PaTup (loc, v [plid "x"; plid "y"; plid "x"], v true)  (* the parser's flag for (x, y, x) *);
        "(x : t)", MLast.PaTyc (loc, plid "x", MLast.TyLid (loc, v "t")) ]

(* new_vars: a name that is free gets a higher suffix. *)
let () =
   let e = app (lid "x0") (app (lid "x1") (lid "y0")) in
      Printf.printf "new_vars [x; y; z] in x0 (x1 y0): [%s]\n"
         (String.concat "," (Free_vars.new_vars e ["x"; "y"; "z"]));
   let e = let_ [plid "q", lid "a"] (lid "x0") in
      Printf.printf "new_vars [x] in let q = a in x0: [%s]\n"
         (String.concat "," (Free_vars.new_vars e ["x"]))

(*
 * The model, on random expressions.  A small LCG, so the cases are the
 * same on every OCaml version (Random differs between 4.14 and 5.x).
 *)
let seed = ref 12345
let rand n =
   seed := (!seed * 1103515245 + 12345) land 0x3fffffff;
   (!seed lsr 8) mod n

let names = [| "a"; "b"; "x"; "y" |]
let name () = names.(rand (Array.length names))

type m =
   Var of string
 | App of m * m
 | Tup of m list
 | If of m * m * m
 | Fun of (string * m option * m) list
 | Match of m * (string * m option * m) list
 | Let of bool * (string * m) list * m

let rec gen d =
   if d = 0 then Var (name ()) else
   match rand 7 with
      0 -> Var (name ())
    | 1 -> App (gen (d - 1), gen (d - 1))
    | 2 -> Tup [gen (d - 1); gen (d - 1)]
    | 3 -> If (gen (d - 1), gen (d - 1), gen (d - 1))
    | 4 -> Fun [gen_case d]
    | 5 -> Match (gen (d - 1), [gen_case d; gen_case d])
    | _ -> Let (rand 2 = 0, List.init (1 + rand 2) (fun _ -> name (), gen (d - 1)), gen (d - 1))
and gen_case d =
   name (), (if rand 2 = 0 then Some (gen (d - 1)) else None), gen (d - 1)

let rec to_expr = function
   Var s -> lid s
 | App (a, b) -> app (to_expr a) (to_expr b)
 | Tup l -> tup (List.map to_expr l)
 | If (a, b, c) -> ifte (to_expr a) (to_expr b) (to_expr c)
 | Fun cl -> fn (List.map to_case cl)
 | Match (e, cl) -> mat (to_expr e) (List.map to_case cl)
 | Let (rc, bl, e) -> let_ ~rc (List.map (fun (x, e) -> plid x, to_expr e) bl) (to_expr e)
and to_case (x, g, e) =
   match g with
      None -> case (plid x) (to_expr e)
    | Some g -> case ~guard:(to_expr g) (plid x) (to_expr e)

(* OCaml's scoping: let binds its names in the body only, let rec in the
 * right-hand sides too; a case binds its variable in the guard and the
 * body. *)
let rec model bound = function
   Var s -> if List.mem s bound then [] else [s]
 | App (a, b) -> model bound a @ model bound b
 | Tup l -> List.concat_map (model bound) l
 | If (a, b, c) -> model bound a @ model bound b @ model bound c
 | Fun cl -> List.concat_map (model_case bound) cl
 | Match (e, cl) -> model bound e @ List.concat_map (model_case bound) cl
 | Let (rc, bl, e) ->
      let names = List.map fst bl in
      let rhs_bound = if rc then names @ bound else bound in
         List.concat_map (fun (_, e) -> model rhs_bound e) bl @ model (names @ bound) e
and model_case bound (x, g, e) =
   let bound = x :: bound in
      (match g with None -> [] | Some g -> model bound g) @ model bound e

(* The constructs an expression contains, for the per-construct lines. *)
let rec has p m =
   p m ||
   match m with
      Var _ -> false
    | App (a, b) -> has p a || has p b
    | Tup l -> List.exists (has p) l
    | If (a, b, c) -> has p a || has p b || has p c
    | Fun cl -> List.exists (has_case p) cl
    | Match (e, cl) -> has p e || List.exists (has_case p) cl
    | Let (_, bl, e) -> List.exists (fun (_, e) -> has p e) bl || has p e
and has_case p (_, g, e) =
   (match g with None -> false | Some g -> has p g) || has p e

let rec to_string = function
   Var s -> s
 | App (a, b) -> "(" ^ to_string a ^ " " ^ to_string b ^ ")"
 | Tup l -> "(" ^ String.concat ", " (List.map to_string l) ^ ")"
 | If (a, b, c) -> "(if " ^ to_string a ^ " then " ^ to_string b ^ " else " ^ to_string c ^ ")"
 | Fun cl -> "(fun " ^ String.concat " | " (List.map case_string cl) ^ ")"
 | Match (e, cl) -> "(match " ^ to_string e ^ " with " ^ String.concat " | " (List.map case_string cl) ^ ")"
 | Let (rc, bl, e) ->
      "(let " ^ (if rc then "rec " else "")
      ^ String.concat " and " (List.map (fun (x, e) -> x ^ " = " ^ to_string e) bl)
      ^ " in " ^ to_string e ^ ")"
and case_string (x, g, e) =
   x ^ (match g with None -> "" | Some g -> " when " ^ to_string g) ^ " -> " ^ to_string e

let () =
   let n = 2000 in
   let cases = List.init n (fun _ -> gen (1 + rand 3)) in
   let classes = [
      "no let, no guard", (fun m -> not (has (function Let _ -> true | _ -> false) m)
                                 && not (has (function Fun cl | Match (_, cl) ->
                                                 List.exists (fun (_, g, _) -> g <> None) cl
                                               | _ -> false) m));
      "with a let", has (function Let (false, _, _) -> true | _ -> false);
      "with a let rec", has (function Let (true, _, _) -> true | _ -> false);
      "with a guard", has (function Fun cl | Match (_, cl) ->
                                       List.exists (fun (_, g, _) -> g <> None) cl
                                     | _ -> false);
      "all", (fun _ -> true) ]
   in
      Printf.printf "model, %d random expressions (depth 1-3, names a b x y):\n" n;
      List.iter (fun (label, sel) ->
            let mine = List.filter sel cases in
            let bad = List.filter (fun m -> fv (to_expr m) <> show (model [] m)) mine in
               Printf.printf "  %-18s %d of %d disagree%s\n" label (List.length bad) (List.length mine)
                  (match bad with
                      [] -> ""
                    | m :: _ ->
                         Printf.sprintf " (first: %s gives %s, OCaml %s)"
                            (to_string m) (fv (to_expr m)) (show (model [] m)))) classes
