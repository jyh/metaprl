(* Term shapes, the parts test_term_shape leaves out: unquote_shape,
   opname_of_shape, the canonical term of a shape carrying quote, shape,
   operator, level and variable parameters, the shapes of variables,
   second-order variables and sequents, and the parameters a shape cannot
   describe.  In term_std and term_ds:
     - on 2000 generated shapes (operators f, g, h; 0-4 parameters of every
       kind, quotes three times as likely; 0-3 subterms of 0-2 binders),
       unquote_shape removes exactly the LEADING quotes (a model: drop
       ShapeQuote from the front of the list, keep every later one), returns
       its argument itself (==) when there is no leading quote, and is
       idempotent;
     - opname_of_shape is the shape's operator name;
     - shape_of_term (canonical_term_of_shape s) is s (eq), and shape_eq
       agrees with eq;
     - the two implementations print every shape the same;
     - a variable, a second-order variable and a sequent have var_shape, a
       var_shape with one zero arity per argument, and sequent_shape;
     - ObId and ParamList parameters make shape_of_term (and
       shape_of_opparam) raise Invalid_argument "Term.shape_of_term".
   The generator is a fixed linear congruential sequence, not Random. *)
open Term_sig

let state = ref 4242
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

let kinds = [| ShapeNumber; ShapeString; ShapeToken; ShapeLevel; ShapeVar; ShapeShape; ShapeOperator |]
let gkind () = if pick 10 < 3 then ShapeQuote else kinds.(pick (Array.length kinds))
let gshape () =
  { shape_opname = Opname.make_opname [ [| "f"; "g"; "h" |].(pick 3) ];
    shape_params = List.init (pick 5) (fun _ -> gkind ());
    shape_arities = List.init (pick 4) (fun _ -> pick 3) }

(* the model: strip the quotes at the front of the list, keep the rest *)
let rec strip = function ShapeQuote :: ps -> strip ps | ps -> ps

module S (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermMan
  module Sh = R.TermShape
  let op s = Opname.make_opname [ s ]
  let safe f = try f () with e -> "EXN " ^ Printexc.to_string e

  (* per shape: printed form, unquote = model, (==) when nothing to strip,
     idempotent, opname, canonical round trip, shape_eq = eq *)
  let checks s =
    let u = Sh.unquote_shape s in
    let model = u.shape_params = strip s.shape_params
                && Opname.eq u.shape_opname s.shape_opname && u.shape_arities = s.shape_arities in
    let same = (match s.shape_params with ShapeQuote :: _ -> true | _ -> u == s) in
    let idem = Sh.eq (Sh.unquote_shape u) u in
    let name = Opname.eq (Sh.opname_of_shape s) s.shape_opname in
    let canon = (try Sh.eq (Sh.shape_of_term (Sh.canonical_term_of_shape s)) s with _ -> false) in
    let seq = Sh.shape_eq s u = Sh.eq s u in
    safe (fun () -> Sh.string_of_shape s), [| model; same; idem; name; canon; seq |]

  let specials () =
    let v = mk_var_term (Lm_symbol.add "a") in
    let so = mk_so_var_term (Lm_symbol.add "z") [] [ v; v ] in
    let sq = mk_sequent_term { sequent_args = mk_simple_term (op "sa") [];
                               sequent_hyps = R.Term.SeqHyp.of_list [ Hypothesis (Lm_symbol.add "h", v) ];
                               sequent_concl = v } in
    let qt ps = mk_term (mk_op (op "q") ps) [] in
    let n1 = make_param (Number (Lm_num.num_of_int 1)) in
    let q = make_param Quote in
    let show name t = Printf.printf "%-34s %s\n" name (safe (fun () -> Sh.string_of_shape (Sh.shape_of_term t))) in
    show "variable" v;
    Printf.printf "%-34s %b\n" "variable is var_shape" (Sh.eq (Sh.shape_of_term v) Sh.var_shape);
    show "second-order variable, 2 args" so;
    show "sequent" sq;
    Printf.printf "%-34s %b\n" "sequent is sequent_shape" (Sh.eq (Sh.shape_of_term sq) Sh.sequent_shape);
    List.iter (fun (name, ps) ->
        let s = Sh.shape_of_term (qt ps) in
        Printf.printf "%-34s %s -> %s\n" name (Sh.string_of_shape s) (Sh.string_of_shape (Sh.unquote_shape s)))
      [ "q[quote; 1]", [ q; n1 ]; "q[quote; quote; 1]", [ q; q; n1 ];
        "q[1; quote]", [ n1; q ]; "q[quote; 1; quote]", [ q; n1; q ]; "q[quote]", [ q ] ];
    List.iter (fun (name, p) ->
        Printf.printf "%-34s %s\n" ("shape_of_term " ^ name) (safe (fun () -> Sh.string_of_shape (Sh.shape_of_term (qt [ p ]))));
        Printf.printf "%-34s %s\n" ("shape_of_opparam " ^ name)
          (safe (fun () -> Sh.string_of_shape (Sh.shape_of_opparam { opparam_name = op "q"; opparam_params = [ p ]; opparam_arities = [] }))))
      [ "ObId", make_param (ObId [ n1 ]); "ParamList", make_param (ParamList [ n1 ]) ]
end

module Std = S (Refiner_std.Refiner)
module Ds = S (Refiner_ds.Refiner)

let () =
  let n = 2000 in
  let shapes = List.init n (fun _ -> gshape ()) in
  let count p = List.length (List.filter p shapes) in
  Printf.printf "%d shapes: %d with a leading quote, %d with a quote after another parameter\n" n
    (count (fun s -> match s.shape_params with ShapeQuote :: _ -> true | _ -> false))
    (count (fun s -> List.mem ShapeQuote (strip s.shape_params)));
  let rs = List.map Std.checks shapes and rd = List.map Ds.checks shapes in
  Printf.printf "%-46s %4d of %d\n" "std and ds print the shape the same"
    (List.fold_left2 (fun k (a, _) (b, _) -> if a = b then k + 1 else k) 0 rs rd) n;
  let names = [| "unquote_shape = the model"; "unquote_shape s == s, no leading quote"; "unquote_shape idempotent";
                 "opname_of_shape"; "canonical term has the shape"; "shape_eq agrees with eq" |] in
  List.iter (fun (impl, res) ->
      Array.iteri (fun i nm ->
          let k = List.length (List.filter (fun (_, a) -> a.(i)) res) in
          let first = List.find_opt (fun (_, a) -> not a.(i)) res in
          Printf.printf "%-46s %4d of %d%s\n" (impl ^ ": " ^ nm) k n
            (match first with None -> "" | Some (p, _) -> " (first: " ^ p ^ ")")) names)
    [ "std", rs; "ds", rd ];
  print_endline "-- std"; Std.specials ();
  print_endline "-- ds"; Ds.specials ()
