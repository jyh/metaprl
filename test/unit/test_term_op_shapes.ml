(* The mk_/is_/dest_ vocabulary of TermOp (refiner/term_std/term_op_std,
   refiner/term_ds/term_op_ds), most of which no unit test reached
   (2026-11-02 census over master and every open branch).  In term_std and
   term_ds, for each of 40 constructors, on one term built with distinct
   components (terms a, b, c, ..., variables x, y, z, ..., numbers,
   strings):
     - dest_X under the constructor's own name gives the components back,
       and so does dest_X_any where it exists;
     - is_X holds under its own name, and is_X and dest_X refuse another
       name;
     - across the whole table, is_X applied to the term built by Y holds
       exactly when the two terms have the same shape (TermShape, under one
       name) -- except is_token_simple_term, which takes any number of
       subterms without binders, so it holds for any term with one token
       parameter and such subterms.
   No generator: every term is written out. *)
open Term_sig

module S (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermOp
  open R.TermMan
  let on = Opname.make_opname [ "shp" ] and other = Opname.make_opname [ "other" ]
  let tm s = mk_simple_term (Opname.make_opname [ s ]) []
  let a = tm "a" and b = tm "b" and c = tm "c" and d = tm "d" and e = tm "e" and f = tm "f"
  let v s = Lm_symbol.add s
  let x = v "x" and y = v "y" and z = v "z" and u = v "u" and w = v "w" and k = v "k"
  let n7 = Lm_num.num_of_int 7 and n8 = Lm_num.num_of_int 8
  let fT t = "T:" ^ Opname.string_of_opname (opname_of_term t)
  let fV x = "V:" ^ Lm_symbol.to_string x
  let fN n = "N:" ^ Lm_num.string_of_num n
  let fS s = "S:" ^ s
  let fO o = "O:" ^ Opname.string_of_opname o
  let lvl = mk_level 1 [ mk_level_var (v "l") 0 ]
  let fL l = let l = dest_level l in Printf.sprintf "L:%d/%d" l.le_const (List.length l.le_vars)

  (* name, term, components, dest under a name, is under a name, dest_any *)
  type case = { nm : string; t : R.TermType.term; want : string list; dest : (Opname.opname -> R.TermType.term -> string list) option;
                is : (Opname.opname -> R.TermType.term -> bool) option; any : (R.TermType.term -> string list) option }
  let cases = [
    { nm = "dep0"; t = mk_dep0_term on a; want = [ fT a ]; dest = Some (fun o t -> [ fT (dest_dep0_term o t) ]); is = Some is_dep0_term; any = None };
    { nm = "dep0_dep0"; t = mk_dep0_dep0_term on a b; want = [ fT a; fT b ]; dest = Some (fun o t -> let p, q = dest_dep0_dep0_term o t in [ fT p; fT q ]); is = Some is_dep0_dep0_term; any = None };
    { nm = "dep0_dep0_dep0"; t = mk_dep0_dep0_dep0_term on a b c; want = [ fT a; fT b; fT c ]; dest = Some (fun o t -> let p, q, r = dest_dep0_dep0_dep0_term o t in [ fT p; fT q; fT r ]); is = Some is_dep0_dep0_dep0_term; any = None };
    { nm = "dep0_dep0_dep0_dep0"; t = mk_dep0_dep0_dep0_dep0_term on a b c d; want = [ fT a; fT b; fT c; fT d ]; dest = Some (fun o t -> let p, q, r, s = dest_dep0_dep0_dep0_dep0_term o t in [ fT p; fT q; fT r; fT s ]); is = Some is_dep0_dep0_dep0_dep0_term; any = None };
    { nm = "dep1"; t = mk_dep1_term on x a; want = [ fV x; fT a ]; dest = Some (fun o t -> let p, q = dest_dep1_term o t in [ fV p; fT q ]); is = Some is_dep1_term; any = Some (fun t -> let p, q = dest_dep1_any_term t in [ fV p; fT q ]) };
    { nm = "dep2"; t = mk_dep2_term on x y a; want = [ fV x; fV y; fT a ]; dest = Some (fun o t -> let p, q, r = dest_dep2_term o t in [ fV p; fV q; fT r ]); is = Some is_dep2_term; any = None };
    { nm = "dep1_dep1"; t = mk_dep1_dep1_term on x a y b; want = [ fV x; fT a; fV y; fT b ]; dest = Some (fun o t -> let p, q, r, s = dest_dep1_dep1_term o t in [ fV p; fT q; fV r; fT s ]); is = Some is_dep1_dep1_term; any = None };
    { nm = "dep0_dep1"; t = mk_dep0_dep1_term on x a b; want = [ fV x; fT a; fT b ]; dest = Some (fun o t -> let p, q, r = dest_dep0_dep1_term o t in [ fV p; fT q; fT r ]); is = Some is_dep0_dep1_term; any = Some (fun t -> let p, q, r = dest_dep0_dep1_any_term t in [ fV p; fT q; fT r ]) };
    { nm = "dep0_dep1_any"; t = mk_dep0_dep1_any_term (mk_op on []) x a b; want = [ fV x; fT a; fT b ]; dest = None; is = Some (fun o t -> Opname.eq (opname_of_term t) o && is_dep0_dep1_any_term t); any = Some (fun t -> let p, q, r = dest_dep0_dep1_any_term t in [ fV p; fT q; fT r ]) };
    { nm = "dep1_dep0"; t = mk_dep1_dep0_term on x a b; want = [ fV x; fT a; fT b ]; dest = Some (fun o t -> let p, q, r = dest_dep1_dep0_term o t in [ fV p; fT q; fT r ]); is = Some is_dep1_dep0_term; any = None };
    { nm = "dep0_dep2"; t = mk_dep0_dep2_term on x y a b; want = [ fV x; fV y; fT a; fT b ]; dest = Some (fun o t -> let p, q, r, s = dest_dep0_dep2_term o t in [ fV p; fV q; fT r; fT s ]); is = Some is_dep0_dep2_term; any = None };
    { nm = "dep0_dep3"; t = mk_dep0_dep3_term on x y z a b; want = [ fV x; fV y; fV z; fT a; fT b ]; dest = Some (fun o t -> let p, q, r, s, u = dest_dep0_dep3_term o t in [ fV p; fV q; fV r; fT s; fT u ]); is = Some is_dep0_dep3_term; any = None };
    { nm = "dep2_dep0"; t = mk_dep2_dep0_term on x y a b; want = [ fV x; fV y; fT a; fT b ]; dest = Some (fun o t -> let p, q, r, s = dest_dep2_dep0_term o t in [ fV p; fV q; fT r; fT s ]); is = Some is_dep2_dep0_term; any = None };
    { nm = "dep0_dep0_dep1"; t = mk_dep0_dep0_dep1_term on a b x c; want = [ fT a; fT b; fV x; fT c ]; dest = Some (fun o t -> let p, q, r, s = dest_dep0_dep0_dep1_term o t in [ fT p; fT q; fV r; fT s ]); is = Some is_dep0_dep0_dep1_term; any = Some (fun t -> let p, q, r, s = dest_dep0_dep0_dep1_any_term t in [ fT p; fT q; fV r; fT s ]) };
    { nm = "dep0_dep0_dep2"; t = mk_dep0_dep0_dep2_term on a b x y c; want = [ fT a; fT b; fV x; fV y; fT c ]; dest = Some (fun o t -> let p, q, r, s, u = dest_dep0_dep0_dep2_term o t in [ fT p; fT q; fV r; fV s; fT u ]); is = Some is_dep0_dep0_dep2_term; any = None };
    { nm = "dep0_dep0_dep1_any"; t = mk_dep0_dep0_dep1_any_term (mk_op on []) a b x c; want = [ fT a; fT b; fV x; fT c ]; dest = None; is = Some (fun o t -> Opname.eq (opname_of_term t) o && is_dep0_dep0_dep1_any_term t); any = Some (fun t -> let p, q, r, s = dest_dep0_dep0_dep1_any_term t in [ fT p; fT q; fV r; fT s ]) };
    { nm = "dep0_dep1_dep1"; t = mk_dep0_dep1_dep1_term on a x b y c; want = [ fT a; fV x; fT b; fV y; fT c ]; dest = Some (fun o t -> let p, q, r, s, u = dest_dep0_dep1_dep1_term o t in [ fT p; fV q; fT r; fV s; fT u ]); is = Some is_dep0_dep1_dep1_term; any = None };
    { nm = "dep0_dep2_dep0_dep2"; t = mk_dep0_dep2_dep0_dep2_term on a x y b c z u d; want = [ fT a; fV x; fV y; fT b; fT c; fV z; fV u; fT d ];
      dest = Some (fun o t -> let p1, p2, p3, p4, p5, p6, p7, p8 = dest_dep0_dep2_dep0_dep2_term o t in [ fT p1; fV p2; fV p3; fT p4; fT p5; fV p6; fV p7; fT p8 ]); is = Some is_dep0_dep2_dep0_dep2_term; any = None };
    { nm = "dep0_dep0_dep3"; t = mk_dep0_dep0_dep3_term on a b x y z c; want = [ fT a; fT b; fV x; fV y; fV z; fT c ];
      dest = Some (fun o t -> let p1, p2, p3, p4, p5, p6 = dest_dep0_dep0_dep3_term o t in [ fT p1; fT p2; fV p3; fV p4; fV p5; fT p6 ]); is = Some is_dep0_dep0_dep3_term; any = None };
    { nm = "dep2_dep2_dep0_dep0"; t = mk_dep2_dep2_dep0_dep0_term on x y a z u b c d; want = [ fV x; fV y; fT a; fV z; fV u; fT b; fT c; fT d ];
      dest = Some (fun o t -> let p1, p2, p3, p4, p5, p6, p7, p8 = dest_dep2_dep2_dep0_dep0_term o t in [ fV p1; fV p2; fT p3; fV p4; fV p5; fT p6; fT p7; fT p8 ]); is = Some is_dep2_dep2_dep0_dep0_term; any = None };
    { nm = "string"; t = mk_string_term on "s"; want = [ fS "s" ]; dest = Some (fun o t -> [ fS (dest_string_term o t) ]); is = Some is_string_term; any = Some (fun t -> [ fS (dest_string_param t) ]) };
    { nm = "string_string"; t = mk_string_string_term on "s" "r"; want = [ fS "s"; fS "r" ]; dest = Some (fun o t -> let p, q = dest_string_string_term o t in [ fS p; fS q ]); is = Some is_string_string_term; any = None };
    { nm = "var_param"; t = mk_var_param_term on x; want = [ fV x ]; dest = Some (fun o t -> [ fV (dest_var_param_term o t) ]); is = Some is_var_param_term; any = None };
    { nm = "var_dep0"; t = mk_var_dep0_term on x a; want = [ fV x; fT a ]; dest = Some (fun o t -> let p, q = dest_var_dep0_term o t in [ fV p; fT q ]); is = Some is_var_dep0_term; any = Some (fun t -> let p, q = dest_var_dep0_any_term t in [ fV p; fT q ]) };
    { nm = "var_dep0_dep0"; t = mk_var_dep0_dep0_term on x a b; want = [ fV x; fT a; fT b ]; dest = Some (fun o t -> let p, q, r = dest_var_dep0_dep0_term o t in [ fV p; fT q; fT r ]); is = Some is_var_dep0_dep0_term; any = None };
    { nm = "string_dep0"; t = mk_string_dep0_term on "s" a; want = [ fS "s"; fT a ]; dest = Some (fun o t -> let p, q = dest_string_dep0_term o t in [ fS p; fT q ]); is = Some is_string_dep0_term; any = None };
    { nm = "string_string_dep0"; t = mk_string_string_dep0_term on "s" "r" a; want = [ fS "s"; fS "r"; fT a ]; dest = Some (fun o t -> let p, q, r = dest_string_string_dep0_term o t in [ fS p; fS q; fT r ]); is = Some is_string_string_dep0_term; any = Some (fun t -> let p, q, r = dest_string_string_dep0_any_term t in [ fS p; fS q; fT r ]) };
    { nm = "number_dep0"; t = mk_number_dep0_term on n7 a; want = [ fN n7; fT a ]; dest = Some (fun o t -> let p, q = dest_number_dep0_term o t in [ fN p; fT q ]); is = Some is_number_dep0_term; any = Some (fun t -> let p, q = dest_number_dep0_any_term t in [ fN p; fT q ]) };
    { nm = "number_dep1"; t = mk_number_dep1_term on n7 x a; want = [ fN n7; fV x; fT a ]; dest = Some (fun o t -> let p, q, r = dest_number_dep1_term o t in [ fN p; fV q; fT r ]); is = Some is_number_dep1_term; any = Some (fun t -> let p, q, r = dest_number_dep1_any_term t in [ fN p; fV q; fT r ]) };
    { nm = "number_number_dep0"; t = mk_number_number_dep0_term on n7 n8 a; want = [ fN n7; fN n8; fT a ]; dest = Some (fun o t -> let p, q, r = dest_number_number_dep0_term o t in [ fN p; fN q; fT r ]); is = Some is_number_number_dep0_term; any = Some (fun t -> let p, q, r = dest_number_number_dep0_any_term t in [ fN p; fN q; fT r ]) };
    { nm = "number_number_string_dep0"; t = mk_number_number_string_dep0_term on n7 n8 "s" a; want = [ fN n7; fN n8; fS "s"; fT a ];
      dest = Some (fun o t -> let p, q, r, s = dest_number_number_string_dep0_term o t in [ fN p; fN q; fS r; fT s ]); is = Some is_number_number_string_dep0_term;
      any = Some (fun t -> let p, q, r, s = dest_number_number_string_dep0_any_term t in [ fN p; fN q; fS r; fT s ]) };
    { nm = "number_number_string_dep0_dep0"; t = mk_number_number_string_dep0_dep0_term on n7 n8 "s" a b; want = [ fN n7; fN n8; fS "s"; fT a; fT b ];
      dest = Some (fun o t -> let p, q, r, s, u = dest_number_number_string_dep0_dep0_term o t in [ fN p; fN q; fS r; fT s; fT u ]); is = Some is_number_number_string_dep0_dep0_term;
      any = Some (fun t -> let p, q, r, s, u = dest_number_number_string_dep0_dep0_any_term t in [ fN p; fN q; fS r; fT s; fT u ]) };
    { nm = "string_dep0_dep0"; t = mk_string_dep0_dep0_term on "s" a b; want = [ fS "s"; fT a; fT b ]; dest = Some (fun o t -> let p, q, r = dest_string_dep0_dep0_term o t in [ fS p; fT q; fT r ]); is = Some is_string_dep0_dep0_term; any = Some (fun t -> let p, q, r = dest_string_dep0_dep0_any_term t in [ fS p; fT q; fT r ]) };
    { nm = "string_dep0_dep0_dep0"; t = mk_string_dep0_dep0_dep0_term on "s" a b c; want = []; dest = None; is = None; any = None };
    { nm = "string_string_dep0_dep0"; t = mk_string_string_dep0_dep0_term on "s" "r" a b; want = [ fS "s"; fS "r"; fT a; fT b ];
      dest = Some (fun o t -> let p, q, r, s = dest_string_string_dep0_dep0_term o t in [ fS p; fS q; fT r; fT s ]); is = Some is_string_string_dep0_dep0_term;
      any = Some (fun t -> let p, q, r, s = dest_string_string_dep0_dep0_any_term t in [ fS p; fS q; fT r; fT s ]) };
    { nm = "number"; t = mk_number_term on n7; want = [ fN n7 ]; dest = Some (fun o t -> [ fN (dest_number_term o t) ]); is = Some is_number_term; any = Some (fun t -> [ fN (dest_number_any_term t) ]) };
    { nm = "univ"; t = mk_univ_term on lvl; want = [ fL lvl ]; dest = Some (fun o t -> [ fL (dest_univ_term o t) ]); is = Some is_univ_term; any = None };
    { nm = "token"; t = mk_token_term on (Opname.make_opname [ "tok" ]); want = [ fO (Opname.make_opname [ "tok" ]) ]; dest = Some (fun o t -> [ fO (dest_token_term o t) ]); is = Some is_token_term; any = Some (fun t -> [ fO (dest_token_param t) ]) };
    { nm = "token_simple"; t = mk_token_simple_term on (Opname.make_opname [ "tok" ]) [ a; b ]; want = [ fO (Opname.make_opname [ "tok" ]); fT a; fT b ];
      dest = Some (fun o t -> let p, l = dest_token_simple_term o t in fO p :: List.map fT l); is = Some is_token_simple_term; any = None };
    { nm = "dep0 (under 'other')"; t = mk_dep0_term other a; want = [ fT a ]; dest = Some (fun _ t -> [ fT (dest_dep0_term other t) ]); is = None; any = None } ]

  let tried f = try Some (f ()) with R.RefineError.RefineError _ -> None | _ -> None
  let run name =
    let n = List.length cases in
    let rows = ref [] in
    List.iter (fun cs ->
        let r = [
          (match cs.dest with Some dd -> (match tried (fun () -> dd on cs.t) with Some l -> if l = cs.want then "dest ok" else "dest WRONG " ^ String.concat "," l | None -> "dest REFUSED") | None -> "-");
          (match cs.any with Some aa -> (match tried (fun () -> aa cs.t) with Some l -> if l = cs.want then "any ok" else "any WRONG" | None -> "any REFUSED") | None -> "-");
          (match cs.is with Some ii -> (if ii on cs.t then "is ok" else "is FALSE") ^ (if ii other cs.t then ", other name WRONGLY true" else "") | None -> "-");
          (match cs.dest with Some dd when cs.nm <> "dep0 (under 'other')" -> if tried (fun () -> dd other cs.t) = None then "other refused" else "other ACCEPTED" | _ -> "-") ] in
        rows := (cs.nm, String.concat "; " r) :: !rows) cases;
    List.iter (fun (nm, r) -> Printf.printf "%s %-32s %s\n" name nm r) (List.rev !rows);
    (* the matrix: is_X on the term built by Y, against shape equality *)
    let shape t = R.TermShape.string_of_shape (R.TermShape.shape_of_term t) in
    let agree = ref 0 and total = ref 0 and same = ref 0 and first = ref "" in
    List.iter (fun ci -> match ci.is with
        | None -> ()
        | Some ii -> List.iter (fun cj ->
            if Opname.eq (opname_of_term cj.t) on then begin
              incr total;
              (* token_simple takes any number of simple subterms: its own shape is a
                 token parameter and subterms without binders, of any count *)
              let expect =
                if ci.nm = "token_simple" then
                  (let sh = R.TermShape.shape_of_term cj.t in
                   sh.shape_params = [ ShapeToken ] && List.for_all (( = ) 0) sh.shape_arities)
                else shape ci.t = shape cj.t in
              if expect then incr same;
              if (try ii on cj.t with _ -> false) = expect then incr agree
              else if !first = "" then first := Printf.sprintf " (first: is_%s on %s)" ci.nm cj.nm end) cases) cases;
    Printf.printf "%s %-32s %d of %d (%d same-shape pairs)%s\n" name "is_X on Y's term = same shape" !agree !total !same !first;
    ignore n
end

module Std = S (Refiner_std.Refiner)
module Ds = S (Refiner_ds.Refiner)
let () = Std.run "std"; Ds.run "ds"
