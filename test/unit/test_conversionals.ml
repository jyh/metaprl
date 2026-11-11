(* Conversionals_boot.Conversionals, the conversion combinators every rewrite
   tactic is written in, which no unit test named (coverage recount
   11-10).  Three input forms are made with create_iform
     swap  f{'a; 'b} --> f{'b; 'a}      ung  g{'a} --> 'a      wrap  c --> g{c}
   and combined at random with idC, failC, thenC, orelseC, tryC,
   progressC, allSubC, someSubC, higherC, lowerC, sweepUpC, sweepDnC,
   firstC, repeatC, repeatForC and addrC; each combination is applied with
   apply_rewrite to 300 random closed terms over f, g and c, and the result
   is compared with a model read from conversionals_boot.ml and
   rewrite_boot.ml:
     allSubC r    r on every immediate subterm; all must succeed; a leaf succeeds
     someSubC r   r on ONE immediate subterm, the first that succeeds; a leaf fails
     higherC r    r here, or else higherC r on every subterm; never fails
     lowerC r     someSubC (lowerC r), or else r here
     sweepUpC r   allSubC (sweepUpC r), then tryC r here
     sweepDnC r   tryC r here, then allSubC (sweepDnC r) on the RESULT
     repeatC r    r until it fails or leaves the term unchanged
     progressC r  r, failing if the term is unchanged
   addrC at an address the term does not have is NOT modelled: measured,
   addr [1] (tryC r) on c succeeds and leaves c, while the same miss under
   repeatC or sweepDnC fails through their tryC.  A random combination is
   kept only when the model reaches no such address (addr_ok below), and
   the miss cases are printed as fixed cases at the end.
   Bodies that would not terminate are not generated: sweepDnC of a body
   that can wrap (it descends into the c it makes), and repeatC of a body
   that can swap or wrap (swap twice is a cycle repeatC does not see).
   The generator is a fixed linear congruential sequence, not Random. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Conversionals_boot.Conversionals

let state = ref 1110
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

type d = C | G of d | F of d * d
let rec gen depth = if depth = 0 || pick 3 = 0 then C else if pick 2 = 0 then G (gen (depth - 1)) else F (gen (depth - 1), gen (depth - 1))

type c = Swap | Ung | Wrap | Id | Fail | Then of c * c | Else of c * c | Try of c | Progress of c
       | AllSub of c | SomeSub of c | Higher of c | Lower of c | SweepUp of c | SweepDn of c
       | First of c list | Repeat of c | RepeatFor of int * c | Addr of int list * c

(* fam: `All, `NoWrap (sweepDnC bodies), `Shrink (repeatC bodies: ung, id, fail and the shape combinators) *)
let rec gc fam depth =
  let base () = match fam with
    | `All -> [| Swap; Ung; Wrap; Id; Fail |].(pick 5)
    | `NoWrap -> [| Swap; Ung; Id; Fail |].(pick 4)
    | `Shrink -> [| Ung; Ung; Id; Fail |].(pick 4) in
  if depth = 0 then base () else
  let sub () = gc fam (depth - 1) in
  match pick 18 with
  | 0 | 1 | 2 -> base ()
  | 3 -> Then (sub (), sub ()) | 4 -> Else (sub (), sub ()) | 5 -> Try (sub ()) | 6 -> Progress (sub ())
  | 7 -> AllSub (sub ()) | 8 -> SomeSub (sub ()) | 9 -> Higher (sub ()) | 10 -> Lower (sub ())
  | 11 -> SweepUp (sub ())
  | 12 -> SweepDn (gc (if fam = `All then `NoWrap else fam) (depth - 1))
  | 13 -> First (List.init (1 + pick 3) (fun _ -> sub ()))
  | 14 -> Repeat (gc `Shrink (depth - 1))
  | 15 -> RepeatFor (pick 3, sub ())
  | _ -> Addr (List.init (1 + pick 2) (fun _ -> 1 + pick 2), sub ())

let rec cshow = function
  | Swap -> "swap" | Ung -> "ung" | Wrap -> "wrap" | Id -> "id" | Fail -> "fail"
  | Then (a, b) -> "(" ^ cshow a ^ " then " ^ cshow b ^ ")" | Else (a, b) -> "(" ^ cshow a ^ " orelse " ^ cshow b ^ ")"
  | Try a -> "try " ^ cshow a | Progress a -> "progress " ^ cshow a | AllSub a -> "allSub " ^ cshow a
  | SomeSub a -> "someSub " ^ cshow a | Higher a -> "higher " ^ cshow a | Lower a -> "lower " ^ cshow a
  | SweepUp a -> "sweepUp " ^ cshow a | SweepDn a -> "sweepDn " ^ cshow a
  | First l -> "first [" ^ String.concat "; " (List.map cshow l) ^ "]" | Repeat a -> "repeat " ^ cshow a
  | RepeatFor (n, a) -> Printf.sprintf "repeatFor %d %s" n (cshow a)
  | Addr (p, a) -> "addr [" ^ String.concat ";" (List.map string_of_int p) ^ "] " ^ cshow a

let kids = function C -> [] | G x -> [ x ] | F (x, y) -> [ x; y ]
let rebuild t ks = match t, ks with C, [] -> C | G _, [ x ] -> G x | F _, [ x; y ] -> F (x, y) | _ -> assert false
let ( >>= ) = Option.bind

(* The model. *)
let rec model r t =
  match r with
  | Swap -> (match t with F (a, b) -> Some (F (b, a)) | _ -> None)
  | Ung -> (match t with G a -> Some a | _ -> None)
  | Wrap -> (match t with C -> Some (G C) | _ -> None)
  | Id -> Some t | Fail -> None
  | Then (a, b) -> model a t >>= model b
  | Else (a, b) -> (match model a t with Some t' -> Some t' | None -> model b t)
  | Try a -> (match model a t with Some t' -> Some t' | None -> Some t)
  | Progress a -> (match model a t with Some t' when t' <> t -> Some t' | _ -> None)
  | AllSub a ->
      let ks = List.map (model a) (kids t) in
      if List.for_all Option.is_some ks then Some (rebuild t (List.map Option.get ks)) else None
  | SomeSub a ->
      let ks = kids t in
      let n = List.length ks in
      let rec try_ i = if i >= n then None else
          match model a (List.nth ks i) with
          | Some k -> Some (rebuild t (List.mapi (fun j x -> if j = i then k else x) ks))
          | None -> try_ (i + 1) in
      try_ 0
  | Higher a -> (match model a t with Some t' -> Some t' | None -> model (AllSub (Higher a)) t)
  | Lower a -> (match model (SomeSub (Lower a)) t with Some t' -> Some t' | None -> model a t)
  | SweepUp a -> model (AllSub (SweepUp a)) t >>= model (Try a)
  | SweepDn a -> model (Try a) t >>= model (AllSub (SweepDn a))
  | First l -> List.fold_right (fun c acc -> match model c t with Some t' -> Some t' | None -> acc) l None
  | Repeat a ->
      let rec loop t = match model a t with Some t' when t' <> t -> loop t' | _ -> t in
      Some (loop t)
  | RepeatFor (n, a) -> if n = 0 then Some t else model a t >>= model (RepeatFor (n - 1, a))
  | Addr (p, a) ->
      let rec at p t = match p with
        | [] -> model a t
        | i :: p -> (match List.nth_opt (kids t) (i - 1) with
            | None -> None
            | Some k -> at p k >>= fun k' -> Some (rebuild t (List.mapi (fun j x -> if j = i - 1 then k' else x) (kids t)))) in
      at p t

(* Does applying r to t (by the model's own route) ever reach an addrC whose address t lacks? *)
exception Miss
let rec reach r t =
  let go c t = ignore (reach c t) in
  match r with
  | Swap | Ung | Wrap | Id | Fail -> model r t
  | Then (a, b) -> (match reach a t with Some t' -> reach b t' | None -> None)
  | Else (a, b) -> (match reach a t with Some t' -> Some t' | None -> reach b t)
  | Try a -> (match reach a t with Some t' -> Some t' | None -> Some t)
  | Progress a -> ignore (reach a t); model r t
  | AllSub a | SomeSub a -> List.iter (go a) (kids t); model r t
  | Higher a -> (match reach a t with Some t' -> Some t' | None -> List.iter (go (Higher a)) (kids t); model r t)
  | Lower a -> List.iter (go (Lower a)) (kids t); go a t; model r t
  | SweepUp a -> List.iter (go (SweepUp a)) (kids t); (match model (AllSub (SweepUp a)) t with Some t' -> go a t' | None -> ()); model r t
  | SweepDn a -> go a t; (match model (Try a) t with Some t' -> List.iter (go (SweepDn a)) (kids t') | None -> ()); model r t
  | First l -> List.iter (fun c -> go c t) l; model r t
  | Repeat a -> let rec loop t = (match reach a t with Some t' when t' <> t -> loop t' | _ -> ()) in loop t; model r t
  | RepeatFor (n, a) -> if n = 0 then Some t else (match reach a t with Some t' -> reach (RepeatFor (n - 1, a)) t' | None -> None)
  | Addr (p, a) ->
      let rec at p t = match p with
        | [] -> go a t
        | i :: p -> (match List.nth_opt (kids t) (i - 1) with None -> raise Miss | Some k -> at p k) in
      at p t; model r t
let addr_ok r t = try ignore (reach r t); true with Miss -> false

let op s = Opname.make_opname [ s ]
let rec build = function C -> mk_simple_term (op "c") [] | G a -> mk_simple_term (op "g") [ build a ] | F (a, b) -> mk_simple_term (op "f") [ build a; build b ]
let rec back t =
  let { Term_sig.term_op; term_terms } = dest_term t in
  match Opname.dest_opname (dest_op term_op).Term_sig.op_name, List.map (fun b -> back (dest_bterm b).Term_sig.bterm) term_terms with
  | [ "c" ], [] -> C | [ "g" ], [ a ] -> G a | [ "f" ], [ a; b ] -> F (a, b) | _ -> failwith "back"

let sov x = TermMan.mk_so_var_term (Lm_symbol.add x) [] []
let swap = create_iform "swap" false (mk_simple_term (op "f") [ sov "a"; sov "b" ]) (mk_simple_term (op "f") [ sov "b"; sov "a" ])
let ung = create_iform "ung" false (mk_simple_term (op "g") [ sov "a" ]) (sov "a")
let wrap = create_iform "wrap" false (build C) (build (G C))

let rec real = function
  | Swap -> swap | Ung -> ung | Wrap -> wrap | Id -> idC | Fail -> failC
  | Then (a, b) -> prefix_thenC (real a) (real b) | Else (a, b) -> prefix_orelseC (real a) (real b)
  | Try a -> tryC (real a) | Progress a -> progressC (real a) | AllSub a -> allSubC (real a)
  | SomeSub a -> someSubC (real a) | Higher a -> higherC (real a) | Lower a -> lowerC (real a)
  | SweepUp a -> sweepUpC (real a) | SweepDn a -> sweepDnC (real a) | First l -> firstC (List.map real l)
  | Repeat a -> repeatC (real a) | RepeatFor (n, a) -> repeatForC n (real a)
  | Addr (p, a) -> addrC (List.map (fun i -> Term_addr_sig.Subterm i) p) (real a)

let apply c t = try Some (back (apply_rewrite Mp_resource.empty_bookmark (real c) (build t))) with RefineError.RefineError _ -> None

let () =
  let n = 300 and agree = ref 0 and ok = ref 0 and shown = ref 0 in
  for _ = 1 to n do
    let rec draw () = let c = gc `All 3 and t = gen 4 in if addr_ok c t then c, t else draw () in
    let c, t = draw () in
    let m = model c t and r = apply c t in
    if m = r then incr agree
    else if !shown < 16 then begin incr shown;
      let rec sh = function C -> "c" | G a -> "g{" ^ sh a ^ "}" | F (a, b) -> "f{" ^ sh a ^ "; " ^ sh b ^ "}" in
      let so = function None -> "fails" | Some t -> sh t in
      Printf.printf "DIFFER %s on %s: model %s, real %s\n" (cshow c) (sh t) (so m) (so r) end;
    if r <> None then incr ok
  done;
  Printf.printf "conversion combinations agreeing with the model: %d/%d (%d succeeded, %d failed)\n" !agree n !ok (n - !ok);
  (* A few fixed cases, printed. *)
  let show = function None -> "fails" | Some t ->
    let rec s = function C -> "c" | G a -> "g{" ^ s a ^ "}" | F (a, b) -> "f{" ^ s a ^ "; " ^ s b ^ "}" in s t in
  List.iter (fun (c, t) -> Printf.printf "%-28s on %-22s %s\n" (cshow c) (show (Some t)) (show (apply c t)))
    [ SomeSub Ung, F (G C, G C); Lower Ung, G (G C); Higher Swap, G (F (C, G C)); SweepUp Wrap, F (C, C);
      SweepDn Swap, F (F (C, G C), C); SweepDn Ung, G (G C); SweepUp Ung, G (G C); Repeat Ung, G (G (G C)); Progress Id, C; AllSub Fail, C; SomeSub Id, C;
      RepeatFor (2, Ung), G C; Addr ([ 2 ], Ung), F (C, G C); First [ Fail; Wrap ], C;
      (* addrC at an address the term lacks (measured, not modelled) *)
      Addr ([ 1 ], Ung), C; Addr ([ 1 ], Try Ung), C; Addr ([ 1 ], Id), C; Repeat (Addr ([ 1 ], Fail)), C;
      SweepDn (Addr ([ 1 ], Swap)), C; Try (Addr ([ 1 ], Ung)), C ]
