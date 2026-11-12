(* Dform's built-in commands (refiner/reflib/dform.ml, init_list) printed
   through the null base, where they are the only forms: the break and zone
   commands over string and meta-string parameters (a meta parameter prints
   its variable's name), pushm over a number, a meta number, a string and
   nothing, pushfont/popfont for every font name, and plain variable terms.
   The whole test runs as a child with TERM removed from its environment:
   Lm_terminfo decides at start-up from TERM whether it looks capabilities
   up, so without it pushfont and popfont print nothing on every machine.
   That pins their silence without a terminal, NOT which capability each
   font name selects (translate_font's table): that output depends on the
   terminal and is not checked here. The expected file is the code's
   output as written, never typed. *)
open Opname
open Refiner.Refiner
open TermType
open Term
open TermMan
open Dform

let cmd n ps = mk_term (mk_op (mk_opname n xperv) ps) []
let s = mk_xstring_term
let st x = make_param (String x)
let ms x = make_param (MString (Lm_symbol.add x))
let show name t =
  Printf.printf "== %s\n%s\n" name (try string_of_term null_base t with e -> "EXCEPTION " ^ Printexc.to_string e)

let child () =
  Printf.printf "TERM set: %b\n" (Sys.getenv_opt "TERM" <> None);
  show "hbreak[\"Y\"; \"N\"]" (mk_xlist_term [ s "a"; cmd "hbreak" [ st "Y"; st "N" ]; s "b" ]);
  show "hbreak[y:s; n:s]" (mk_xlist_term [ s "a"; cmd "hbreak" [ ms "y"; ms "n" ]; s "b" ]);
  show "sbreak[y:s; n:s]" (mk_xlist_term [ s "a"; cmd "sbreak" [ ms "y"; ms "n" ]; s "b" ]);
  show "cbreak[y:s; n:s]" (mk_xlist_term [ s "a"; cmd "cbreak" [ ms "y"; ms "n" ]; s "b" ]);
  show "tzone[t:s]" (mk_xlist_term [ cmd "tzone" [ ms "t" ]; s "x"; cmd "ezone" [] ]);
  show "tzone[\"tag\"]" (mk_xlist_term [ cmd "tzone" [ st "tag" ]; s "x"; cmd "ezone" [] ]);
  List.iter (fun (n, ps) -> show n (mk_xlist_term [ cmd "pushm" ps; s "x"; cmd "popm" [] ]))
    [ "pushm[3]", [ make_param (Number (Lm_num.num_of_int 3)) ];
      "pushm[i:n]", [ make_param (MNumber (Lm_symbol.add "i")) ];
      "pushm[\"2\"]", [ st "2" ];
      "pushm[]", [] ];
  List.iter (fun f -> show ("pushfont[\"" ^ f ^ "\"]")
                (mk_xlist_term [ s "a"; cmd "pushfont" [ st f ]; s "b"; cmd "popfont" []; s "c" ]))
    [ "bf"; "it"; "em"; "rm"; "sub"; "sup"; "ul"; "other" ];
  show "pushfont[plain:s]" (mk_xlist_term [ s "a"; cmd "pushfont" [ ms "plain" ]; s "b"; cmd "popfont" [] ]);
  show "a variable x" (mk_var_term (Lm_symbol.add "x"));
  show "a second-order variable v" (mk_so_var_term (Lm_symbol.add "v") [] [ mk_var_term (Lm_symbol.add "x") ])

let () =
  if Array.length Sys.argv > 1 && Sys.argv.(1) = "--child" then child ()
  else begin
    let keep e = not (String.length e >= 5 && String.sub e 0 5 = "TERM=") in
    let env = Array.of_list (List.filter keep (Array.to_list (Unix.environment ()))) in
    let pid = Unix.create_process_env Sys.executable_name [| Sys.executable_name; "--child" |] env
        Unix.stdin Unix.stdout Unix.stderr in
    match snd (Unix.waitpid [] pid) with
    | Unix.WEXITED 0 -> ()
    | Unix.WEXITED n -> Printf.printf "child exit %d\n" n; exit 1
    | _ -> print_endline "child killed"; exit 1
  end
