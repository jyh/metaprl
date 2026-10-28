(*
 * filter_parse.ml finds camlp5's operator_rparen entry at load time with
 * Grammar.Entry.find on Pcaml.expr (camlp5 installs no pa_o.cmi). This test
 * runs that lookup with pa_o linked and parses with the entry it returns.
 * It checks the lookup, not the rest of filter_parse.
 *)
let entry_name =
   if Array.length Sys.argv > 1 then Sys.argv.(1) else "operator_rparen"

let operator : string Grammar.Entry.e =
   try Obj.magic (Grammar.Entry.find Pcaml.expr entry_name) with
      Not_found ->
         Printf.printf "FAIL: entry %s not found in Pcaml.expr\n" entry_name;
         exit 1

let parse s = Grammar.Entry.parse operator (Stream.of_string s)

let () =
   let ok = ref true in
   List.iter (fun (input, expected) ->
         let got = try parse input with e -> "<" ^ Printexc.to_string e ^ ">" in
         let pass = got = expected in
            if not pass then ok := false;
            Printf.printf "%s %S -> %S (expected %S)\n" (if pass then "OK  " else "FAIL") input got expected)
      ["+ )", "+"; "mod )", "mod"; "<*> )", "<*>"];
   if !ok then print_endline "OK operator_rparen found and parses" else exit 1
