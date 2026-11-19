(* unit-link: filter *)
(* Definition (library/), the Nuprl-5 link's table of definitions, fed
   broadcast terms through apply_broadcast as the link would: insert (with
   and without an auto-commit stamp), delete, commit and undo, then read
   back with directory_p, roots, directory_children and termtable_map.
   Nothing had reached import_term, term_to_data or auto_commit (2026-11-15
   rank: unit tests, theory build, proof census).  Every stamp is
   SYNTHETIC (a !stamp term with process "test"), never Basic.new_stamp,
   which reads this host; transaction n uses stamp n.  An entry inserted
   with a ObjectIdDAG description and a !directory substance is a
   directory (a root when the directory names one); every other entry is a
   term.  Each line prints ok, the value read, or the exception; Basic's
   Nuprl5_Exception is not exported, so its message is the lines
   Basic.error prints first.
   Read from the output: a later transaction sees a delete only once it is
   committed; an undone insert is gone, and committing it then is refused
   ("Tent Commit Missing"); termtable_map prints "oidtablemap fail" (no
   newline) for each entry the stamp cannot see.
   Not reached, stated: substance_import (only a definition's provide or
   get_substance calls it, term_entry is abstract, and nothing exported
   calls either), and term_to_data's !data_persist arm (its data are read
   from the link's database).
   The expected file is the output of the code as written (2026-11-16),
   never typed. *)
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Term_sig

let tok s = Token (Opname.mk_opname s Opname.nil_opname)
let num i = Number (Lm_num.num_of_int i)
let p = make_param
let n5 params bts = mk_term (Nuprl5.mk_nuprl5_op (List.map p params)) (List.map (mk_bterm []) bts)
let oid i = [ p (num i) ]
(* a SYNTHETIC stamp (never Basic.new_stamp, which reads this host) *)
let ftok s = Token (Opname.mk_opname s (Opname.mk_opname "FDL" Opname.nil_opname))
let stamp_t ?(tseq = 1) seq =
  mk_term (Nuprl5.mk_nuprl5_op [ p (ftok "!stamp"); p (num seq); Nuprl5.make_time_parameter (Lm_num.num_of_int 0); p (num tseq); p (ftok "test") ]) []
let stamp ?tseq seq = Basic.term_to_stamp (stamp_t ?tseq seq)
let c s = mk_simple_term (Opname.make_opname [ s; "Tdb" ]) []
let substance t = n5 [ tok "!substance" ] [ t; c "refs"; c "props"; c "super" ]
let inline_data t = n5 [ tok "!data_persist_inline"; tok "TERM" ] [ stamp_t 3; n5 [ tok "!data" ] [ substance t ] ]
let dep i = n5 [ tok "!dependency"; ObId (oid i) ] [ stamp_t 4; stamp_t 5 ]
let idef i t = n5 [ tok "!definition" ] [ dep i; inline_data t ]
let insert seq i t = n5 [ tok "!definition_insert"; num seq ] [ idef i t ]
let delete seq i = n5 [ tok "!definition_delete"; num seq; ObId (oid i) ] []
let commit seq i = n5 [ tok "!commit"; num seq; ObId (oid i) ] []
let undo seq i = n5 [ tok "!undo"; num seq; ObId (oid i) ] []
let child name i = n5 [ tok "!dag_child"; tok name; ObId (oid i) ] []
let cons a b = mk_term (Nuprl5.mk_nuprl5_op [ p (tok "!dag_cons") ]) [ mk_bterm [] a; mk_bterm [] b ]
let dir ?root kids =
  let ps = tok "!directory" :: (match root with Some r -> [ tok r ] | None -> []) in
  n5 ps [ Basic.list_to_ilist_by_op (Nuprl5.mk_nuprl5_op [ p (tok "!dag_cons") ]) kids ]
let itok s = n5 [ tok "!token"; tok s ] []
let idesc purposes = n5 [ tok "!description" ] [ Basic.inil_term; Basic.list_to_ilist_map Basic.itoken_term purposes ]

let say name f = Printf.printf "%-34s %s\n%!" name (try f () with Failure m -> "Failure " ^ m | Not_found -> "Not_found" | e -> Printexc.to_string e)
let s1 = stamp 1
let s2 = stamp ~tseq:2 2
let ids l = String.concat " " (List.map (fun o -> String.concat "." (List.map (fun q -> match dest_param q with Number n -> Lm_num.string_of_num n | _ -> "?") o)) l)

let () =
  let tt = Definition.make_termtable () in
  let void = Basic.ivoid_term in
  say "insert 7 (term), auto-commit" (fun () -> Definition.apply_broadcast tt (insert 1 7 (c "x")) void s1 (Some s1); "ok");
  say "directory_p 7" (fun () -> string_of_bool (Definition.directory_p tt s2 (oid 7)));
  let dagd = idesc [ "ObjectIdDAG" ] in
  say "insert 8 (root directory)" (fun () -> Definition.apply_broadcast tt (insert 2 8 (dir ~root:"top" [ child "a" 7; child "b" 9 ])) dagd s1 (Some s1); "ok");
  say "insert 9 (directory)" (fun () -> Definition.apply_broadcast tt (insert 3 9 (dir [])) dagd s1 (Some s1); "ok");
  say "insert 10 (DAG, not a directory)" (fun () -> Definition.apply_broadcast tt (insert 4 10 (c "y")) dagd s1 (Some s1); "ok");
  say "directory_p 8 / 9 / 10" (fun () -> String.concat " " (List.map (fun i -> string_of_bool (Definition.directory_p tt s2 (oid i))) [ 8; 9; 10 ]));
  say "roots" (fun () -> String.concat ", " (List.map (fun (n, o) -> n ^ "=" ^ ids [ o ]) (Definition.roots tt s2)));
  say "children of 8" (fun () -> String.concat ", " (List.map (fun (n, o) -> n ^ "=" ^ ids [ o ]) (Definition.directory_children tt s2 (oid 8))));
  let entries st = ids (List.sort compare (Definition.termtable_map tt st (fun o _ -> Some o))) in
  say "entries" (fun () -> entries s2);
  (* transaction 3: delete 7, not auto-committed *)
  let s3 = stamp ~tseq:3 3 and s4 = stamp ~tseq:4 4 in
  say "delete 7 in transaction 3" (fun () -> Definition.apply_broadcast tt (delete 5 7) void s3 None; "ok");
  say "entries seen by 3 (pending)" (fun () -> entries s3);
  say "entries seen by 4 (later)" (fun () -> entries s4);
  say "commit 7 seq 5 in transaction 3" (fun () -> Definition.apply_broadcast tt (commit 5 7) void s3 None; "ok");
  say "entries seen by 4 after commit" (fun () -> entries s4);
  (* transaction 5: insert 11, then undo it *)
  let s5 = stamp ~tseq:5 5 and s6 = stamp ~tseq:6 6 in
  say "insert 11 in transaction 5" (fun () -> Definition.apply_broadcast tt (insert 6 11 (c "z")) void s5 None; "ok");
  say "entries seen by 5" (fun () -> entries s5);
  say "undo 11 seq 6 in transaction 5" (fun () -> Definition.apply_broadcast tt (undo 6 11) void s5 None; "ok");
  say "entries seen by 5 after undo" (fun () -> entries s5);
  say "commit 11 after the undo" (fun () -> Definition.apply_broadcast tt (commit 6 11) void s5 None; "ok");
  say "entries seen by 6" (fun () -> entries s6);
  say "children of 7 (a term)" (fun () -> String.concat ", " (List.map fst (Definition.directory_children tt s2 (oid 7))));
  say "an unknown broadcast" (fun () -> Definition.apply_broadcast tt (n5 [ tok "!other"; num 1 ] []) void s5 None; "ok");
  say "a term that is not a definition" (fun () -> Definition.apply_broadcast tt (n5 [ tok "!definition_insert"; num 7 ] [ c "q" ]) void s5 None; "ok")
