(* unit-link: filter *)
(* Registry (library/), the MathBus label registry of the Nuprl-5 link:
   registry_lookup_value, registry_lookup_identifier, registry_store_local
   and clear_registry on labels of this test's own (the link reads its
   labels from lib/registry.txt, which no build installs;
   test_mbterm_round_trip stores them locally the same way).  StringId is
   bidirectional, SubTypes is not.  Each line prints the value found or
   the Failure.
   Read from the code: read_registry stores into the LOCAL registry, and
   nothing in the tree stores into the global one, so the global fallback
   of both lookups always finds nothing and the lookup fails with
   "undefined ..." (stated; the global tables are abstract here).
   Pinned as found: clear_registry empties the registry of its TYPES (the
   tables Hashtbl.clear removes are keyed by type), not of their entries,
   and define_registry_type will not define a type again (its name is still
   in registry_types), so after clear_registry false true every lookup
   fails and registry_store_local raises Not_found.  Nothing in the tree
   calls clear_registry: recorded here, not changed.
   The expected file is the output of the code as written (2026-11-16),
   never typed. *)
let i32 = Lint32.lint32_of_int
let s32 x = string_of_int (Lint32.int_of_lint32 x)
let say name f = Printf.printf "%-40s %s\n%!" name (try f () with Failure m -> "Failure " ^ m | Not_found -> "Not_found" | e -> Printexc.to_string e)

let () =
  Registry.registry_store_local "TestLabelA" "StringId" (i32 0x7101);
  Registry.registry_store_local "TestLabelB" "SubTypes" (i32 (-1));
  say "value TestLabelA StringId" (fun () -> s32 (Registry.registry_lookup_value "TestLabelA" "StringId"));
  say "identifier StringId 0x7101" (fun () -> Registry.registry_lookup_identifier "StringId" (i32 0x7101));
  say "value TestLabelB SubTypes" (fun () -> s32 (Registry.registry_lookup_value "TestLabelB" "SubTypes"));
  say "value TestLabelA SubTypes (not stored)" (fun () -> s32 (Registry.registry_lookup_value "TestLabelA" "SubTypes"));
  say "value Missing StringId" (fun () -> s32 (Registry.registry_lookup_value "Missing" "StringId"));
  say "identifier StringId 0x7102 (missing)" (fun () -> Registry.registry_lookup_identifier "StringId" (i32 0x7102));
  say "identifier SubTypes -1 (not bidirectional)" (fun () -> Registry.registry_lookup_identifier "SubTypes" (i32 (-1)));
  say "value TestLabelA NoSuchType" (fun () -> s32 (Registry.registry_lookup_value "TestLabelA" "NoSuchType"));
  Registry.clear_registry false true;
  say "after clear_registry false true" (fun () -> s32 (Registry.registry_lookup_value "TestLabelA" "StringId"))
;;
let () =
  say "store after clear_registry false true" (fun () -> Registry.registry_store_local "TestLabelC" "StringId" (i32 0x7103); "ok");
  Registry.define_registry_type "StringId" true;
  say "store after define_registry_type again" (fun () -> Registry.registry_store_local "TestLabelC" "StringId" (i32 0x7103); "ok")
