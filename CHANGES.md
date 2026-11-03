# Changes

## Unreleased

### Fixed through libmojave 1.1.1

MetaPRL reads its shell input and serves its browser through libmojave; built
against libmojave 1.1.1 or later:

- `mp`'s shell accepts a command line of any length. Without GNU readline
  (every dune build of libmojave), a line of 1,022 characters or more came back
  in pieces, so a long command failed with a parse error (jyh/libmojave#117).
- A line ending in `\` continues onto the next line, as the shell intends.
  Lines came back with their newline, so the shell's continuation test never
  saw the `\` at the end (jyh/libmojave#118).
- The browser server's plain (non-SSL) connections close their sending side on
  `shutdown`, as the SSL path does; before, a client waiting for end of file
  waited until the connection was closed (jyh/libmojave#126).

### Fixed

- The browser server answers a refused request (`ForbiddenCode`, sent by the
  shell's browser for a forbidden path) with `403 Forbidden`; it sent `402`,
  which is Payment Required. mllib's unused `Http_server` carries the same
  table and is left as it is.
- term_ds's `TermSubst.standardize` (term_ds is the default refiner) gave back
  a context's arguments in reverse order: a context hypothesis
  `<K<||>[a; b]>` came back as `<K<||>[b; a]>` (three list reversals where
  two were meant), and a context term `<H>[a; b]` likewise (one where two
  were meant: no `List.rev`, which the second-order case has),
  so the result was not alpha-equal to the term it renamed. term_std was
  right. Its one caller outside the debug refiner is the experimental M
  compiler's `m_standardize`. Found by the new TermSubst checks in
  `test/unit/test_term_differential.ml`: 211 of 2,000 terms, and the
  context term.
- term_ds's `TermMan.all_vars_info` left out bound variables (term_std
  records them as first order). Its callers take the names it returns as
  the names in use and pick a fresh one outside them (itt_vec_sequent_term's
  `hoist_hyps_length_tac`, meta_context_ind1's `new_vars_table`), so on
  term_ds the "fresh" name could be one the term binds. 562 of 2,000 terms.
- term_std's `TermMan.explode_term` of a second-order variable listed one
  subterm more than its arguments: the contexts list term_std keeps as a
  last subterm. It now lists the arguments only, as term_ds and the
  signature's "standard form" do. 281 of 2,000 terms (every one whose root
  is a second-order variable).
- A module whose id is 2^30 or more could not be built from its proof
  archive (`.prla`): the filter refused it with `Filter_summary.dest_id:
  not an int`. The id is an OCaml int written as a decimal; reading it,
  `Lm_num` makes a decimal at or above 2^30 a big number, and `dest_id`
  asked whether it fits `Lm_num`'s 30-bit range. Such ids occur on 64-bit
  (the hash is seeded with bit 30 set); no committed archive has one, and a
  new module was the first. `dest_id` now reads the decimal as an OCaml
  int. Test: `test/filter_prla_id/run.sh` (a CI step after the build)
  compiles a copied theory with ids 1,511,842,520, 609,661,056 and
  -1,000,750,977; before the fix the first was refused.
- term_std (`TERMS = std`; term_ds, which the refiner uses, was right) put
  context hypotheses and contexts lists where term_ds does not: its
  addressing indexed them (#56), `map_down`, `map_up`, `iter_down` and
  `iter_up` visited them (#57), and `find_subterm` walked into them (#58).
  A `TERMS = std` proof census lost 8 proofs to these; it now loses none.
  term_std's `all_vars` also left out contexts-list names and `is_fo_term`
  called a sequent first-order (#72).
- term_ds's `match_terms` let a bound variable of the pattern match any
  subterm, so `lam x.f{'x}` matched `lam y.f{c}` (#63), and its `all_vars`
  left out the variables a bound term binds (#67).
- `Term_match_table` lost a sequent pattern with hypotheses on both sides of
  its context (`{ 'a; <H>; 'b >- c }`): `compile_sequent` built the
  pattern's program from the stack it was given instead of the one its
  recursion returned, dropping the hypotheses after the context, so a
  lookup missed the entry even where the rewriter's own matcher accepts the
  pattern. The tables behind resources (intro, elim, the decision tables)
  are of this kind. Found by `test/unit/test_term_match_seq.ml`: 64 of 600
  tables missed a matching value, none now.
- `Tactic_boot` compared one argument's term-list attributes with
  themselves, so the proof editor could reattach a stored sub-proof to a
  subgoal whose term-list attribute differs (#59).
- `Unify_mm.unifiable` said true for a variable equated with a term that
  contains it (`'d = f{..'d..}`): the occurs check was skipped (#64).
- `Ctime.parse_time` read every HTTP date as 0, in all three forms a server
  must accept; it now reads them, in UTC (#71).
- Hash-consing could give one term two live indices after a subterm was
  collected, so `Term_eq_table` missed keys it held (#76).
- `Term.ops_eq` (term_std and term_ds) compared parameters with polymorphic
  equality, so an operator whose number was computed as a product kept as a
  big integer (`40000 * 3`) differed from the same operator written with
  `120000`, while `alpha_equal` (which compares numbers by value) called the
  terms equal; on 3,000 generated pairs 68 disagreed. It now compares
  parameters as `alpha_equal` does. Its caller in a theory is
  `if_same_op` (`base_reflection`).
- `Supinf`'s `isNumber` compared unreduced fractions with polymorphic
  compare, so a zero coefficient such as 0/4 counted as nonzero and the
  SUP-INF procedure could miss a bound it had derived; it could only lose
  proofs, not admit false ones (#78).
- `check_all ()`, the grounded check, read every proved rule of a module named
  like its theory (`itt_rfun`, `itt_supinf`) as depending on an incomplete
  copy of itself. Rules are registered with `Shell_command.extract [module;
  rule]`, which resolved the pair as a path from the root, where a theory
  name wins over a module of the same name. It now looks the module up by
  name. Proofs were never affected (`status_all` read them complete).
  Test: `editor/ml/tests/no_self_dependency.sh`, a CI step after the proof
  replay and in the weekly Windows census; on `THEORIES = all` it checks
  5,232 rules in 330 modules and finds 0 self-dependencies (#90).
- `omake install` worked on Linux only: it ran GNU `/bin/cp -L -r
  --remove-destination`, which macOS's BSD cp rejects (nothing was
  installed) and native Windows omake cannot run. It now copies with
  OMake's own `mkdir` and `cp`, following symbolic links to files and
  merging into an existing install; a link to a directory stops it with a
  message. The install tests run on Linux, macOS and the Windows lane.

### Tests

- Unit tests for MetaPRL's OCaml libraries (`test/unit/`, #51): each
  `test/unit/test_*.ml` is built against the built libmojave and `mllib`,
  run, and compared with its `.expected` file by `test/unit/run.sh`, a CI
  step after the build, on Linux and Windows. The first, `test_bitset.ml`, checks `mllib`'s
  `Bitset` against a bool array (100,000 reads, none differ). `refiner/`
  and `mllib/` had no unit tests; the proof census tests them end to end.
- JProver on propositional formulas (`test/unit/test_jprover_prop.ml`, #79):
  on 400 generated formulas, classical JProver proves exactly the
  tautologies, whatever LJ proves is a tautology, LJ proves `~~F` exactly
  when `F` is a tautology (Glivenko), and LJ and LJmc agree: 383 of 383
  checked. The 17 on which LJ did not finish in 10 s are skipped and
  counted (see Known not to work).
- `File_base`, which chooses which of a module's files to load
  (`test/unit/test_file_base.ml`): the first directory on the path that
  has any of them, and in it the newest by mtime, the earlier file type on
  a tie. Eight cases agree with a model of that rule; mutants that break
  the tie the other way or ignore the mtime differ in 2 and 6. This is why
  a newer archive of any kind shadows the stored proof (a session's
  auto-saved `.cmoz` is read instead of the `.prla`). Recorded: when the
  newest file cannot be unmarshalled, loading fails; it does not fall back
  to an older file.
- `Term_dtable`, the table behind the intro step for subtype goals
  (`Itt_subtype`), against a model (`test/unit/test_term_dtable.ml`): a
  small subtyping system inserted the three ways itt theories insert one,
  looked up on all 576 pairs of ground terms up to depth 1; the table and
  the model give the same derivation on all 576 (a mutant that lets older
  entries win makes 4 differ; one that stops at the first matching entry
  whose subgoals fail makes 2 differ). The test records two behaviours
  that may be bugs: a left-to-right entry answers every goal whose left
  side matches, with the derivation of a different pair (92 of 104
  answers; `Itt_set`'s set rule is one), and a right-to-left entry whose
  right side is a variable answers no ground goal (`Itt_void`'s void
  rule). Both rules also carry their own intro annotation.
- `Term_copy2_weak`, which copies terms between term implementations for
  the filter's proof cache and `Term_io` (`test/unit/test_term_copy2_weak.ml`):
  2,000 generated terms copied between term_std and term_ds; convert gives
  the ds term built from the same description, revert gives the std term,
  and revert of convert is the identity, on all 2,000 (a mutant that
  reverses subterms in the copy's header makes the first two 1,604; the
  round trip cannot see a defect that is undone on the way back). Two
  copies of one term convert to one shared term on all 2,000, with a full
  GC between the two converts (#84). The 1,961 to 1,980 first reported
  here was not reproduced on this code; built against `Weak_memo` from
  before #76 the same check reads 1,038 of 2,000.
- The filter's term-type checking (`term_ty_infer`) on seven small theories
  (`test/filter_types/`, a CI step after the build, Linux only): building
  the theories shows that well-typed declarations are accepted, and these
  check that ill-typed ones are refused, with the error: a Dform result
  where a Term is required, a Dform argument where a Term is taken, a
  Dform-typed bound variable used as a Term, and a wrong arity; and three
  that must be accepted, including a Term where a Dform is taken (perv
  declares `Dform <- Term`). A mutant whose subtype check accepts makes
  the three type errors pass.
- `Term_match_table.lookup_bucket` and `lookup_rmap`
  (`test/unit/test_term_match_table.ml`, 600 tables each, against the same
  matching model): the bucket is every value added with one most specific
  matching pattern, patterns being the same up to the names of their
  variables (`'a` and `'b` share one); `lookup_rmap` returns a most specific
  pattern's newest value with its contracta instantiated by the match. A
  bucket cut to its first value fails 127 tables; reversed contracta fail 8.
- Display forms (`editor/ml/tests/dform_golden.sh`, a CI step after the
  build): `mp -batch` prints 59 goals, one per itt/core module (its first
  rule with a stored complete proof), and the text is compared with
  `dform_golden.expected`. Until now nothing pinned printed output; the
  proof census reads rule statuses. A mutant that changes one bracket in
  `itt_record_renaming`'s `rename_df` changes 10 lines of the output.
  ASCII display mode only, at mp's default width of 80.
- Term shapes (`test/unit/test_term_shape.ml`): on 500 generated terms with
  parameters of each kind and binders, in both implementations, the
  canonical term of a shape has that shape, `opparam_of_term` and back
  gives the same shape, and `shape_compare` is 0 exactly when `eq` holds;
  both print every shape the same. Mutants that reverse a shape's
  arities or parameters, or cap an arity at 1, each fail.
- `mllib`'s `Sort`, `List_neq_append`, `Flist` and `Permutations` are
  checked against plain OCaml (`test/unit/test_mllib_models.ml`, #52), as
  their interfaces state them. No defect. `List_neq_append.to_list`
  returns the elements in reverse order of insertion (no order is
  documented; the test records it).
- Meta terms, the statements of rules (`test/unit/test_term_meta.ml`): on 400
  generated statements in both implementations, the zip/unzip pairs for
  implications and functions give back their parts, `meta_alpha_equal`
  holds for a renamed copy and fails for a different statement,
  `term_of_meta_term` and back is the same, `free_vars_mterm` is the parts'
  free variables plus the meta-functions' variables (a rule's arguments
  count as free), and free-variable encoding round-trips. Recorded as it
  stands: `meta_alpha_equal` ignores labels and a meta-function's variable,
  so `(a:c -> 'a)` and `(b:c -> 'b)` compare unequal while `(a:c -> 'b)`
  and `(b:c -> 'b)` compare equal (its main caller strips meta-functions
  first). Three mutants each fail.
- `mllib`'s `Latin1_case` (all 256 characters against ISO 8859-1, and its
  string functions) and `Precedence` (`get_prec` against the closure of
  `add_lt` and `add_eq`) are checked (`test/unit/test_mllib_models2.ml`,
  #53). No defect. `mllib/simplehashtbl.ml` is not built (it is not in
  mllib's `FILES`) and nothing uses it.
- The refiner's rewrite combinators (`test/unit/test_refine_rw.ml`):
  `andthenrw`, `orelserw`, `rwhigher` and `rwaddr` over three rewrites made
  with `create_rewrite` in a null refiner, 60 random combinations on 5
  random terms each, through `rwtactic` and `refine`, against a model; all
  300 agree. Recorded: `rwhigher` never fails — where its rewrite applies
  nowhere it leaves the term as it is. `refine.ml` had no unit test before.
  Mutants that swap `andthenrw`'s order, drop `orelserw`'s fallback, or
  ignore `rwaddr`'s address each fail.
- `mllib`'s `Memo`, `Weak_memo` and `Line_buffer` are checked
  (`test/unit/test_mllib_models3.ml`, #54): memo tables against the
  function they memoize, the weak table across forced major collections
  (which drive its slot reuse; a hash table that kept a reused slot's old
  entry reads 1,515 of 6,000 wrong), and the bounded buffer and table
  against lists. No defect. `LineTable` evicts by `Unix.gettimeofday`, and
  entries added in the same clock tick are ordered by key, so on a coarse
  clock (Windows) a newly added key that sorts first can be the one
  evicted; the test adds keys in increasing order and records this.
- `TermAddr.subterm_exists` and `strip_address`
  (`test/unit/test_term_addr_std_ds.ml`): on four terms (the sequent, an
  operator, a binder, a second-order variable) and 157 addresses each,
  `subterm_exists` holds exactly when `term_subterm` answers, and
  `strip_address` of every prefix composes back to the address, in both
  implementations. Recorded, not endorsed: on a sequent, term_std answers
  plain `Subterm` addresses by walking its own encoding of the sequent,
  where term_ds refuses (8 of 628 pairs).
- metaprl's two term implementations disagree on addresses under a
  context hypothesis (`test/unit/test_term_addr_std_ds.ml`, #55, a pin:
  16 of 36 addresses differ). For `sequent { <H>; x: A; <K['t1; it]> >- C }`,
  term_ds's `term_subterm` at `[ClauseAddr 3; Subterm j]` is the j-th
  argument of `K`, while term_std's exposes the rest of the sequent
  (`concl{C}`, a trailing `xnil`) as further subterms, so negative indexes
  and indexes past the arguments differ. The refiner uses term_ds
  (`TERMS = ds`); with `TERMS = std` the proof census loses 90 proofs, all
  in theories built on such contexts, and `TERMS = both` stops the build on
  this disagreement. `test/unit/run.sh` now also links the refiner.
- Fixed: term_std's addressing (`refiner/term_gen/term_addr_gen.ml`, #56)
  now addresses a context hypothesis as `K<|conts|>[args]` and does not
  count the contexts list of a second-order variable or context as a
  subterm, as term_ds does and as `subterm_addresses` in the same file
  already listed them; the pin above reads 0 of 36. Its `subterm_addresses`
  also lists the arguments of a context hypothesis in increasing order, as
  term_ds does (it listed them in decreasing order, and tactics take them
  in order). The refiner (term_ds) does not use this file. With both
  fixes a `TERMS = both` build no longer stops on `term_subterm`; the 66
  remaining reports compare rewrite justifications with polymorphic
  equality across the two representations and also fire in proofs that
  pass. The 90 proofs a `TERMS = std` census loses are unchanged: their
  first failure is a context-hoisting rewrite whose subgoal drops the
  `<|S|>` contexts of `A2` and `T`, which `Refiner_debug` cannot see (it
  compares term shapes only).
- Fixed: term_std's `map_down`, `map_up`, `iter_down` and `iter_up`
  (`refiner/term_std/term_op_std.ml`, #57) applied the function to a
  context hypothesis, which term_std encodes as a context node, and
  visited the contexts lists of variables; term_ds does neither
  (`test/unit/test_term_op_std_ds.ml`: 6 of 6 lines differed, now 0).
  `Refine.mk_rewrite_hack` adds the context `H` to every second-order
  variable and context with `map_down`, so under `TERMS = std` a rule's
  rewrite goal was a different term from the one its stored proof was
  made for: the `TERMS = std` proof census loses 8 proofs instead of 90
  (6 in `itt_vec_sequent_term`, 1 in `itt_hoas_sequent_term`,
  `cic_prop_connectives and_elimL`).
- Fixed: term_std's `find_subterm` (`refiner/term_gen/term_addr_gen.ml`,
  #58) returned addresses `term_subterm` refuses: paths into the contexts
  lists of second-order variables and contexts, and, inside a sequent, paths
  through the term that encodes its hypotheses. The reduce resource
  (`support/tactics/top_conversionals.ml`) takes these addresses on a rule's
  redex and applies them to its instances, where a context such as `<J>`
  stands for any number of hypotheses, so under `TERMS = std` a conditional
  rule's reduction raised and `reduceC` fell back to the identity. It now
  addresses a sequent by clause (`ArgAddr`, `ClauseAddr i`, `ClauseAddr 0`)
  and names only arguments, as term_ds does
  (`test/unit/test_find_subterm_std_ds.ml`: 5 of 9 addresses refused and the
  redex's address refused on its instance; now 0, and both agree with
  term_ds). The `TERMS = std` proof census now replays all 264 modules and
  5,191 rule statuses as stored, as `TERMS = ds` does.
- Fixed: `Tactic_boot`'s `tactic_arg_alpha_equal_with_attributes`
  (`tactics/proof/tactic_boot.ml`, #59) compared the first argument's
  term-list attributes with themselves, so two tactic arguments that
  differed only there compared equal, and the proof editor could re-attach
  a stored sub-proof to a subgoal whose term-list annotations differ
  (`test/unit/test_tactic_arg_attributes.ml`: `[a]` against `[b]` and against
  `[a; b]` read equal, now different). No stored proof depended on it: the
  proof census is unchanged (264 modules, 5,191 rule statuses).
- term_std and term_ds are compared on 2,000 pseudo-random terms
  (`test/unit/test_term_differential.ml`, #60): sequents with hypotheses and
  context hypotheses, second-order variables with contexts lists, binders;
  for each, the term, `subterm_addresses` and `term_subterm`,
  `find_subterm`, `free_vars_set`, `alpha_equal` against a renamed copy,
  the terms `TermOp.iter_down` visits, and `TermSubst.subst` of a term
  that a binder could capture (compared up to bound-variable names: term_std
  renames such a binder even where the variable does not occur, term_ds does
  not). All agree; a term_std substitution that ignores a single variable
  makes the last check disagree on 1,096. On the code before
  #56–#58 the same test finds the defects those fixed: `subterm_addresses`
  disagrees on 84 terms, `find_subterm` on 921, `iter_down` on 1,054.
  The rewriter is compared the same way (`test/unit/test_rewrite_differential.ml`):
  four rules (an operator, a beta rule with a second-order body, a sequent
  with a context and a hypothesis, the `hyps_length` rule of #58) compiled
  in both implementations and applied to 400 instances of each redex and to
  400 random terms; all agree. The defects #56–#58 fixed do not reach the
  bare rewriter, so it was checked with a mutant instead: a term_std
  substitution that ignores a single variable makes the beta rule disagree
  on 152 of its 400 instances.
  The rewriter's separate redex interface, which the filter's generated
  code and every display form (`Term_match_table.lookup_rwi`) use, is
  checked against first-order matching (`test/unit/test_rewrite_redex.ml`):
  `compile_redex`, `compile_redices`, `extract_redex_types`,
  `test_redex_applicability` and `apply_redex` on 500 patterns and 500 pairs
  of redices over terms and a number parameter, in both implementations,
  and `lookup_rwi` on 300 tables; all agree. It records that
  `compile_redices [p; q]` lists `q`'s variables before `p`'s. Mutants that
  reverse `apply_redex`'s items or `extract_redex_types`' list, or make
  `test_redex_applicability` accept every term, each turn their checks red.
  Term I/O, through which stored proofs come back, is checked by round
  trip (`test/unit/test_term_io.ml`): the same 2,000 terms written with
  `Ascii_io.AsciiIO.write_term` and read back, one per file and as the
  filter saves a proof file (each written with the table read from the
  previous version), are alpha-equal to what was written. A reader that
  reverses a term's subterms makes 396 of them differ.
  `Match_seq.match_hyps`, which re-attaches a sub-proof when hypotheses were
  added, is checked against a model on 20,000 pairs of sequents
  (`test/unit/test_match_seq.ml`): it succeeds exactly when the model says
  a match exists and every mapping it returns is a valid matching (a
  mutant that forgets to record a hypothesis match makes 5,997 invalid).
  The test records one asymmetry: a big context is never skipped while
  small hypotheses remain, but once they are all matched the rest of the
  big sequent is skipped, contexts too (big `<K>; x: B` matches small with
  no hypotheses).
- Rules whose contractum carries parameters (`test/unit/test_rewrite_params.ml`):
  five rules that move a number, a string and a token parameter, swap two,
  add constant parameters and require a repeated parameter variable to
  match equal numbers, each applied to 300 instances and 300 near misses in
  both implementations and compared with a model; all agree, and a
  contractum parameter the redex does not bind does not compile. A mutant
  that reverses the contractum's parameters fails the two rules with
  several (0 of 300).
- `Term_stable`, the table keyed by a term's shape behind itt_squash's
  unsquash resource (`test/unit/test_term_stable.ml`): 300 generated terms
  inserted and 1,000 looked up, one in five of a shape never inserted;
  `slookup_all` returns the values whose shape matches, newest first, and
  `slookup` the newest or `Not_found`, against a model that computes the
  shape from the term's structure, on all 1,000. Mutants: inserting with
  `Hashtbl.replace` (212), counting no binders (790), giving a Token
  parameter the Number kind (983). Recorded: a variable and a
  second-order variable with no arguments have the same shape.
- Three more rules check the matcher against a model as well as across
  the implementations: a second-order variable that occurs twice as a
  pattern (rewrites exactly when the two bodies are the same up to the
  binder), a second occurrence that is an instance (`'b[c]`: exactly when it
  is the first body with `c` for its variable), and a conclusion restricted
  to no context (`'C<||>`: exactly when no variable of `<J>` occurs); all
  400 of 400. Disabling `check_simple_match`, `check_match` or
  `check_var_restrictions` each fails its own model.
- How the shell resolves paths (`editor/ml/tests/dir_of_path_precedence.sh`,
  #92): an absolute path whose first part names a theory is the theory, even
  when a module has the same name (`/itt_supinf/<rule>` asks for a module
  named `<rule>`); `..`, `...`, `~` and `.` from a proof or a module; and, as
  it is, a module reached under another theory's name (`../itt_supinf` from
  `itt_int_base`) — the theory part is not checked against the module.
- What the shell's `ls` options select (`editor/ml/tests/ls_options.sh`):
  on `itt_int_base`, `r` lists only rewrites and definitions, `R` only rules,
  `rR` both, `u` exactly the rewrites and rules not yet proved, `p` the
  `Extends` lines, `d` display forms, `D` documentation, `f` no informal
  items, `a` everything `f` and `i` list; an unknown option is an error and
  the shell goes on. Checked by the kind of each entry, not by counts.
- The proof census ends a module's rows at the next module (#93): a module
  named like its theory is entered through the theory, whose `status_all`
  replays every module in it, and `itt_rfun`'s rows had also carried
  `itt_well_founded_equiv`'s `well_founded_reduction`.
- Rules over universe levels (`test/unit/test_rewrite_levels.ml`):
  `u[l] --> v[l]`, `u[l+1] --> v[l+1]` and `u[l+1] --> v[l]` on 300 random
  levels in both implementations, against a model that compares levels by
  their value for every value of their variables: `l+1` is refused exactly
  when a variable has offset 0, and otherwise the level comes back equal
  (or one below). Recorded, not endorsed: the constant level 0 matches
  `l+1` with `l = 0`, so `u[l+1] --> v[l+1]` turns 0 into 1. A mutant that
  lets `l+1` take only offsets of 2 or more fails the model on 89 levels.
- The filter's term-type checks on every kind of statement
  (`test/filter_types`, #94): besides `prim_rw`, `interactive`, `dform`,
  `iform`, `production` and `declare rewrite`, each with a well-typed and an
  ill-typed fixture.
- A rewrite with an argument (`test/unit/test_rewrite_args.ml`), as rules
  such as `thin 'H` take one: `sequent[sa]{ <H>; x: 'A<|H|>; <J<|H|>> >-
  'C<|H;J|> } --> sequent[sb]{ <H>; <J<|H|>> >- 'C<|H;J|> }` with the length
  of `H` an int argument, on 200 sequents with every argument from -5 to 6
  in both implementations: it removes exactly the hypothesis the argument
  names (k > 0 the k-th; k <= 0 leaving -k after it), when nothing later
  mentions it; 2,400 of 2,400 agree with that model. An off-by-one in
  placing a positive argument fails 374.
- Level expressions and primitive strings (`test/unit/test_level_exp.ml`):
  in both implementations, a level built from `mk_const_level_exp`,
  `mk_var_level_exp`, `max_level_exp` and `incr_level_exp` has the value of
  its expression (max of a constant and variable-plus-offset terms) under
  every assignment of 0..3 to three variables, on 3,000 random expressions,
  with its variables distinct and in order; `level_le` and `level_lt` are
  sound against those values on 3,000 pairs (they compare constant with
  constant and offset with offset, so about 4 % of pairs whose values agree
  get a no, which the test counts). `mk_xstring_term` round-trips and
  `is_xstring_term`/`dest_xstring` refuse four other shapes. No defect.
  Mutants that drop an offset in `max_level_exp`, forget the variables in
  `incr_level_exp`, accept a variable missing on the right, or make
  `level_lt` non-strict each fail.
- Display forms in the `tex` and `src` modes as well as `prl`
  (`editor/ml/tests/dform_golden.sh` with `DFORM_MODE`, #95): the same 59
  itt/core goals, against `dform_golden.tex.expected` and
  `dform_golden.src.expected`.
- Operator-parameter equality and term types
  (`test/unit/test_opparam_eq_ty.ml`): in both implementations,
  `TermSubst.opparam_eq` on 4,000 pairs of operator parameters built
  separately from descriptions -- every parameter kind, nested operators,
  object ids and parameter lists, and pairs that differ in one parameter at
  any depth -- is true exactly when the descriptions are equal; `Term_ty`'s
  `eq_ty` compares name, parameters, bound terms and type and ignores the
  term, `eq` also compares the term, `term_of_ty` gives the term back, and
  `string_of_ty_param` names each kind. No defect. Mutants that ignore the
  arities, treat nested operators or token parameters as always equal, or
  drop the term from `eq` each fail.
- Three redex shapes no other test compiled (`test/unit/test_rewrite_shapes.ml`):
  a variable bound in the redex and used in it (`lam{x. 'x} --> id` rewrites
  exactly the identity, not `lam{u. 'z}`), a free first-order variable
  (`f{'x} --> g{'x}` exactly when the argument is a variable), and a context
  in two sequents of one redex (exactly when both have the same
  hypotheses); 300 terms each, both implementations, all agree with the
  model. Disabling the bound-variable check, letting the free variable
  match any term, or skipping the second context's comparison each fails
  its model.
- Term shapes, the parts `test_term_shape` leaves out
  (`test/unit/test_term_shape_quote.ml`): on 2,000 generated shapes with
  quote, shape, operator, level and variable parameters, in both
  implementations, `unquote_shape` removes exactly the leading quotes (a
  quote after another parameter stays), returns its argument itself when
  there is none, and is idempotent; `opname_of_shape` and the canonical term
  of a quoted shape hold. Variables, second-order variables and sequents
  have their special shapes, and an `ObId` or `ParamList` parameter makes
  `shape_of_term` raise `Invalid_argument`. No defect. Mutants that strip
  every quote, always copy the shape, or give a quote's canonical term a
  variable parameter each fail.
- The Windows lane runs the filter tests (`test/filter_types`,
  `test/filter_prla_id`, #96) and the display-form goldens in all three modes
  (#98), which ran on Linux only. The filter runners now hand the native
  filter `cygpath -m` paths and join `MP_INCLUDE` with `;` under Cygwin
  (before, every case failed there); the goldens print byte-identically on
  Windows and Linux.

### Known not to work

- `Term_order.compare_params` on every kind of parameter
  (`test/unit/test_term_order_params.ml`), levels and operator parameters
  included: on 400 generated parameters it is a total order (0 exactly when
  two parameters are the same, antisymmetric, transitive on 20,000 triples)
  that puts the kinds in the order of its match. Mutants that ignore a
  level's variables, a level variable's offset, or an operator parameter's
  arities each break "0 exactly when the same".
- JProver's intuitionistic search (LJ, LJmc) does not finish in 10 s on 17
  of the 400 test formulas, all non-theorems, although the multiplicity is
  capped at 3. On `~~((r => r) => r)` the time goes to prefix (string)
  unification: the first 100,000 search steps average about 40 us, and once
  the search path reaches 8 atoms the unifications sampled took 30-230 ms
  each. Changing the search to avoid this is not
  attempted here.

## 1.0.0 (2026-10-29): the 2026 refresh

MetaPRL's first tagged release. It had not been built since 2017. These
changes make it build and run on a current OCaml again, without changing what
the theories say.

**What tests this release.** The proof census (`editor/ml/tests/proof_census.sh`,
below) is its test: on every push it builds every theory in `THEORIES_ALL`
and replays every stored proof (264 modules, 5,191 rule statuses) against
libmojave's master, on OCaml 4.14.4 and 5.4.1, and the Windows workflow does
the same with MinGW. There are no unit tests of the refiner or of `mllib` yet;
they are planned after libmojave's test coverage. The gaps are listed under
"Known not to work" below.

### Building

- Builds on OCaml 4.14.4 and 5.4.1 with camlp5 8.05.02 and OMake 0.10.7, with
  libmojave checked out beside the tree (#6–#8, #11–#13, #17–#19, #27).
  - `mk/defaults`' `CAML_VERSIONS` names exactly those two versions; the check
    is an exact match.
  - Warnings that newer compilers added are numbered in the flags, and
    warning 68 (raised by OCaml 4.14 only) is not an error (#7, #27).
- The OCaml-syntax filter is ported from camlp5 7 to camlp5 8 (#10, #11). A pin
  in `filter/test/` (#9) records the terms the camlp5 7 filter produced for
  320 items; the camlp5 8 filter produces the same term structure.
- `mp`, the MetaPRL shell, builds and runs (#18). It reads a one-argument minus
  as negation, as OCaml does (`editor/ml/tests/toploop_minus.sh`).
- `infix.ml` is generated by the build, not tracked (#21), and declared as
  generated, so a parallel build no longer races on it (#26).
- The files a build generates are ignored (#20, #24, #38).
- `omake install` works again (#38). It installs what the configuration
  builds; the `mprun` variant, which is not ported, is installed only when
  `MPRUN_ENABLED` is set. An `INSTALL_DIR` containing a space is quoted in the
  install rule (#38) and stays one `THEORYPATH` entry (#33).
- Windows with MinGW (#34, #41): the default configuration builds on both
  OCaml versions with ocaml-omake's master branch (OMake 0.10.7 does not build
  there), measured by a manual workflow, `.github/workflows/windows.yml`, that
  does not run on pushes. After the build it runs the two shell tests
  (`toploop_minus.sh`, `old_labels.sh`) through the Windows launcher
  `editor/ml/mp.bat`, and both pass on both OCaml versions (#43). With its
  `census` input it builds every theory and runs the proof census, which
  matches `proof_census.expected` on both versions: 264 modules, 5,191 rule
  statuses (#44). The same holds for a native-code build (its `native` input:
  `mp.bat` then runs `mp.opt`) (#46). On Windows OMake's `shell-code` does not drain a child's output
  while the child runs, so a command run through MetaPRL's `prlcomp` alias hung
  once it wrote about 4 KB, and the build stopped at the first theory files.
  There the preprocessor steps now run as plain rule commands, with the
  alias's environment variables set for each directory (#41). `mk/defaults`
  adds `/MT` only for MSVC, and `macropp` is linked with `mkcamlp5 -opt` (#34).
- `clib/locale.c` is no longer built (#36). libmojave 1.0.0 defines the same
  six C primitives for `Lm_ctype`, and linking both gave duplicate symbols.

### Fixed

- A theory's refiner was named after its file rather than its module, so
  every rule lookup failed and `check_all` printed nothing (#22).
- Thirteen rules loaded with no proof: their 2006 archives store a `~labels:`
  annotation in a form the decoder had not read since 2005 (#23). All 13 now
  replay complete.
- The decoder for `?x` optional-argument patterns in old archives was
  commented out; it is restored (#28).
- Stored ML items in some old archives use a three-subterm `with`-constraint
  form that the decoder rejected with a warning; it now reads them (#31).
- The spelling filter wrote its dictionary through a second channel to the
  same file, so the rename that replaces the dictionary failed on Windows
  (#35).
- `MP_INCLUDE` is split on the platform's path-list separator, `;` on
  Windows, where splitting on `:` broke paths such as `d:\...` (#37).

### Tests

- `editor/ml/tests/old_labels.sh` (#23) and `toploop_minus.sh` (#18).
- `editor/ml/tests/proof_census.sh` (#29) replays every stored proof, one
  module per `mp` process, and compares each rule's status and rule-box count
  with `proof_census.expected`. It checks status, not the proofs' content. It
  fails on an empty expected file or a run with no statuses (#31).
- `editor/ml/tests/install_space.sh` (#38) installs to a directory whose name
  contains a space.
- CI (#25, #29) builds the default configuration on both OCaml versions and
  runs the tests above, and in a second job builds every theory in
  `THEORIES_ALL` and runs the proof census. Both jobs run on OCaml 4.14.4 and
  5.4.1 (#32); the census (264 modules, 5,191 rule statuses) is the same on both.

### Known not to work

- 37 stored proofs replay unfinished. Most were already unfinished in the
  archive when it was saved. For the others the saved proof was complete and a
  step now fails; whether that began before or after 2017 is not known.
- The theories outside `THEORIES_ALL` (mesa, kat, ilc, lf, hol,
  experimental/unity, experimental/mcc) were not in the 2017 build either and
  are not built now. hol compiles; the others do not, and their sources are
  unchanged since 2006.
- Windows with MSVC does not build: OMake does not build on OCaml 5.4.1 (MSVC
  rejects the OCaml headers' C11 atomics), and on 4.14.4 camlp5 does not
  install.
- Two theories written in 2017 were never committed to this repository and
  are not part of this release; their toolchain (OCaml 4.05 with a camlp5
  that opam never packaged) could not be rebuilt.
- A build reads a module's proofs from the newest of its `.prla`, `.prlb` and
  `.cmoz` files, and the build itself writes `.prlb` and `.cmoz`. In a tree
  that was built before a change to the filter, those files shadow the `.prla`
  until they are removed.

### Repository

- Commit, branch-name and pull-request checks run on every push (#5).
