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

- Two of `itt_int_ext`'s remainder rules were false as stated, so they
  could never be proved. `rem_neg` said `a %@ b ~ (-a) %@ (-b)`; at a = 7,
  b = 2 the literal reductions give 1 and -1 (the remainder takes the
  dividend's sign). It now says `a %@ b ~ a %@ (-b)`, which its rewrite
  `rem_neg_rw` already said. `rem_indReduce` and `rem_indReduce_rw` said
  `((a * b) + c) %@ b ~ c %@ b` for any b <> 0; at a = 1, b = 2, c = -1 they
  give 1 and -1. They now carry `div_indReduce`'s conditions, a >= 0, b > 0
  and c >= 0. Both rules were unproved and no stored proof uses them, so no
  proof's status changes. The false forms date from the 2006 change that gave
  div and rem explicit definitions; the earlier axiom `rem_neg` had the
  right form.

- `itt_int_ext` could prove False (#144): the definition of `div` recursed
  as `else div (a - b) b`, dropping the `1 +@`, so unfolding gave
  `7 /@ 2 ~ 0` where the primitive literal rewrite gives 3. `rem`, defined
  from `div`, inherited it. The definition now adds the 1; `div_neg` is
  re-proved with a new lemma `ge_zero_both`. Test:
  `editor/ml/tests/int_div_def.sh` (unfolds both definitions on literals,
  never through `byDefT`; all six cases fail on the old definition).
- The ITT core could prove `void` (#145):
  `itt_inv_typing.independentProductTypeElimination` inferred `type{B}`
  from `type{A * B}`, which is false when `A` is empty (`type{void * B}`
  holds for every `B`); a 42-step derivation reached `void`. The rule now
  adds `w: (A -> type{B})`, the form `functionTypeElimination` uses.
  `itt_record0.recordTypeElimination`, the one stored proof that depended
  on the old form, is re-proved. Test: `editor/ml/tests/inv_typing_sound.sh`
  (the derivation must not close; its true first step must).
- Every division and remainder rule of `itt_int_ext` is now proved (#244):
  `div_wf`, `rem_wf`, `div_remProperty`, `rem_baseReduce`, `div_indReduce`,
  `rem_neg`, `rem_neg_rw`, `rem_indReduce`, `lt_divMono`, `add_divReduce`
  and `div_Assoc`, on the corrected `div`, so no rule in the module is
  unproved.
- `Proof_boot.make_assum` added each node's own conclusion as an assumption
  instead of the chosen goal's, because a local binding shadowed the
  parameter (#156; pinned by #155). Its one caller is the proof editor's
  `make_assum` command.
- `rewrite_of_parsed_rewrite` parsed the contractum before the redex (an
  OCaml tuple is evaluated right to left), so a second-order variable's
  default contexts came from the contractum (#181; pinned by #179). Three
  theories' rewrites now parse with the context they name (`cic_ind_type`,
  `itt_vec_dform`, `s4_logic`); no proof status changes.
- `expand` of an unchanged proof could move a sub-proof to another subgoal:
  a leaf's fuzzy match could take the sub-proof made for a later leaf that
  matched it exactly (26 of 300 random proofs). Every leaf now gets its
  exact match first (#183; pinned by #182).
- `Rewrite_compile_redex` looked a free-variable context's restriction up
  by its address index instead of its stack index, so under a binder
  `Not_found` escaped `compile_redices`, or the context silently got another
  variable's restriction (#199; pinned by #198).
- `Unify_mm` raised on a sequent at the top level under `TERMS = ds` (the
  default), and its sequent view built generic terms that std and ds read
  differently; it now has a private sequent symbol (#162).
- `type_subst` on a nested existential type rebuilt it with the substituted
  variable's name, leaving the inner variable free, so
  `exst a: Ty. exst b: Ty. Pair{'a; 'b}` was accepted where
  `exst a: Ty. Pair{'a; 'a}` is required (#231). Latent in the theories (no
  theory build reaches the arm).
- `Proof.post`: reading the cache after the posted address disappeared
  raised `RefineError "Proof_boot.index"` instead of giving the old node
  (#232). No shell path to it was found.
- `Ascii_io` renamed a duplicate named by a Token, Shape or Operator
  parameter and then wrote the old name, so saving such a (hand-edited)
  file raised (#214; pinned by #213).
- `Opname.dst_opname` on an un-normalized marshalled copy returned a
  remainder that `eq` judged different from the shared opname (#251). No
  caller is affected today.
- `File_type_base`'s `check` left the channel open on every save over an
  existing file; on Windows the handle stopped the file from being removed
  (#246). `Setup.editor` left `~/.metaprl/editor` open when the file is
  empty (#250).
- `Proof.info` described `nthAssumT i` as `nthAssumT (i - 1)` (#230), and a
  rewrite at an assumption i > 0 like the same rewrite at the goal (#236).
  Display only.
- `Proof_boot.replace_child` had an unreachable arm with an off-by-one
  index; it now refuses like `select_child` (#233).
- `lambdaSqSubstT` (itt_struct2) found its subterm with a stateful
  predicate, which gave a different answer on a second run (#161). The
  default build gets the same address and argument as before.
- The `TERMS = both` differential checker (`Refiner_debug`, which runs
  every refiner call on term_std and term_ds and reports any disagreement)
  did not build on master and, once built, lost 1,149 of 5,191 proof
  statuses to its own defects: polymorphic comparison of caller-supplied
  results, exceptions of the wrong module (#160), binder names std and ds
  may legitimately choose differently (#163, #164, #167, #168), and
  callbacks run once per implementation (#165, #166; the cause of four
  modules growing past 8 GB). With these and #161 / #162 the `TERMS = both`
  census replays 264 of 264 modules with no disagreement. The default build
  does not use `Refiner_debug`.
- `Free_vars.free_vars` (filter/base) did not examine a let's body (the
  last right-hand side was examined in its place, so `let x = a in b` gave
  `[a]`) or a case's `when` guard, and did not bind a `let rec`'s names in
  its right-hand sides; so `new_vars` could return a name free in the
  expression. Pinned by #261 (`test_free_vars`: on 2,000 random expressions
  it disagreed with OCaml's scoping on 529, now on 0). Nothing in metaprl
  calls it except the camlp5 parity pin, whose `fv=` fields change on 70 of
  328 items (`filter/test/README.md`).
- A module summary's term form (`FilterSummaryTerm.term_list` /
  `of_term_list`, used by the term file system and the library) could not
  read back a dform with the `DFormInheritPrec` option: it was written as a
  `prec_df` with no parameter, which the reader refused. It is now written
  as `inherit_df`, which the reader already accepted. `Modes` and
  `ExceptModes` also came back in reverse order; they now keep it (#265;
  pinned by #264).
- The generic term syntax (`base_grammar`'s `xterm_param`) could not give
  a level successor: `Term_grammar` defined `xparam_succ_opname` as
  `"xparam_string"`, so the `xparam_succ{p}` term built for `p'` was
  refused as "not a parameter". It now gives `i'` = `max(1, i+1)` and
  so on (#267; pinned by #266). No theory writes `p'` in that syntax.
- `Filter_util.adjust_pos`, which places a location found in a quotation's
  text in the file, counted the location's end from the quotation's end
  instead of its start, so every such span ran past the quotation: a
  syntax error at the `}` of `<<foo{a; }>>` at characters 230-250 was
  reported at 239-260 instead of 239-240. It came in with the 2017 port
  from `Lexing.position` to `Ploc.t` (#271; pinned by #270).
- Three `Filter_exn` messages: `Bad command:` had no space before the
  command, `Bad_magic` said "that is is either", and `Bad_version` put a
  `, ` after the last supported version (#273; pinned by #272).
- `Filter_buffer.putc` and `puts` grew the buffer and then wrote into the
  old bytes, so any write past the first 32 bytes raised
  `Invalid_argument`. Nothing in the tree uses the module (#275; pinned
  by #274).
- `Filter_ocaml`'s way back from terms to OCaml syntax
  (`str_item_of_term`, `sig_item_of_term`) failed on much common syntax,
  because decoders did not read what their encoders write. In every case
  the decoder now reads the encoder's terms. No encoder changed, so a
  term already written reads back the same. The camlp5 parity pin's 320
  items went from 278 round trips to all 320. Each fix is pinned by
  `test_filter_ocaml` items first:
  - every variant type and every type parameter (#280; the 2017 OCaml
    4.05 port, d34a0b0f2, changed the encoders only);
  - every `external`, in a structure or a signature (#281);
  - object expressions, class and class-type declarations, and class
    infos (#282);
  - a labelled parameter: turning one into a term recursed until the
    stack overflowed (`mk_patt_lab`'s loop matched the outer list), and
    its decoder built a record pattern (#283);
  - `let ... and ... in`, which raised on the `patt_and` between bindings
    (#284);
  - `new`, `{< ... >}` and a class's `let` (#285);
  - `let rec ... and ...`, which came back with its bindings in reverse
    order: the encoder has written them reversed since 1998 and neither
    decoder reversed them back (#286);
  - variant patterns (`` `A ``, `` `B x ``) and object types (#287);
  - an unpacked module, `(val e : S)` and `(val e)` (#290).
- `Free_vars.free_vars` and `patt_vars` raised on `{ e with ... }`,
  labelled arguments, `lazy`, `assert`, `let open`, int32 / int64 /
  nativeint literals, objects, variant patterns, first-class module
  patterns and array patterns; they now give the free variables OCaml
  gives (#288; pinned by `test_free_vars_syntax`). An object binds its
  self pattern and instance variables in its methods and initializers
  only.

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
- The rest of `TermSubst` (`test/unit/test_term_subst_rest.ml`): on 1,500
  terms in both implementations, each against an oracle that does not use
  it -- `alpha_equal_vars` is `alpha_equal` under a binder,
  `alpha_equal_fun` is `alpha_equal` to the substitution,
  `dest_bterm_and_rename` avoids the given variables and keeps the bound
  term, `free_vars_terms` is the union, `is_some_var_free_list` is the
  exists, and `equal_operators`/`equal_params` agree with `alpha_equal`. No
  defect. Five mutants of term_ds's own code, each rebuilt, fail on the line
  they change.
- Rules whose contractum carries parameters (`test/unit/test_rewrite_params.ml`):
  five rules that move a number, a string and a token parameter, swap two,
  add constant parameters and require a repeated parameter variable to
  match equal numbers, each applied to 300 instances and 300 near misses in
  both implementations and compared with a model; all agree, and a
  contractum parameter the redex does not bind does not compile. A mutant
  that reverses the contractum's parameters fails the two rules with
  several (0 of 300).
- Term projections, simple terms and the rest of `Term_addr`
  (`test/unit/test_term_base_addr.ml`): in both implementations, on 1,500
  terms, `opname_of_term`/`subterms_of_term`/`subterm_arities` match the
  description; at every listed address `apply_fun_arg_at_addr` and
  `apply_var_fun_arg_at_addr` agree with their plain forms and with
  `term_subterm` (term_ds builds the plain form from the `_arg` one, so the
  `term_subterm` check is the one that does not share its code);
  `split_clause_address` splits clause addresses on sequents and refuses
  others; and the simple-term constructors and destructors round-trip and
  refuse parameters and binders. No defect. Five rebuilt mutants of
  term_ds's own code each fail.
- `Term_stable`, the table keyed by a term's shape behind itt_squash's
  unsquash resource (`test/unit/test_term_stable.ml`): 300 generated terms
  inserted and 1,000 looked up, one in five of a shape never inserted;
  `slookup_all` returns the values whose shape matches, newest first, and
  `slookup` the newest or `Not_found`, against a model that computes the
  shape from the term's structure, on all 1,000. Mutants: inserting with
  `Hashtbl.replace` (212), counting no binders (790), giving a Token
  parameter the Number kind (983). Recorded: a variable and a
  second-order variable with no arguments have the same shape.
- The `TermOp` constructors (`test/unit/test_term_op_shapes.ml`): in both
  implementations, for 40 `mk_` constructors, `dest_` (and `dest_..._any`)
  gives the components back, `is_` holds under its own name, and both
  refuse another name; across the table, `is_X` on the term `mk_Y` built
  holds exactly when the two have the same shape (1,482 pairs), except
  that `is_token_simple_term` accepts any number of binder-free subterms.
  No defect. Four rebuilt mutants of term_ds's `term_op_ds.ml` each fail.
- Three more rules check the matcher against a model as well as across
  the implementations: a second-order variable that occurs twice as a
  pattern (rewrites exactly when the two bodies are the same up to the
  binder), a second occurrence that is an instance (`'b[c]`: exactly when it
  is the first body with `c` for its variable), and a conclusion restricted
  to no context (`'C<||>`: exactly when no variable of `<J>` occurs); all
  400 of 400. Disabling `check_simple_match`, `check_match` or
  `check_var_restrictions` each fails its own model.
- The rest of `Term_meta` (`test/unit/test_term_meta_rest.ml`): on 600
  generated meta terms and 300 rewrites, in both implementations, each
  against a model on the description -- `is_meta_term`, `iter_mterm` (in
  order), `map_mterm`, `all_vars_mterm`, `strip_mfunction` (with its two
  refusals), `unzip_mrewrite`, and `zip_mlabeled` with `unfold_mlabeled`.
  No defect. Five rebuilt mutants of `term_meta_gen.ml` each fail.
- How the shell resolves paths (`editor/ml/tests/dir_of_path_precedence.sh`,
  #92): an absolute path whose first part names a theory is the theory, even
  when a module has the same name (`/itt_supinf/<rule>` asks for a module
  named `<rule>`); `..`, `...`, `~` and `.` from a proof or a module; and, as
  it is, a module reached under another theory's name (`../itt_supinf` from
  `itt_int_base`) — the theory part is not checked against the module.
- `Ml_term`, the string form in which the filter stores a theory's terms,
  and `Lib_term`'s sequent encoding (`test/unit/test_ml_term.ml`): on 300
  batches of terms, meta terms, opnames and numbers (big integers among
  them), `term_arrays_of_string (string_of_term_lists ...)` gives every list
  back in order; a string without the header is refused; and a sequent
  survives `ugly_term_of_sequent_term` and back, as every term survives
  `Lib_term.dest_term` and `make_term`. No defect. Four rebuilt mutants of
  `ml_term.ml` and `lib_term.ml` each fail.
- What the shell's `ls` options select (`editor/ml/tests/ls_options.sh`):
  on `itt_int_base`, `r` lists only rewrites and definitions, `R` only rules,
  `rR` both, `u` exactly the rewrites and rules not yet proved, `p` the
  `Extends` lines, `d` display forms, `D` documentation, `f` no informal
  items, `a` everything `f` and `i` list; an unknown option is an error and
  the shell goes on. Checked by the kind of each entry, not by counts.
- `Unify_mm`'s equation lists (`test/unit/test_unify_eqnl.ml`): against
  `test_unify_mm`'s Robinson unifier, on 1,500 systems of one to three
  equations with and without a constant, the list builders match a list
  model, `unifiable_eqnl` agrees, `unify_eqnl` raises exactly when there is
  no unifier and otherwise returns a most general one, `unify_eqnl_eqnl`'s
  solved form unifies every equation, and `new_eqns_var` is fresh. No
  defect. Five rebuilt mutants of `unify_mm.ml` each fail.
- The proof census ends a module's rows at the next module (#93): a module
  named like its theory is entered through the theory, whose `status_all`
  replays every module in it, and `itt_rfun`'s rows had also carried
  `itt_well_founded_equiv`'s `well_founded_reduction`.
- The primitive term vocabulary (`test/unit/test_xterms.ml`): in both
  implementations, list terms built by `mk_xlist_term` and by
  `xcons`/`xnil` agree and `dest_xlist` gives the terms back (500 random
  lists); a cons with a non-list tail or a bound variable, and `xnil` with a
  parameter, are refused; `xrewrite`, `xbind` and the string with one
  subterm round-trip and refuse other shapes; `is_fso_var_term` holds for a
  variable and a second-order variable with contexts but no arguments; and
  `construct_redex` is the binders in order around `params @ terms`. No
  defect. Mutants that drop the tail check, swap `params` and `terms`, or
  reverse the binders each fail.
- Rules over universe levels (`test/unit/test_rewrite_levels.ml`):
  `u[l] --> v[l]`, `u[l+1] --> v[l+1]` and `u[l+1] --> v[l]` on 300 random
  levels in both implementations, against a model that compares levels by
  their value for every value of their variables: `l+1` is refused exactly
  when a variable has offset 0, and otherwise the level comes back equal
  (or one below). Recorded, not endorsed: the constant level 0 matches
  `l+1` with `l = 0`, so `u[l+1] --> v[l+1]` turns 0 into 1. A mutant that
  lets `l+1` take only offsets of 2 or more fails the model on 89 levels.
- The msequent accessors of `Refine` (`test/unit/test_msequent.ml`): on
  1,000 msequents in both implementations, `msequent_num_assums`,
  `msequent_all_assums` and `msequent_nth_assum` (counting from 1; 0 and
  one past the end refused), `mk_msequent`/`dest_msequent`/`msequent_goal`,
  and `msequent_alpha_equal` against a rebuilt copy and three kinds of
  difference. No defect. Four rebuilt mutants of `refine.ml` each fail.
- The filter's term-type checks on every kind of statement
  (`test/filter_types`, #94): besides `prim_rw`, `interactive`, `dform`,
  `iform`, `production` and `declare rewrite`, each with a well-typed and an
  ill-typed fixture.
- Variable info (`test/unit/test_vars_info.ml`): on 1,500 terms with
  sequents, contexts, second-order variables, binders and parameters, and
  1,500 lists of them, `param_vars_info` is the set of meta-variables the
  parameters name (inside parameter lists, not inside operator
  parameters), `so_vars_info` and `context_vars_info` name exactly the
  second-order variables and context hypotheses, each `_list` form is the
  fold of its single form, `all_vars_terms` is the union of `all_vars`, and
  term_std and term_ds agree on all of it. No defect. Mutants that look
  inside operator parameters, skip parameter lists, read only the first
  term of a list, or mark a sequent context as plain each fail.
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
- Tests added 2026-11-03 to 2026-11-12, one line per pull request; each
  description gives the cases, what is pinned, and the mutants run against
  the real source:
  - Options_boot's option table against a model (#146).
  - The conversion combinators of Conversionals_boot against a model (#147).
  - Sequent_boot's goal accessors against a list model (#148).
  - Tacticals_boot combinators against a model (#149).
  - Tacticals_boot clause tacticals against a model (#150).
  - Rewrite_boot's rw tactic against a model (#151).
  - Exn_boot.format_exn's Unix and fall-through forms (#152).
  - Proof_convert and the proof io round trips (#153).
  - Proof_boot's tree accessors against a model (#154).
  - Proof_boot's editing operations against a model (#155).
  - Pin refine.ml rules (create_rule, prim_rule, sentinels) against a model
    (#157).
  - Pin refine.ml conditional rewrites against a model (#158).
  - Pin refine.ml extracts (derived/delayed rules, extract_term,
    compute_dependencies) (#159).
  - A weekly TERMS = both proof census that fails on any std/ds disagreement
    (#169).
  - Pin Term_ty_infer (inference and the six check_* functions) (#170).
  - Pin Dform (mode selection, precedence and parentheses, slots) (#171).
  - JProver on first-order formulas, and its LJ proof reconstruction (#172).
  - Pin Rewrite_match_redex's parameter, meta-parameter and Strict-context
    branches (#173).
  - SupInf's min/max forms (MakeSAF) against a pointwise model (#174).
  - Pin Rewrite_compile_redex's instance, address-context and
    argument-restriction branches (#175).
  - Pin Rewrite_build_contractum (parameters, binder renaming, context fill,
    hypothesis substitution) (#176).
  - Pin Rewrite_compile_contractum's remaining census-only branches (#177).
  - Pin the remaining Tacticals_boot tacticals (label filters, sequencing,
    assumptions, arguments) (#178).
  - Pin Term_meta_gen's parser-side conversions (pins a rewrite-parsing
    order defect) (#179).
  - Pin the clause and assumption rewrite tactics of Conversionals_boot
    (#180).
  - Pin Proof.expand and Proof.kreitz (expand moves sub-proofs between
    subgoals) (#182).
  - Pin Tactic_boot's attribute and option tacticals (#184).
  - Term_ds against term_std on context terms and sequents (#185).
  - `test_refine_build`: how the refiner is built and checked (#186).
  - Tests for Refine_exn's error printer and conditional rewrites in
    Rewrite_boot (#187).
  - `test_tactic_sentinels`: theory sentinels and rule tactics in
    Tactic_boot (#188).
  - `test_refine_derived_rw`: derived and delayed rewrites in the refiner
    (#189).
  - `test_term_ty_infer_seq`: Term_ty_infer on sequents, contexts and
    meta-parameters (#190).
  - `test_proof_composite`: Proof on refinements by composite tactics
    (#191).
  - `test_rewrite_seq_redex`: contexts with arguments in two sequents of a
    redex (#192).
  - `test_dform_prims`: Dform's formatting primitives (#193).
  - `test_rewrite_opparam`: operator parameters in the rewriter (#194).
  - JProver in S4, and its LJ rule permutations (#195).
  - Jtunify's S4 prefix unification, unifiers checked (#196).
  - SupInf's Tree, infinities, term_of and sources (#197).
  - Rewrite_compile_redex's argument restrictions, as compiled (#198).
  - Term_subst_ds against term_std on binder renaming and contexts (#200).
  - Mp_resource's imperative processors, improve_list and the top resource
    (#201).
  - Match_seq.match_some_hyps against a model; two behaviours pinned (#202).
  - Unify_mm with second-order variables, mixed symbols and constants
    (#203).
  - Term_base_ds against term_std on pending substitutions and contexts
    (#204).
  - Term copying across implementations, levels and meta-terms (#205).
  - Term_man_ds against term_std on parameter kinds (#206).
  - Term_match_table's resource adapters, sequent patterns and buckets
    (#207).
  - File_base, the multi-format store of a theory's compiled files (#208).
  - Term_addr_ds against term_std on contexts, SO variables and bad
    addresses (#209).
  - Rewrite's parameter items and Rewrite_util's maybe-patterns (#210).
  - A matched context re-instantiated with other arguments in a contractum
    (#211).
  - WhileProgressMT, onSomeHypT, thinning and int arguments, options (#212).
  - Ascii_io's parameter kinds, old-format readers and save path (#213).
  - Proof_term_boot's attribute and node kinds, and hand-edited proof terms
    (#215).
  - The refiner's extracts and dependencies through rewrite steps (#216).
  - Refine_exn on every refine_error constructor and exception kind (#217).
  - Tactic_boot's arglist compression, printers and attribute removal
    (#218).
  - Proof_boot's editor operations on attribute and composite nodes (#219).
  - Proof_boot's editor operations below the root (#220).
  - The refiner's extracts and dependencies through conditional rewrites
    (#221).
  - Refiner extracts of sequents with hypotheses (upd_term) (#222).
  - Term_ty_infer on polymorphic declarations (#223).
  - Term_ty_infer on sequent types as values and existential hypotheses
    (#224).
  - Proof_boot editing operations on nested and reloaded proofs (#225).
  - Term_ty_infer on quoted terms and non-term types as values (#226).
  - Proof.info at a step's extract (make_extract_expr) (#227).
  - Term_ty_infer unify_equal_params on Quote, level, shape and Nuprl5
    params (#228).
  - Proof edit operations at a step's extract address (#229).
  - Proof_boot edits at the extract of a composed or annotated step (#234).
  - Proof_boot's save path on edited and posted proofs (#235).
  - A conditional rewrite refuses a condition with a bound variable (#237).
  - Terms declared with a level or an operator parameter (#238).
  - Rewrite matching, instances before patterns and argument restrictions
    (#239).
  - Term_meta_gen conversions the census reaches (#240).
  - Term_ds arms the census reaches (#241).
  - Term_dtable's right-to-left entries with a ground right side (#242).
  - Expand after the goal has changed, and initialize_goal (#245).
  - The archive format's magic and version checks; fix a leaked channel in
    check (#246).
  - File_base picks the newest of several specs of one format (#247).
  - Conditional rewrite refusals, no match and a renamed inner binder
    (#248).
  - Find_sentinal of a rule defined before its refiner joined another
    (#249).
  - Opname; fix dst_opname on a marshalled copy (#251).
  - Dform's built-in commands (breaks, zones, pushm, fonts) (#252).
  - Term_ty_infer on operator and level parameters (#253).
  - Reach term_base_ds's filter_sub_vars; correct #204's header claim
    (#254).
  - Term_subst_ds remove_var below the head; is_some_var_free (#255).
  - Rule_labels_of_opt_terms; get_pos_assum_num (#256).
  - Is_no_subterms_term and one_subterm refusals, std against ds (#257).
  - Jall's prover entry point (LJ, one conclusion) (#258).
  - Opname.eq with the marshalled copy second (#259).
  - `test_free_vars`: Free_vars against a model; the first unit test of
    `filter/`, which `run.sh` links for a test whose first line is
    `(* unit-link: filter *)` (#261).
  - The camlp5 parity pin of `Filter_ocaml` and `Free_vars` (`filter/test`,
    328 items over 8 files) runs in CI after the unit tests; it was run by
    hand only. Most of `filter_ocaml.ml` is reached by no theory build.
  - `test_filter_summary_term`: a module summary's term form round trip,
    one item of every summary item kind (#264). No theory build or
    proof census reaches the term form.
  - `test_term_grammar_params`: `Term_grammar`'s `[value:kind]` casts in
    quotation text and `dest_xparam` on `base_grammar`'s terms (#266);
    `run.sh` gives a test linked with the filter `-I filter/filter` and
    `MP_ROOT` / `MPLIB`.
  - `test_filter_spell`: `Filter_spell`'s dictionary, each case in a child
    process with its own `MPLIB`: a first build, a load of an up-to-date
    `.dat`, a rebuild when a words file is newer, when the magic is wrong
    and when the table is unreadable, and no words files; `check`'s
    capitalised, numeric and one-letter words, and `add` (#269).
  - `test_filter_util`: `Filter_util`'s locations (`adjust_pos` on a first
    and a later line), `grammar_parse`'s restore of Plexing's counters,
    `unzip_rewrite`, and opname and module-path printing (#270); a syntax
    error inside a quotation, in `test_term_grammar_params` (#271).
  - `test_filter_exn`: `Filter_exn.format_exn` on every exception it
    names, and `print_exn`, `stderr_exn` and `handle_exn` (which exits 2)
    in child processes, with and without `OCAMLRUNPARAM=b` (#272).
  - `test_filter_buffer` and `test_filter_shape`: `Filter_buffer` below and
    past its first 32 bytes; the shape classes' predicates, num form and
    printing (#274).
  - `test_filter_summary_check`: `check_implementation` on every interface
    item it checks, each implemented, missing and differing, and the items
    an interface passes on (#276).
  - `run.sh`: a filter-linked test whose second line is
    `(* unit-native: <objects> *)` is linked natively with those objects
    (camlp5's parser and printer exist only as native objects); it is
    SKIPPED, with a line naming what is missing, in a build without them,
    as on the Windows runners (#278). `test_filter_patt`:
    `Filter_patt.build_term_patt` (#278).
  - `test_filter_ocaml`: OCaml syntax parsed by camlp5's `pa_o`, to terms
    and back, printed by `pr_o` (#279); 72 items after #280-#287, all
    reading back the same.
  - `test_free_vars_syntax`: `Free_vars` on syntax parsed by `pa_o`
    (#288).

### Known not to work

- Nested modules: `Filter_summary_io.sub_info` looks a submodule up with
  the full path from the file's root (`path @ [name]`) but on the current
  module's own summary, so it searches for the file's own name first and
  fails; `Filter_summary.find_sub_module` also prints a "checking" line
  to stderr for every module it compares. Both are under
  `filter_cache_fun`'s "BUG ... if we want nested modules", and no theory
  has a nested module.
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
- `foldC` at an assumption i > 0 rewrites the goal: it is a cut closed with
  `nthAssumT` against the goal, so it is refused unless the goal equals the
  unfolded assumption, and when it succeeds the goal is folded and the
  assumption is left as it was (pinned by #151, `test_rewrite_boot`).
- `Rewrite_compile_redex`: an argument restricted to `H` is not refused when
  it mentions a variable bound in `J`; the goal's clashing hypothesis is
  renamed instead (pinned by #175).
- `expand` on a sequent goal attaches the `nthAssumT 1` step made for the
  goal with itself assumed to the goal with no assumption, and leaves the
  other an open leaf (pinned by #245; possibly a defect).
- `Term_dtable` keys a right-to-left entry by its right side only, so
  `a <= w{b}` is answered with the derivation of `b <= w{b}` (pinned by
  #242).
- `File_type_base.pack_version` refuses a minor or revision of 255,
  although 255 fits the byte `unpack_version` reads (pinned by #246).
- `Filter_cache.AsciiIO.read_table` leaves its channel open when the table
  read raises (found by #250's census; `filter/base` is not linked by the
  unit harness, so it has no test yet).
- A module summary's term form writes a dform's `PrimitiveModes` as no
  modes, so it reads back as `AllModes`; keeping it needs a term of its
  own (a format change). Pinned by `test_filter_summary_term` (#264).
- `Free_vars.free_vars` raises on a packed module expression
  (`(module struct ... end : S)`) and on an object with `inherit`; it
  counts the `f` of `M.f` as a variable, as the old `ExAcc` case did
  (#288; one corpus item of the parity pin).
- `Filter_ocaml` has no term for some of the OCaml it reads, so the way
  back loses them: a type abbreviation's `private`, `open!`'s flag,
  attributes on an item (`[@@inline]`), and an int literal's base
  (`0x1F` reads back as `31`). `M.(e)` is written as camlp5 7 parsed it,
  an array subscript, and reads back as one (it prints the same). It
  refuses, on the way in, `type t += ...`, an attribute on an
  expression, an exception case in a `match`, and a locally abstract
  type (`let g : type a. ...`, refused on purpose). Keeping any of these
  needs a new term, which is a format change. Pinned by
  `test_filter_ocaml` (#290).

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
