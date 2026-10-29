# Changes

## Unreleased

### Tests

- Unit tests for MetaPRL's OCaml libraries (`test/unit/`, #51): each
  `test/unit/test_*.ml` is built against the built libmojave and `mllib`,
  run, and compared with its `.expected` file by `test/unit/run.sh`, a CI
  step after the build, on Linux and Windows. The first, `test_bitset.ml`, checks `mllib`'s
  `Bitset` against a bool array (100,000 reads, none differ). `refiner/`
  and `mllib/` had no unit tests; the proof census tests them end to end.
- `mllib`'s `Sort`, `List_neq_append`, `Flist` and `Permutations` are
  checked against plain OCaml (`test/unit/test_mllib_models.ml`, #52), as
  their interfaces state them. No defect. `List_neq_append.to_list`
  returns the elements in reverse order of insertion (no order is
  documented; the test records it).
- `mllib`'s `Latin1_case` (all 256 characters against ISO 8859-1, and its
  string functions) and `Precedence` (`get_prec` against the closure of
  `add_lt` and `add_eq`) are checked (`test/unit/test_mllib_models2.ml`,
  #53). No defect. `mllib/simplehashtbl.ml` is not built (it is not in
  mllib's `FILES`) and nothing uses it.
- `mllib`'s `Memo`, `Weak_memo` and `Line_buffer` are checked
  (`test/unit/test_mllib_models3.ml`, #54): memo tables against the
  function they memoize, the weak table across forced major collections
  (which drive its slot reuse; a hash table that kept a reused slot's old
  entry reads 1,515 of 6,000 wrong), and the bounded buffer and table
  against lists. No defect. `LineTable` evicts by `Unix.gettimeofday`, and
  entries added in the same clock tick are ordered by key, so on a coarse
  clock (Windows) a newly added key that sorts first can be the one
  evicted; the test adds keys in increasing order and records this.
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
  and the terms `TermOp.iter_down` visits. All agree. On the code before
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
