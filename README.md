# MetaPRL

**MetaPRL** is a logical framework and tactic-based proof assistant developed
from 1997–2017, begun at Cornell as "Nuprl-Light" (a reimplementation of the
Nuprl proof system) and carried forward at Caltech by Jason Hickey and
collaborators. It implements Nuprl-style constructive/intuitionistic type
theory (ITT) and hosts a remarkable range of related formal theories in one
system — Aczel's constructive set theory (CZF), the Edinburgh Logical Framework
(LF), the Calculus of Inductive Constructions (CIC), higher-order and
first-order logic, Kleene algebra with tests, justification logic, a compiler
intermediate representation (FIR), and a POPLmark-challenge development — with
theories connected by derived-rule model translations. Its defining ideas were
modular theories, computational reflection, and a tight weave of formal
statements with OCaml code.

**Status: archived in 2017; refreshed in 2026 (see below). GPL-2.0-or-later.**
Preserved as a research artifact and a record of two decades of
proof-assistant engineering. Reading the `theories/` and `refiner/` sources is
the best way in.

## The 2026 refresh: building on a current OCaml

Since October 2026 MetaPRL builds again, on OCaml 4.14.4 and 5.4.1 with
camlp5 8.05.02 and OMake 0.10.7 (all from opam). It needs
[libmojave](https://github.com/jyh/libmojave) checked out beside it:

```sh
git clone https://github.com/jyh/metaprl.git
git clone https://github.com/jyh/libmojave.git
ln -s ../libmojave metaprl/libmojave
cd metaprl
printf 'CAMLP5 = camlp5\nSSL_ENABLED = false\n' > mk/config.local
omake            # the first run writes mk/config and stops
# optional: set THEORIES = all in mk/config to build every theory
omake -j4
editor/ml/mp -cli    # the MetaPRL shell
```

CI builds this on Linux with both OCaml versions and runs the shell tests in
`editor/ml/tests/`. A second job builds every theory in `THEORIES_ALL` and
replays every stored proof, comparing each rule's status with
`editor/ml/tests/proof_census.expected`. At the last update that file records
5,191 rule statuses in 264 modules: 3,357 rules whose stored proof replays
complete, 1,265 primitive rules, 532 with no stored proof, and 37 whose stored
proof replays unfinished. It checks status, not the content of the proofs.
[`CHANGES.md`](./CHANGES.md) lists what changed and what is known not to work.

### On Windows (MinGW)

MetaPRL also builds and runs on Windows with opam's MinGW toolchain, on both
OCaml versions. The tested recipe is the manual workflow
[`.github/workflows/windows.yml`](./.github/workflows/windows.yml) (GitHub's
`windows-latest`); in outline, from opam's Cygwin shell:

```sh
opam pin add omake git+https://github.com/ocaml-omake/omake.git#master  # 0.10.7 does not build here
# camlp5 needs the Perl modules IPC::System::Simple and String::ShellQuote in
# Cygwin's perl; the workflow copies them from CPAN (sha256-pinned)
opam install ocamlfind camlp5.8.05.02 camlp-streams
# then the steps above, from `git clone` to `omake -j4`, except that the
# workflow clones libmojave into metaprl/libmojave instead of linking it
cd editor/ml && cmd /c mp.bat   # the MetaPRL shell; mp.bat runs from editor/ml
                                # (the Windows build is bytecode)
```

Run by hand, that workflow builds, runs the two shell tests through
`mp.bat`, and, with its `census` input, builds every theory and runs the
proof census, which matches the Linux expected file. MSVC does not build:
OMake does not build on OCaml 5.4.1 there, and camlp5 does not install on
4.14.4.

### Why OMake, not dune

MetaPRL stays on OMake. A port to dune was priced at about 30 to 37
engineer-days (the build generates code, runs its own filter over every theory
and writes proof archives), and OMake already builds the tree and checks every
stored proof on Linux and Windows. Two things would reopen the question: if
OMake stops building from opam on a supported OCaml, or if an opam release of
MetaPRL is decided.

The 2017 build targeted OCaml 4.05 with camlp5 7.02; its instructions are kept
as they were in the plain-text [`README`](./README) (plus
[`README.MACOSX`](./README.MACOSX) and [`README.WIN32`](./README.WIN32)).

## License

GPL-2.0-or-later. Every source file carries a GNU General Public License
header ("either version 2 of the License, or (at your option) any later
version"); the full text of GPL version 2 is in [`COPYING`](./COPYING).
