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

The 2017 build targeted OCaml 4.05 with camlp5 7.02; its instructions are kept
as they were in the plain-text [`README`](./README) (plus
[`README.MACOSX`](./README.MACOSX) and [`README.WIN32`](./README.WIN32)).

## License

GPL-2.0-or-later. Every source file carries a GNU General Public License
header ("either version 2 of the License, or (at your option) any later
version"); the full text of GPL version 2 is in [`COPYING`](./COPYING).
