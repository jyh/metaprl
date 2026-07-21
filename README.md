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

**Status: archived / historically frozen (2017).** Preserved as a research
artifact and a record of two decades of proof-assistant engineering. Reading
the `theories/` and `refiner/` sources is the best way in.

## Building (historical)

The original build instructions live in the plain-text [`README`](./README)
(plus [`README.MACOSX`](./README.MACOSX) and [`README.WIN32`](./README.WIN32)).
They target the OCaml + OMake toolchain of the era and are kept verbatim as
historical content — they will not work against a modern toolchain unmodified.

## What revival would take

A working build targets OCaml 4.05 with camlp5 7.02, driven by a 0.9.8-era
OMake; none of those are drop-in against current toolchains. The mathematics in
`theories/` is written in MetaPRL's own camlp5 quotation syntax — extended
concrete syntax realised through camlp5 quotations and grammar extensions —
spread across several hundred source files (over 500 `.ml` files, the bulk of
them using these term-quotation constructs). Reviving the system therefore
means either resurrecting the exact legacy toolchain or porting both the
quotation front end and the build to modern equivalents, on top of the
system's own bootstrap of syntax extensions and filters. That is a
substantial, research-grade porting project rather than a routine version bump.

## License

GPL-2.0-or-later. Every source file carries a GNU General Public License
header ("either version 2 of the License, or (at your option) any later
version"); the full text of GPL version 2 is in [`COPYING`](./COPYING).
