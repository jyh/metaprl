# Filter_ocaml pin

`filter/base/filter_ocaml.ml` maps OCaml syntax (camlp5's `MLast`) to MetaPRL
terms and back. The port to camlp5 8, which changed `MLast`, must keep the
terms the same. This pin records them.

- `pin_filter_ocaml.ml` parses each file, maps every top-level item to a term,
  and prints the term's MD5 (the full term with `PIN_FULL=1`). It then maps the
  term back to OCaml and to a term again, and prints whether that gives the
  same term. For each top-level `let`, it also prints
  `Free_vars.free_vars` of each bound expression. `pin_compat_camlp5_7.ml`
  and `pin_compat_camlp5_8.ml` extract those expressions from each version's
  `MLast`.
- `corpus/` holds the input files:
  - `coverage.ml` is written for this pin.
  - The other seven are copies of `mllib/` and `library/` files from commit
    `073c78cff` (this repository, same licence). Together they reach all 150
    term operators that the 51 `mllib/` and `library/` files produce.
- `pin_filter_ocaml.expected` was produced by this program built against the
  **camlp5 7 filter**, on OCaml 4.12.1 with camlp5 7.14 (the last camlp5 with
  the old `MLast`). That filter is the code at `073c78cff` plus
  `pin-reference.patch`. camlp5 7.14 already wraps module names as
  `V (option (V string))` and adds one argument to `StTyp`, `MtFun` and
  `MeFun`, so the 2017 code needs those 32 lines to compile there. The result:
  320 items; 278 round-trip to the same term; 42 fail on the way back and 8
  fail on the way in, both in the old filter too.

Run it against a built tree, with that tree's compilers on `PATH`:

    sh filter/test/run_pin_filter_ocaml.sh <tree> out.txt $(ls filter/test/corpus/*.ml | sort)
    sh filter/test/compare_pin.sh filter/test/pin_filter_ocaml.expected out.txt

What must match is the term's **structure** (`shape=`: the MD5 of the term
with each node's location pair blanked), the round trip and the free
variables. `compare_pin.sh` fails on any difference there. The full MD5
also covers locations; camlp5 7 and 8 record source positions differently
(for example, camlp5 8 starts a structure item after its keyword), so items
that differ only there are counted and reported, not failed.

Checked when it was made: two runs of the reference give byte-identical
output. Renaming one term operator (`str_open`) in the reference filter
changes 33 lines. Making `free_vars` drop every variable changes 183 lines.
238 items carry free variables; for 14 of them the old `free_vars` raises,
and that is pinned as it is.

Not covered:
- The old filter overflows the stack on `let f ?(x = 1) () = ...`, and the
  camlp5 7 parser rejects `type t = ..` and `match ... with exception`, so
  none of the three is in the corpus.
- Locations appear inside the terms as character offsets, so a change in how
  camlp5 counts them shows up as a difference.
