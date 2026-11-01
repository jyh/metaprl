# vir-arm-tools — the MetaPRL arm's driver, scripts and run records (O95)

A snapshot of the tools that produced every MetaPRL count for the VIR study
(programs 1-3 in `theories/vir/`), taken from the tools repository at commit
`b754500`. Nothing here is built by OMake.

- `STORED.tsv` — for each scored theorem, the step script whose proof is stored
  in that theory's `.prla` archive.
- `steps/*.mp` — the step scripts, fed to `editor/ml/mp -cli` by `mpdrive.py`.
- `runs-*.txt` — the driver's record of each run (one `=== STEP` / `=== CHILDREN`
  line per step); the counts are read from these.
- `verdict.sh` — replays the stored proofs of one module in `mp -batch` and
  compares each rule's status with `verdict*.expected`.
- `COUNTS-metaprl*.md` — the counts as reported.

Scripts that need the MetaPRL checkout read it from `VIR_METAPRL`
(e.g. `VIR_METAPRL=$PWD sh theories/vir/vir-arm-tools/test-verdict.sh`).

## Redactions in this snapshot

Made so the directory carries no local machine detail; no count or step changes:
- `clean-rebuild.sh`, `reset3.sh`, `test-verdict.sh`: the absolute paths of the
  author's checkouts became `$VIR_METAPRL` and the script's own directory.
- `runs-d2-*.txt`: the host name in the run header became `<host>`.
