# Finite Lean verification evidence

All **71 current executable fixtures** have passing evidence: 68 unchanged
passes from the initial full run and three successful targeted rechecks.
This is a provenance-checked combination, not a new simultaneous full run.
The separate final kernel rebuild passed 612 modules and 5,290 axiom reports.

Read [summary.txt](summary.txt) for each selected result, and
[provenance.json](provenance.json) for the exact source snapshots, commands,
dependency revisions, original summaries and correction history.
[initial-failures.log](initial-failures.log) preserves all three original flags.
Two fixture budget assertions omitted translation-generation arithmetic; the
third flag came from the harness expecting a singleton for the raw zero-size
translation list rather than the later wrapper. The production Lean proofs
were unchanged between the two runtime snapshots. The corrected fixtures
were included in the fresh final kernel snapshot.

The final source/configuration SHA-256 is
`9d5e9865f2e599654af2082098a609a237ed2208d99adbb14648695b9527b04b`.
The archived [final kernel log](kernel-final.log) and
[complete fixture output](runtime-stdout.log) are retained alongside the
original runner, corrected runner and exact evidence-merging helper.
`MANIFEST.sha256` covers the 12 generated evidence files; this README and the
local log inclusion and whitespace rules were added afterward. Captured logs
and patch context retain their original bytes, including whitespace.

To reproduce a full current fixture run, first rebuild the proof with the
pinned Lean 4.31.0 toolchain and dependencies as described in
[the parent README](../README.md). From the repository root, use a fresh
output directory and the resulting complete kernel transcript:

```sh
python3 scripts/verify_lean.py --jobs 4 > /tmp/current-lean-kernel.txt
python3 lean/runtime-verification/runner-corrected.py --run \
  --root "$PWD" --toolchain-bin /path/to/lean-4.31.0/bin \
  --verified-log /tmp/current-lean-kernel.txt --jobs 4 \
  --logs /tmp/current-lean-fixtures
```

The runner rejects mismatched source snapshots. Some exhaustive fixtures
are slow. In the frozen source-family fixture, specialization of the closed
row-size predicate repeats the full graph execution while checking its 64
rows; the archived run retains that complete check unchanged. These timings
are finite correctness checks, not APSP benchmarks or the theorem's work model.
