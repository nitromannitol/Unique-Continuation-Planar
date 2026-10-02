# Contributing / Building notes

This repository is primarily a finished artifact rather than an actively
solicited collaborative project, but issues and pull requests are welcome.

The shared library [`Lattice-Probability`](https://github.com/nitromannitol/Lattice-Probability)
and the Schoenflies library [`schoenflies-lean`](https://github.com/alonamaloh/schoenflies-lean)
are `git` dependencies of `lakefile.lean`, each pinned to an exact commit; Lake
materializes them under `.lake/packages`.  They are read-only for this project,
and contributors must not edit the dependencies' sources.

## Building locally

```bash
lake exe cache get   # first time: prebuilt Mathlib
lake build           # compile the project
```

The production build is required to emit no Lean or linter warnings
(`python3 tools/check_warnings.py`).  The four Mathlib-only files
`UCPlanarAudit/*/Challenge.lean` are the sole exception: each contains one
documented statement-level `sorry`, checked against its completed solution by
`leanprover/comparator`.

A few practical notes for working with this development:

- **Never run `lake clean`.**  It wipes the Mathlib oleans and forces a
  multi-hour rebuild from source.  To force a project-only rebuild, remove the
  project build artifacts under `.lake/build/lib/lean/UCPlanar` (and the
  corresponding `.lake/build/ir/UCPlanar`) and re-run `lake build`.

- **Per-file rebuilds.**  Lake invalidates by content hash, not mtime, so
  `touch` does nothing; delete the specific `.olean` under
  `.lake/build/lib/lean/` and rebuild the module.

- **Frozen statements.**  The text between `-- FROZEN-STATEMENT-BEGIN` and
  `-- FROZEN-STATEMENT-END` in `UCPlanar/Frozen/` and `UCPlanar/External/` is
  pinned by the SHA-256 recorded in `ledger/manifest.yaml`.  A change there
  must be registered with `python3 tools/freeze.py` and shows up in
  `python3 tools/check_manifest.py`; proofs after the end marker may be
  changed freely.

- **The main results** are in `UCPlanar/MainTheorems.lean`; the axiom audit is
  `lake build UCPlanar.Meta.AxiomsAudit`, and the comparator surface is
  `lake build UCPlanarAudit`.  The audit module is deliberately not imported by
  the library root, so it is built only as an explicit target.

## Elaboration policy for new files

- Close arithmetic goals with named monotonicity lemmas and `calc`, not with
  `nlinarith`.  When a nonlinear fact is needed, hoist it into a small `private`
  lemma over abstract real variables, so that `Real.rpow` and `Real.exp` terms
  never enter a numeric tactic; in particular, never call `nlinarith` on a goal
  that contains `Real.rpow` or `Real.exp`.
- Before `ring` or `field_simp` on an expression built with `set`, run
  `clear_value` on the bound names; otherwise the let-bodies are unfolded inside
  the tactic.
- Do not split a file, narrow its imports, or add an instance cache "for
  performance" without a warm profile before and after
  (`lake env lean --profile <file>`).  The profiler's default 100 ms floor hides
  diffuse costs; use `-D profiler.threshold=1` when hunting them.
- Do not raise `maxHeartbeats` in a new file.  A default-budget failure is a
  design signal (usually a wrong lemma orientation or a `set`-bound term), not a
  budget problem.
- Keep Lean files under 1500 lines.
- Never run `lake clean` (see above).
