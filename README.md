# Krebs–Sankar Question 5.3

Alex Chan — Harvard University and National Bureau of Economic Research.

This repository contains a manuscript, reproducible finite graph checks, and
a complete Lean formalization of the classification theorem, including
arbitrary infinite groups and disconnected Cayley graphs.
The manuscript classifies nonabelian exponent-four groups admitting a
three-chromatic Cayley graph; disconnected Cayley graphs are permitted.

## Status

- The exact classification is formalized as
  `KrebsSankarQ53.q53_full_classification` in
  `KrebsSankarQ53/Classification.lean`.
- The theorem proves equivalence of a three-chromatic Cayley graph, a D8
  section, and failure of the Q8 × E form, where E is any elementary
  abelian two-group. It also gives a finite, inverse-closed, identity-free
  connection set of cardinality at most ten in every positive case.
- `lake build`, the project-wide axiom audit, and `lake env lean Audit.lean`
  passed for proof revision `0866eb8` on 19 October 2026. The final theorem depends only on
  `propext`, `Classical.choice`, and `Quot.sound`.
- The completed formalization and revised manuscript are included in this
  repository; [PR #3](https://github.com/alexgocardinal/krebs-sankar-q53/pull/3)
  records the proof development.
- See [LEAN_VERIFICATION.md](LEAN_VERIFICATION.md) for the exact checked
  source commit, CI run, scope, module map, and third-party attribution.
- Human-readable manuscript and finite computational checks are retained.
  Formal verification does not establish publication priority.

## Files

- `Krebs_Sankar_Q53_Chan.tex` and `.pdf`: revised manuscript.
- `verify_small.py`: standard-library Python checks supplied in the evidence.
- `finite_verification.json`: output reproduced from that script.
- `PROOF_AND_SCOPE.txt`: supplied mathematical proof and scope record.
- `FORMALIZATION_PLAN.md`: completed proof map and acceptance checks.
- `PUBLICATION_PRIORITY.md`: literature overlap and the manuscript's contribution.
- `KrebsSankarQ53/Witness.lean`: concrete graph and finite multiplication.
- `KrebsSankarQ53/CayleyCore.lean`, `CycleLift.lean`, `D8Group.lean`,
  `QuotientLift.lean`, `SubgroupLift.lean`: checked coloring and lifting lemmas.
- `KrebsSankarQ53.lean`, `Audit.lean`, `lakefile.toml`, `lean-toolchain`:
  project entry point, axiom check, and pinned Lean/Mathlib configuration.

## Run finite checks

From this folder, run:

```bash
python3 verify_small.py
```

The script writes `finite_verification.json`. Expect zero three-chromatic
examples in both exhaustive quaternionic searches (16 and 512 sets), and a
three-chromatic D8 witness. This is not a proof of the infinite classification.

## Lean verification and related work

The default library imports every proof module, including the final theorem.
Run:

```bash
lake exe cache get
lake build
lake env lean Audit.lean
```

GitHub Actions runs the build and an axiom allowlist audit on pull requests
and pushes to main. The final theorem's audit is in `Audit.lean`.

The cubelike proof adapts the combinatorial winding lemmas from Sergi
Galán's MIT-licensed development. Attribution and the full MIT notice are
retained in `CubelikeWinding.lean`; the pinned Lean/Mathlib version remains
4.29.0. The infinite result uses an exponent-two reversal argument and
does not import the upstream averaging modules.

The separate project https://github.com/tysunseven/CayleyExpanded is not a
dependency of this formalization. No external classification, finiteness,
or cubelike axiom is assumed.

## Paper PDF

To compile using an installed LaTeX distribution:

```bash
pdflatex Krebs_Sankar_Q53_Chan.tex
pdflatex Krebs_Sankar_Q53_Chan.tex
```

Before submission, review the checked theorem and manuscript together and
rerun the verification commands on the intended release commit.

