# Krebs–Sankar Question 5.3

Alex Chan — Harvard University and National Bureau of Economic Research.

This packet contains a manuscript, reproducible finite graph checks, and a
first Lean checkpoint for the eight-vertex witness.
The manuscript classifies nonabelian exponent-four groups admitting a
three-chromatic Cayley graph; disconnected Cayley graphs are permitted.

## Status

- Human-readable proof: supplied in the manuscript.
- Finite computational checks: reproduced on 16 October 2026.
- Finite Lean witness source: supplied, but not compiled in the preparation
  environment. Run the commands in `TERMINAL_MAC_START_HERE.md` on a Mac.
- Complete Lean proof of this manuscript: NOT supplied and NOT claimed.
- Publication priority: requires review; the manuscript cites overlapping work.

## Files

- `Krebs_Sankar_Q53_Chan.tex` and `.pdf`: revised manuscript.
- `verify_small.py`: standard-library Python checks supplied in the evidence.
- `finite_verification.json`: output reproduced from that script.
- `PROOF_AND_SCOPE.txt`: supplied mathematical proof and scope record.
- `TERMINAL_MAC_START_HERE.md`: Mac Terminal-only walkthrough.
- `FORMALIZATION_PLAN.md`: remaining proof work and acceptance checks.
- `KrebsSankarQ53/Witness.lean`: concrete Cayley graph, coloring, odd-cycle
  obstruction, and finite multiplication-table proof candidates.
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

## Lean status and related work

Lean files for the finite witness are included. Their successful compilation
has not been independently confirmed in this preparation environment. Run
`lake update`, `lake exe cache get`, `lake build`, and
`lake env lean Audit.lean` on your Mac. These commands do not prove the full
classification. The related third-party project is at
https://github.com/tysunseven/CayleyExpanded and states a theorem conditional
on external inputs. This packet does not redistribute that project.

Author profile: https://github.com/alexgocardinal
Suggested repository name: `krebs-sankar-q53` (not asserted to exist).

## Paper PDF

To compile using an installed LaTeX distribution:

```bash
pdflatex Krebs_Sankar_Q53_Chan.tex
pdflatex Krebs_Sankar_Q53_Chan.tex
```

Before submission, replace the paper's pending-deposit statement with a
verified project URL and fixed release/commit. Update proof status only after
checking the final theorem and its dependencies.
