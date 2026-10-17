# Krebs–Sankar Question 5.3

Alex Chan — Harvard University and National Bureau of Economic Research.

This repository contains a manuscript, reproducible finite graph checks, and
a Lean development for the eight-vertex witness and the section-lifting
direction of the theorem.
The manuscript classifies nonabelian exponent-four groups admitting a
three-chromatic Cayley graph; disconnected Cayley graphs are permitted.

## Status

- Human-readable proof: supplied in the manuscript.
- Finite computational checks: reproduced on 16 October 2026.
- Lean witness and section-lifting direction: `lake build` completed on the
  author's Mac with Lean 4.29.0, and `lake env lean Audit.lean` reported only
  `propext`, `Classical.choice`, and `Quot.sound` for the section theorem.
  The theorem covers arbitrary groups with a subgroup surjecting onto the
  concrete D8, and yields a finite connection set of at most ten elements.
- Complete Lean proof of this manuscript: NOT supplied and NOT claimed.
- Publication priority: requires review; the manuscript cites overlapping work.

## Files

- `Krebs_Sankar_Q53_Chan.tex` and `.pdf`: revised manuscript.
- `verify_small.py`: standard-library Python checks supplied in the evidence.
- `finite_verification.json`: output reproduced from that script.
- `PROOF_AND_SCOPE.txt`: supplied mathematical proof and scope record.
- `TERMINAL_MAC_START_HERE.md`: Mac Terminal-only walkthrough.
- `FORMALIZATION_PLAN.md`: remaining proof work and acceptance checks.
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

## Lean status and related work

On the author's Mac, run `lake build` and `lake env lean Audit.lean` to check
the finite witness and the D8-section implication. The reverse implication,
the structural dichotomy, and the quaternionic obstruction are not yet proved
in this Lean project. The related third-party project is at
https://github.com/tysunseven/CayleyExpanded and states a theorem conditional
on external inputs. This packet does not redistribute that project.

Repository (currently private): https://github.com/alexgocardinal/krebs-sankar-q53

## Paper PDF

To compile using an installed LaTeX distribution:

```bash
pdflatex Krebs_Sankar_Q53_Chan.tex
pdflatex Krebs_Sankar_Q53_Chan.tex
```

Before submission, re-audit the exact final theorem and update the manuscript
if the remaining Lean proof is completed.
