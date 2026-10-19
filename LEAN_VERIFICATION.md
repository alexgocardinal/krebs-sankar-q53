# Lean verification record — 19 October 2026

## Checked result

`KrebsSankarQ53.q53_full_classification` in
`KrebsSankarQ53/Classification.lean` proves, for every group G satisfying
`∀ g, g ^ 4 = 1` and `∃ i j, i*j ≠ j*i`:

1. An inverse-closed, identity-free connection set with a proper three-coloring
   and no proper two-coloring exists iff G has a D8 section.
2. G has a D8 section iff G is not isomorphic to Q8 × E for any commutative
   exponent-two group E.
3. Every positive case has such a finite connection set of cardinality at most ten.

Neither G nor E is assumed finite. Connection sets in the obstruction may be
infinite. No connectedness assumption is imposed.

## Reproducible evidence

- Proof source commit: [2ed9cc4869886ca847d77086d4727ef534449212](https://github.com/alexgocardinal/krebs-sankar-q53/commit/2ed9cc4869886ca847d77086d4727ef534449212)
- Fresh GitHub Actions checkout and successful run:
  [Lean verification 39316121516](https://github.com/alexgocardinal/krebs-sankar-q53/actions/runs/39316121516)
- Lean: `leanprover/lean4:v4.29.0`.
- Mathlib: `8a178386ffc0f5fef0b77738bb5449d50efeea95`
  (`v4.29.0`), with transitive dependencies pinned by `lake-manifest.json`.
- Mathlib cache retrieval, `lake build`, the workflow's axiom audit, and
  `lake env lean Audit.lean` succeeded.
- The allowlist audit covered 708 declarations under `KrebsSankarQ53`.
- The final theorem's actual printed dependencies are exactly:
  `[propext, Classical.choice, Quot.sound]`.
- No source placeholders, custom axioms, or native computation axioms were added.
  Finite coordinate checks use ordinary kernel-checked `decide`.

## Proof modules

| Part | Modules |
| --- | --- |
| Pair square identity | `PairSquareIdentity.lean` |
| Centralizer and common square | `QuaternionCentralizer.lean` |
| Standard Q8 embedding | `QuaternionPair.lean` |
| Quaternion–center cover | `QuaternionCover.lean` |
| Infinite elementary abelian complement | `ElementaryComplement.lean` |
| Structural product decomposition | `NoD8Classification.lean` |
| Winding and arbitrary cubelike obstruction | `CubelikeWinding.lean`, `CubelikeObstruction.lean` |
| Q8 × E coordinate transfer | `QuaternionCubelike.lean` |
| Exact equivalences and ten-element witness | `Classification.lean` |

## Third-party attribution

The combinatorial portion of Sergi Galán's MIT-licensed
[`TheoremW.lean`](https://github.com/decalion89/chromatic-number-of-the-plane/blob/cb660f322dce47a773f347d39818ffc46e6ca72c/lean/TheoremW.lean)
was adapted in `CubelikeWinding.lean`. Its full MIT notice is retained.
The upstream project uses Lean 4.34.1. This adaptation compiles on this
repository's pinned 4.29.0 and imports neither `TheoremWInf` nor the
real-valued averaging or circular-clique modules.

The exponent-two argument uses reversal and permutation invariance of winding
sums, then path parity and coset extension. It handles infinite groups and
arbitrary connection sets directly. No finite-group classification, Sanov
finiteness theorem, or external cubelike theorem is assumed.

## Remaining work

The exact classification and stated size bound have no remaining Lean proof
gaps at the checked source commit. PR #3 remains a draft for review and merge.
