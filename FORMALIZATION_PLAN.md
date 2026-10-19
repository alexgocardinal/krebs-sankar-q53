# Formalization map and acceptance checks

The exact target classification has been formalized in
`KrebsSankarQ53.q53_full_classification`. See `LEAN_VERIFICATION.md` for
the successful source commit, GitHub Actions run, and dependency audit.

## Scope

For any nonabelian group G with every fourth power equal to one:

- An inverse-closed, identity-free three-chromatic Cayley graph exists iff
  G has a D8 section.
- These conditions hold iff G is not isomorphic to Q8 × E for an arbitrary
  elementary abelian two-group E.
- Every positive case has such a finite connection set of cardinality at
  most ten.

G and E may be infinite, and the graphs may be disconnected. The obstruction
allows arbitrary connection sets. E is represented by a commutative group
whose elements square to one; the complement construction supplies the
equivalent F2-vector-space structure without a finite-dimensionality assumption.

## Completed proof stages

1. Concrete D8 witness and section lifting: the original witness, quotient,
   subgroup, and five-step modules.
2. No-D8 central involutions, squares, and commutators: the original structural
   modules through `PairCore`, `PairRelations`, and `PairCentralNormal`.
3. Pair square identity: `PairSquareIdentity`, using the quotient by {1,x²}.
4. Quaternion subgroup and centralizer: `QuaternionPair`,
   `QuaternionCentralizer`, and `QuaternionCover`.
5. Infinite central complement and product isomorphism:
   `ElementaryComplement` and `NoD8Classification`.
6. Cubelike obstruction for arbitrary exponent-two groups and connection
   sets: `CubelikeWinding` and `CubelikeObstruction`.
7. Explicit Q8 × E coordinate transfer: `QuaternionCubelike`.
8. Exact equivalences and inverse-closed ten-element witness:
   `Classification`.

## Acceptance checks

- Lean is pinned to 4.29.0; Mathlib and all transitive revisions are locked
  in `lake-manifest.json`.
- The default library target imports all proof modules and the final theorem.
- A fresh GitHub checkout successfully retrieved Mathlib's cache and ran
  `lake build`, the allowlist axiom audit, and `lake env lean Audit.lean`.
- The audit prints the actual final theorem and its definitions and hypotheses.
- The final theorem depends only on
  `[propext, Classical.choice, Quot.sound]`.
- No proof placeholders, unproved custom axioms, or native computation axioms
  are used. Finite coordinate verifications use ordinary kernel-checked
  `decide`.
- The third-party MIT notice and exact source revision are retained.

## Review status

No Lean proof gap remains in the exact classification at the checked source
commit. The implementation is in draft PR #3 for review and merge.
Publication priority and the manuscript's historical claims remain matters
for mathematical/editorial review.

## Third-party proof source

The combinatorial winding lemmas are adapted from Sergi Galán's MIT-licensed
`decalion89/chromatic-number-of-the-plane/lean/TheoremW.lean`, revision
`cb660f322dce47a773f347d39818ffc46e6ca72c`. The source used Lean 4.34.1;
the retained lemmas compile under this project's 4.29.0. The averaging and
`TheoremWInf` modules are not imported. Neither CayleyExpanded nor any
external classification or cubelike theorem is assumed.
