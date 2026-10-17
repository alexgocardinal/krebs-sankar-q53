# What remains to formalize

The finite witness and D8-section implication have now been compiled and
audited on the author's Mac with Lean 4.29.0. The audit reports only standard
Lean foundations for `d8_section_has_three_chromatic_cayley`. This plan is
not a machine-checked classification proof.
The manuscript's direct structural proof avoids
Sanov's theorem and the finite structural classification assumed by the
separate CayleyExpanded project.

## Target statement

For every nonabelian group G with g^4 = 1 for every element, prove equivalence
of: an inverse-closed identity-free connection set with chromatic number
exactly three; a D8 section; and failure to be isomorphic to Q8 × E for any
elementary abelian two-group E. Allow infinite groups and disconnected graphs.
Also prove existence of a connection set of cardinality at most ten in the
positive cases. A finite-graph theorem alone is not the target.

## Direct proof modules

1. Definitions: right Cayley graph, exact three-chromaticity, sections,
   exponent dividing four, quaternion and dihedral models, and elementary
   abelian two-groups. Interpret E as an arbitrary F2-vector space, not only
   a finite product.
2. D8 witness: completed in `Witness.lean` and integrated with the general
   group definition in `D8Group.lean`.
3. Section lifting: completed in `CayleyCore.lean`, `CycleLift.lean`,
   `QuotientLift.lean`, and `SubgroupLift.lean`, including finite size ≤ 10.
4. Structural theorem: absence of a D8 section implies central involutions;
   central squares and commutators; the noncommuting-pair square identity;
   a quaternion subgroup; splitting off a central elementary abelian factor.
   The complement argument uses classical choice in the infinite case.
5. Quaternionic obstruction: prove the coordinate graph isomorphism; prove
   or import a fully formalized cubelike obstruction; handle arbitrary E by
   the finite odd-cycle reduction.
6. Assemble the final equivalences and at-most-ten bound. Every imported
   result must have a checked proof or be explicitly disclosed as an extra
   assumption. A citation in prose is not a Lean proof.

## Acceptance checks

- Pin Lean in lean-toolchain and Mathlib in lake-manifest.json.
- Make the default library target import every proof module and final theorem.
- Run lake exe cache get, lake build, and the final theorem's Audit.lean.
- In Audit.lean, import the final module and use #check and #print on the final
  theorem, then #print axioms with its actual fully qualified name.
- Review the quantified statement and every hypothesis. A theorem accepting
  a structure containing the desired result is still conditional.
- Inspect dependencies for sorryAx and unproved custom axioms; inspect sources
  for sorry, admit, axiom and opaque declarations without proved content.
  Text search is an aid, not sufficient evidence by itself.
- Disclose any native computation trust assumptions if used. Prefer ordinary
  kernel-checked proof terms for the advertised complete theorem.
- Rebuild a fresh checkout and record the exact commit and commands.

## Third-party project

https://github.com/tysunseven/CayleyExpanded
Its README lists an abelian obstruction, finite no-D8 classification, and
Sanov finiteness theorem as external inputs. Inspect its license and preserve
attribution before reuse. Compiling it can check the conditional result;
it does not complete this direct manuscript's formalization.
