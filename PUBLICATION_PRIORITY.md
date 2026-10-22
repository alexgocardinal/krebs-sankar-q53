# Publication-priority review — 22 October 2026

This review concerns the exact theorem in `Krebs_Sankar_Q53_Chan.tex`.
It distinguishes an earlier statement from a complete proof, and a theorem
from ingredients that may already be classical.

| Claim or ingredient | Earlier record | Assessment |
| --- | --- | --- |
| Nonabelian exponent-four classification question | Krebs–Sankar, Question 5.3 | The target matches the question, with disconnected graphs permitted. |
| Three-chromatic Cayley graph iff a D8 section | Public CayleyExpanded project | The same criterion is explicitly stated conditionally on three inputs; the finite no-D8 classification is one of them. Do not describe the criterion itself as wholly new. |
| Connection set {r²,s,rs} on D8 | CayleyExpanded, Concrete.lean | Identical witness and its three-chromaticity already appear there. |
| Section transfer | CayleyExpanded, QuotientColorLift.lean and subgroup lift | Already established with a full preimage connection set. |
| Uniform connection-set cardinality at most ten | The manuscript's five-cycle lift | No earlier explicit bound was located in the checked sources. This strengthens the full-preimage construction. No optimality claim is made. |
| Graphically abelian groups are Q8 × E in the nonabelian case | Goldstone–Weld (2010) | A different property; cite the overlap without treating it as the chromatic classification. |
| Central involutions and shared order-four square imply Q8 × E | McCabe–Weld (2011), Proposition 4.10 | Earlier arbitrary-group splitting result. Deriving its hypotheses from absence of a D8 section remains a distinct step of the direct proof. |
| Cubelike chromatic obstruction | Payan (1992) | Established theorem, cited explicitly. |
| Complete unconditional Lean verification | Current repository | Exact scope and successful axiom audit are recorded in LEAN_VERIFICATION.md. Code attribution to Sergi Galán is preserved. Formal verification does not establish publication priority. |

## Sources

- M. Krebs and M. Sankar, *Abelian groups without 3-chromatic Cayley graphs*,
  J. Combin. Theory Ser. B **179** (2026), 205–218.
  [arXiv v2](https://arxiv.org/html/2410.11028v2);
  [DOI](https://doi.org/10.1016/j.jctb.2026.03.004).
  The arXiv record began on 14 October 2024; v2 is dated 23 February 2026.
- [tysunseven/CayleyExpanded](https://github.com/tysunseven/CayleyExpanded),
  [commit 15bc128](https://github.com/tysunseven/CayleyExpanded/commit/15bc1289e3e1f13920c54cae69cef4d07789f38c).
  The retrieved commit metadata is dated 21 July 2026. This is a commit date,
  not an independently established date on which the repository became public.
  The README explicitly lists the external inputs.
- R. Goldstone and K. Weld, *Graphically abelian groups*, Discrete Math.
  **310** (2010), 2806–2810.
  [DOI](https://doi.org/10.1016/j.disc.2010.06.015).
- J. McCabe and K. Weld, *On automorphisms of Cayley graphs and irregular
  groups*, Australas. J. Combin. **51** (2011), 157–173.
  [Official full text](https://ajc.maths.uq.edu.au/pdf/51/ajc_v51_p157.pdf).
  Definition 4.7 and Proposition 4.10 are the relevant passages; the paper
  places no restriction on the cardinality of its groups.
- C. Payan, *On the chromatic number of cube-like graphs*, Discrete Math.
  **103** (1992), 271–277.
  [DOI](https://doi.org/10.1016/0012-365X(92)90319-B).
- K. Enami and T. Matsushita, *Cayley graphs of abelian groups, circular
  colorings and discrete fundamental groups*,
  [arXiv:2610.21940](https://arxiv.org/abs/2610.21940).
  The checked follow-up concerns abelian groups and does not supply the
  nonabelian exponent-four classification.

## Manuscript positioning and limits

The manuscript presents an unconditional answer with a direct structural
argument for arbitrary groups and a uniform connection-set bound. It credits
the identical conditional section criterion and witness, the earlier
splitting theorem, and Payan's obstruction. It makes no first-publication
or optimality claim.

The search checked exact question references, exponent-four and quaternionic
variants, primary papers, arXiv follow-ups, and the public overlapping Lean
source. No earlier complete unconditional proof of this exact classification
was located. This bounded search cannot exclude unindexed material,
unpublished work, or a proof under different terminology. A private GitHub
commit does not by itself establish public disclosure of the manuscript.
