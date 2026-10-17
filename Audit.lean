import KrebsSankarQ53

/-!
Run `lake env lean Audit.lean` after a successful `lake build`.
This audit covers only the finite witness; it is not a classification audit.
-/

#check KrebsSankarQ53.concrete_cayley_witness
#print axioms KrebsSankarQ53.concrete_cayley_witness
