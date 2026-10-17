import KrebsSankarQ53

/-!
Run `lake env lean Audit.lean` after a successful `lake build`.
This audit covers the finite witness and the general coloring lemmas;
it is not a classification audit.
-/

#check KrebsSankarQ53.concrete_cayley_witness
#print axioms KrebsSankarQ53.concrete_cayley_witness
#check KrebsSankarQ53.cayleyColor_pullback
#print axioms KrebsSankarQ53.cayleyColor_pullback
#check KrebsSankarQ53.no_two_of_five_cycle
#print axioms KrebsSankarQ53.no_two_of_five_cycle
