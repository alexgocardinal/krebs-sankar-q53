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
#check KrebsSankarQ53.fiveCycle_lift
#print axioms KrebsSankarQ53.fiveCycle_lift
#check KrebsSankarQ53.d8_threeColor_proper
#print axioms KrebsSankarQ53.d8_threeColor_proper
#check KrebsSankarQ53.d8_fiveCycle_edges
#print axioms KrebsSankarQ53.d8_fiveCycle_edges
#check KrebsSankarQ53.d8_quotient_has_three_chromatic_cayley
#print axioms KrebsSankarQ53.d8_quotient_has_three_chromatic_cayley
#check KrebsSankarQ53.d8_section_has_three_chromatic_cayley
#print axioms KrebsSankarQ53.d8_section_has_three_chromatic_cayley
#check KrebsSankarQ53.square_is_involution
#print axioms KrebsSankarQ53.square_is_involution
#check KrebsSankarQ53.noncommuting_involutions_product_order_four
#print axioms KrebsSankarQ53.noncommuting_involutions_product_order_four
#check KrebsSankarQ53.conjugate_involution
#print axioms KrebsSankarQ53.conjugate_involution
#check KrebsSankarQ53.involutionSubgroup
#print axioms KrebsSankarQ53.involutionSubgroup
#check KrebsSankarQ53.involution_reflects_product
#print axioms KrebsSankarQ53.involution_reflects_product
#check KrebsSankarQ53.involution_reflects_product_right
#print axioms KrebsSankarQ53.involution_reflects_product_right
