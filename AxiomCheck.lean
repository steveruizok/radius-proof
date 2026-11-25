import RadiusProof

/-! Run `lake env lean AxiomCheck.lean`. Each result must list only the three standard axioms
`propext`, `Classical.choice` and `Quot.sound`, and in particular must not list `sorryAx`. -/

#print axioms RadiusProof.nested_radius_theorem
#print axioms RadiusProof.cthickening_roundedRect
#print axioms RadiusProof.roundedRect_inj
#print axioms RadiusProof.outer_radius_eq
#print axioms RadiusProof.inner_radius_eq
#print axioms RadiusProof.equal_radii_iff
#print axioms RadiusProof.gap_le_outer_radius
