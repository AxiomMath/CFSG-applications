import CFSGOutside.HallPaige.Lie.OrthModels
import CFSGOutside.HallPaige.Lie.TypeA
import CFSGOutside.HallPaige.Catalogue
import CFSGOutside.Corpus.HallPaige.LieOrth

/-!
# The catalogue cases `B_r(q)` (`q` odd, `r ≥ 3`), `D_r(q)` and `²D_r(q)`

The corpus identifies the TauCeti carriers of these indices with `PΩ_{2r+1}`, `PΩ⁺_{2r}` and
`PΩ⁻_{2r}` over the fixed field of the index (`CFSGOutside.Corpus.Lie.typeBGroupEquivStatedProj_odd`,
`typeDGroupEquivStatedProj_of_valid`, `exists_typeTwistedDGroupEquivStatedProj_of_valid`), and
`PΩ` of a quadratic form with three orthogonal hyperbolic pairs satisfies the Wilcox criterion
(`CFSGOutside.HallPaige.Orth.wilcoxCriterion_omega`).
-/

namespace CFSGOutside.HallPaige

open TauCeti Corpus.Lie Orth

/-- The fixed field of a valid index is finite (the TauCeti instance, which instance search does
not find for an index written as an anonymous constructor). -/
theorem finite_fixedField (d : ValidLieTypeIndex) : Finite ↥(ValidLieTypeIndex.fixedField d) :=
  ValidLieTypeIndex.instFiniteSubtypeClosureMemSubfieldFixedField d

/-- The fixed field of an index of type `B` with odd characteristic has `2 ≠ 0`. -/
theorem two_ne_zero_fixedField_B {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.B r q).Valid)
    (hq : q.p ≠ 2) : (2 : ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)) ≠ 0 := by
  have := finite_fixedField ⟨.B r q, hv⟩
  have hcard : Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) = q.p ^ q.exponent := by
    rw [ValidLieTypeIndex.card_fixedField, ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
      ValidLieTypeIndex.characteristic, ValidLieTypeIndex.fieldExponent,
      LieTypeIndex.characteristic_B, LieTypeIndex.fieldExponent_B]
  have hodd : Odd (Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)) := by
    rw [hcard]; exact (q.prime_p.odd_of_ne_two hq).pow
  intro h2
  apply neg_one_ne_one_of_odd_card hodd
  rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, h2]

section
variable [h0 : Corpus.Lie.OrthEquivs]
include h0

/-- **Hall–Paige for `B_r(q)`, `q` odd, `r ≥ 3`**: the minimal-counterexample step. -/
theorem catalogueCase_B_odd (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid)
    (hq : q.p ≠ 2) (hr : 3 ≤ r) : CatalogueCase (.lie ⟨.B r q, hv⟩) := by
  have := finite_fixedField ⟨.B r q, hv⟩
  intro _ hP
  let e := typeBGroupEquivStatedProj_odd r q hv hq hr
  exact HasCompleteMapping.of_mulEquiv e.symm (hasCompleteMapping_POmegaOdd hr
    (two_ne_zero_fixedField_B hv hq) (ProperSubgroupsAdmissible.of_mulEquiv e hP))

/-- **Hall–Paige for `D_r(q)`**: the minimal-counterexample step. -/
theorem catalogueCase_D (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.D r q).Valid) :
    CatalogueCase (.lie ⟨.D r q, hv⟩) := by
  have hr : 4 ≤ r := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have := finite_fixedField ⟨.D r q, hv⟩
  intro _ hP
  let e := typeDGroupEquivStatedProj_of_valid r q hv
  exact HasCompleteMapping.of_mulEquiv e.symm (hasCompleteMapping_POmegaPlus (by omega)
    (ProperSubgroupsAdmissible.of_mulEquiv e hP))

/-- **Hall–Paige for `²D_r(q)`**: the minimal-counterexample step. -/
theorem catalogueCase_twistedD (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.twistedD r q).Valid) :
    CatalogueCase (.lie ⟨.twistedD r q, hv⟩) := by
  have hr : 4 ≤ r := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have := finite_fixedField ⟨.twistedD r q, hv⟩
  intro _ hP
  obtain ⟨b, c, hirr, ⟨e⟩⟩ := Corpus.Lie.OrthEquivs.exists_typeTwistedDGroupEquivStatedProj_of_valid r q hv
  exact HasCompleteMapping.of_mulEquiv e.symm (hasCompleteMapping_POmegaMinus hr hirr
    (ProperSubgroupsAdmissible.of_mulEquiv e hP))

end

end CFSGOutside.HallPaige
