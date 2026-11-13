import CFSGOutside.HallPaige.Lie.RankOneSU3
import CFSGOutside.HallPaige.Lie.Basic
import CFSGOutside.HallPaige.DoubleCosets
import CFSGOutside.HallPaige.Catalogue
import CFSGOutside.Corpus.HallPaige.LieUnitary

/-!
# The catalogue case `²A₂(q)`

By the corpus identification of the TauCeti carrier of `²A₂(q)` with
`PSU₃(q) = StatedProj (StatedSU 3 q 𝔽_{q²})` (`CFSGOutside.Corpus.Lie.typeTwistedAGroupEquivStatedProj`),
`StatedSU = SUid` (`CFSGOutside.HallPaige.Unitary.SUid_eq_statedSU`) and the `J`-model
(`CFSGOutside.HallPaige.UnitaryThree.psuEquiv`): for `q` odd `PSU₃(q)` has a complete mapping outright
(`CFSGOutside.HallPaige.UnitaryThree.hasCompleteMapping_PG`, Wilcox Lemma 23), and for `q` even the Wilcox
criterion holds with `H = B` (`CFSGOutside.HallPaige.UnitaryThree.wilcoxCriterion_PG`).
-/

namespace CFSGOutside.HallPaige

open Unitary Corpus.Lie TauCeti

section
variable [h0 : Corpus.Lie.UnitaryEquiv]
include h0

/-- **Hall–Paige for `²A₂(q)`**: the minimal-counterexample step. -/
theorem catalogueCase_twistedA_two (q : PrimePower) (hv : (LieTypeIndex.twistedA 2 q).Valid) :
    CatalogueCase (.lie ⟨.twistedA 2 q, hv⟩) := by
  intro hG hP
  have e := typeTwistedAGroupEquivStatedProj 2 q hv
  set d : ValidLieTypeIndex := ⟨.twistedA 2 q, hv⟩
  set p := ValidLieTypeIndex.characteristic d
  set f := ValidLieTypeIndex.fieldExponent d
  have hf : f ≠ 0 := (ValidLieTypeIndex.fieldExponent_pos d).ne'
  have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
    rw [GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  rw [← SUid_eq_statedSU (K := GaloisField p (2 * f)) (p := p) (f := f) (2 + 1)] at e
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨u, hu⟩ := hσ.exists_norm_neg_one
  let e' := e.trans (UnitaryThree.psuEquiv hσ.invol hu)
  by_cases h2 : (2 : GaloisField p (2 * f)) = 0
  · have hW := UnitaryThree.wilcoxCriterion_PG hσ h2 (IsGood.of_mulEquiv e' hG)
    exact HasCompleteMapping.of_mulEquiv e'.symm
      (hasCompleteMapping_of_wilcoxCriterion cosetStatement hW
        (ProperSubgroupsAdmissible.of_mulEquiv e' hP))
  · exact HasCompleteMapping.of_mulEquiv e'.symm (UnitaryThree.hasCompleteMapping_PG hσ h2)

end

end CFSGOutside.HallPaige
