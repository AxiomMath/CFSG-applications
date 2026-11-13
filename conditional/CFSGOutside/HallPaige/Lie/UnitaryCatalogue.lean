import CFSGOutside.HallPaige.Lie.UnitaryFour
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# The catalogue case `²A_r(q)`, `r ≥ 3`, except `r = 3` with `q` odd

By the corpus identification of the TauCeti carrier of `²A_r(q)` with
`PSU_{r+1}(q) = StatedProj (StatedSU (r+1) q 𝔽_{q²})`
(`CFSGOutside.Corpus.Lie.typeTwistedAGroupEquivStatedProj`), `CFSGOutside.HallPaige.Unitary.hasCompleteMapping_PSU`
(with `CFSGOutside.HallPaige.Unitary.hasCompleteMapping_PSU'` for `r = 3`, `q` odd) settles `²A_r(q)` for all
`r ≥ 3`.
-/

namespace CFSGOutside.HallPaige

open Unitary Corpus.Lie TauCeti

section
variable [h0 : Corpus.Lie.UnitaryEquiv]
include h0

/-- **Hall–Paige for `²A_r(q)`, `r ≥ 3`**: the minimal-counterexample step. -/
theorem catalogueCase_twistedA (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.twistedA r q).Valid)
    (hr : 3 ≤ r) : CatalogueCase (.lie ⟨.twistedA r q, hv⟩) := by
  intro hG hP
  have e := typeTwistedAGroupEquivStatedProj r q hv
  set d : ValidLieTypeIndex := ⟨.twistedA r q, hv⟩
  set p := ValidLieTypeIndex.characteristic d
  set f := ValidLieTypeIndex.fieldExponent d
  have hf : f ≠ 0 := (ValidLieTypeIndex.fieldExponent_pos d).ne'
  have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
    rw [GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  rw [← SUid_eq_statedSU (K := GaloisField p (2 * f)) (p := p) (f := f) (r + 1)] at e
  have : Fintype (GaloisField p (2 * f)) := Fintype.ofFinite _
  obtain ⟨ι, hι⟩ : IsSquare (-1 : GaloisField p (2 * f)) := by
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hK]
    intro h
    have : (p ^ f) ^ 2 % 4 = 0 ∨ (p ^ f) ^ 2 % 4 = 1 := by
      rcases Nat.even_or_odd (p ^ f) with ⟨k, hk⟩ | ⟨k, hk⟩ <;> rw [hk] <;> ring_nf <;> omega
    omega
  exact HasCompleteMapping.of_mulEquiv e.symm (hasCompleteMapping_PSU'
    (isUnitaryInvolution_unitaryInvolution hK) (by omega) hι.symm (IsGood.of_mulEquiv e hG)
    (ProperSubgroupsAdmissible.of_mulEquiv e hP))

end

end CFSGOutside.HallPaige
