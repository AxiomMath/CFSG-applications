import CFSGOutside.HallPaige.Lie.SymplecticPolar
import CFSGOutside.HallPaige.Catalogue
import CFSGOutside.HallPaige.Cosets

/-!
# The catalogue cases `C_r(q)`, `B_2(q)` (`q` even) and `B_r(q)` (`q` even)

`PSp_{2n}(q)` acting on the points of `ℙ^{2n-1}(q)` satisfies the polar-space criterion; the
point stabilizer is good when `q` is even (odd index) and when `n ≥ 3` (a Klein four-group of
plane signs). The corpus identifies the TauCeti carriers of `C_r(q)`, `B_2(q)` and `B_r(q)`
(`q` even) with `PSp_{2r}(q)`.
-/

namespace CFSGOutside.HallPaige

open Symplectic Corpus.Lie TauCeti

variable {K : Type} [Field K] [Finite K]

/-- **Hall–Paige for `PSp_{2n}(q)`, `n ≥ 2`, `q` even or `n ≥ 3`.** -/
theorem hasCompleteMapping_PSp {n : ℕ} (hn : 2 ≤ n) (hcase : Even (Nat.card K) ∨ 3 ≤ n)
    (hG : IsGood (StatedProj (StatedSp n K)))
    (hP : ProperSubgroupsAdmissible (StatedProj (StatedSp n K))) :
    HasCompleteMapping (StatedProj (StatedSp n K)) := by
  refine hasCompleteMapping_of_wilcoxCriterion cosetStatement (wilcoxCriterion_PSp hn ?_) hP
  by_cases hq : Even (Nat.card K)
  · exact isGood_stabilizer_basePt_of_even _ hq hG
  · exact isGood_stabilizer_basePt_of_three_le (hcase.resolve_left hq)
      (neg_one_ne_one_of_odd_card (Nat.not_even_iff_odd.1 hq))

theorem card_galoisField_primePower (q : PrimePower) [Fact q.p.Prime] :
    Nat.card (GaloisField q.p q.exponent) = q.card :=
  GaloisField.card q.p q.exponent q.exponent_pos.ne'

theorem even_card_of_p_eq_two {q : PrimePower} (h : q.p = 2) : Even q.card := by
  rw [PrimePower.card, h]
  exact (Nat.even_pow' q.exponent_pos.ne').2 even_two

section
variable [h0 : Corpus.Lie.SymplecticEquivs]
include h0

/-- **Hall–Paige for `C_r(q)`**: the minimal-counterexample step. -/
theorem catalogueCase_C (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.C r q).Valid) :
    CatalogueCase (.lie ⟨.C r q, hv⟩) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hr : 3 ≤ r := ((LieTypeIndex.inStandardRange_iff _).1
    ((LieTypeIndex.valid_iff _).1 hv).1).1
  intro hG hP
  obtain ⟨e⟩ := Corpus.Lie.SymplecticEquivs.nonempty_mulEquiv_lie_C_of_statedProj hv (card_galoisField_primePower q)
  exact HasCompleteMapping.of_mulEquiv e (hasCompleteMapping_PSp (by omega) (Or.inr hr)
    (IsGood.of_mulEquiv e.symm hG) (ProperSubgroupsAdmissible.of_mulEquiv e.symm hP))

/-- **Hall–Paige for `B_2(q)`, `q` even**: the minimal-counterexample step. -/
theorem catalogueCase_B2_even (q : PrimePower) (hv : (LieTypeIndex.B 2 q).Valid) (hq : q.p = 2) :
    CatalogueCase (.lie ⟨.B 2 q, hv⟩) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  intro hG hP
  obtain ⟨e⟩ := Corpus.Lie.SymplecticEquivs.nonempty_mulEquiv_lie_B2_of_statedProj hv (card_galoisField_primePower q)
  refine HasCompleteMapping.of_mulEquiv e (hasCompleteMapping_PSp le_rfl (Or.inl ?_)
    (IsGood.of_mulEquiv e.symm hG) (ProperSubgroupsAdmissible.of_mulEquiv e.symm hP))
  rw [card_galoisField_primePower]
  exact even_card_of_p_eq_two hq

/-- **Hall–Paige for `B_r(q)`, `q` even, `r ≥ 3`**: the minimal-counterexample step. -/
theorem catalogueCase_B_even (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid)
    (hq : q.p = 2) (hr : 3 ≤ r) : CatalogueCase (.lie ⟨.B r q, hv⟩) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  intro hG hP
  obtain ⟨e⟩ := Corpus.Lie.SymplecticEquivs.nonempty_mulEquiv_lie_B_of_statedProj hv hq hr (card_galoisField_primePower q)
  exact HasCompleteMapping.of_mulEquiv e (hasCompleteMapping_PSp (by omega) (Or.inr hr)
    (IsGood.of_mulEquiv e.symm hG) (ProperSubgroupsAdmissible.of_mulEquiv e.symm hP))

end

end CFSGOutside.HallPaige
