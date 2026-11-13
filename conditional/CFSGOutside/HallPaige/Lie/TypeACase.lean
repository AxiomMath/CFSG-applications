import CFSGOutside.HallPaige.Lie.TypeA
import CFSGOutside.HallPaige.Catalogue
import CFSGOutside.Corpus.HallPaige.LieTypeA

/-!
# The catalogue case `A_r(q)`

By the corpus identification of the TauCeti carrier of `A_r(q)` with `PSL_{r+1}(𝔽_q)`
(`CFSGOutside.Corpus.Lie.linearCatalogCandidateEquivPSL`), `CFSGOutside.HallPaige.hasCompleteMapping_PSL`
settles every `A_r(q)` with `r ≥ 2`, and `A_1(q)` with `q` even or `q ≡ 3 (mod 4)`.
-/

namespace CFSGOutside.HallPaige

open TauCeti

section
variable [h0 : Corpus.Lie.TypeAEquiv]
include h0

/-- **Hall–Paige for `A_r(q)`, `r ≥ 2`, or `q` even, or `q ≡ 3 (mod 4)`**: the
minimal-counterexample step. -/
theorem catalogueCase_A (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.A r q).Valid)
    (h : 2 ≤ r ∨ q.p = 2 ∨ q.card % 4 = 3) : CatalogueCase (.lie ⟨.A r q, hv⟩) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hr : 1 ≤ r := ((LieTypeIndex.inStandardRange_iff _).1
    ((LieTypeIndex.valid_iff _).1 hv).1).1
  intro hG hP
  let e := Corpus.Lie.linearCatalogCandidateEquivPSL r q hv
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  refine HasCompleteMapping.of_mulEquiv e.symm
    (hasCompleteMapping_PSL m ?_ (IsGood.of_mulEquiv e hG) (ProperSubgroupsAdmissible.of_mulEquiv e hP))
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.card :=
    GaloisField.card q.p q.exponent q.exponent_pos.ne'
  rcases h with h | h | h
  · right; left; omega
  · left
    rw [hcard, PrimePower.card, h]
    exact (Nat.even_pow' q.exponent_pos.ne').2 even_two
  · right; right; rw [hcard]; exact h

end

end CFSGOutside.HallPaige
