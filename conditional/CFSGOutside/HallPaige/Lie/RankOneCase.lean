import CFSGOutside.HallPaige.Lie.RankOnePSL
import CFSGOutside.HallPaige.Lie.TypeACase

/-!
# The catalogue cases of type `A`, including `A₁(q)` with `q ≡ 1 (mod 4)`

`CFSGOutside.HallPaige.catalogueCase_A_one_mod_four` settles `A₁(q)`, `q ≡ 1 (mod 4)`, through the corpus
identification with `PSL₂(𝔽_q)` and `CFSGOutside.HallPaige.hasCompleteMapping_PSL_two_of_mod_four_eq_one`;
together with `CFSGOutside.HallPaige.catalogueCase_A` this gives every entry of type `A`
(`CFSGOutside.HallPaige.catalogueCase_A_all`).
-/

namespace CFSGOutside.HallPaige

open TauCeti

section
variable [h0 : Corpus.Lie.TypeAEquiv]
include h0

/-- **Hall–Paige for `A₁(q)`, `q ≡ 1 (mod 4)`.** -/
theorem catalogueCase_A_one_mod_four (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.A r q).Valid)
    (hr : r = 1) (hq : q.card % 4 = 1) : CatalogueCase (.lie ⟨.A r q, hv⟩) := by
  subst hr
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  intro _ _
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.card :=
    GaloisField.card q.p q.exponent q.exponent_pos.ne'
  exact HasCompleteMapping.of_mulEquiv (Corpus.Lie.linearCatalogCandidateEquivPSL 1 q hv).symm
    (hasCompleteMapping_PSL_two_of_mod_four_eq_one (by rw [hcard]; exact hq))

/-- **Hall–Paige for every catalogue entry of type `A`.** -/
theorem catalogueCase_A_all (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.A r q).Valid) :
    CatalogueCase (.lie ⟨.A r q, hv⟩) := by
  have hr : 1 ≤ r := ((LieTypeIndex.inStandardRange_iff _).1
    ((LieTypeIndex.valid_iff _).1 hv).1).1
  by_cases h : 2 ≤ r ∨ q.p = 2 ∨ q.card % 4 = 3
  · exact catalogueCase_A r q hv h
  · push Not at h
    obtain ⟨h1, h2, h3⟩ := h
    have hodd : Odd q.card := by
      rw [PrimePower.card]
      exact (q.prime_p.eq_two_or_odd'.resolve_left h2).pow
    exact catalogueCase_A_one_mod_four r q hv (by omega) (by
      rcases Nat.odd_iff.1 hodd with h; omega)

end

end CFSGOutside.HallPaige
