import CFSGOutside.SutherlandSmallEll.Paper
import CFSGOutsideClean.Corpus.DicksonGlTwo
import CFSGOutsideClean.Corpus.Uc22s2112r34PglTameCasesIso

/-!
# Sutherland (2016), Proposition 5.8 for all primes `ℓ ≥ 5`

A. V. Sutherland, Computing images of Galois representations attached to elliptic curves, Forum Math. Sigma 4 (2016), e4, Proposition 5.8. https://doi.org/10.1017/fms.2015.33 The published statement assumes `ℓ > 7`. Dickson's classification is supplied by the corpus.
-/

namespace CFSGOutsideClean.SutherlandSmallEll

open CFSGOutside.Sutherland

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **Sutherland's sufficient criterion for `ℓ ≥ 5`.** Let `ℓ ≥ 5` be prime and `G ≤ GL₂(𝔽_ℓ)`. If `G` contains
elements `g₁, g₂, g₃` of nonzero trace with `χ(g₁) = 1`, `χ(g₂) = -1`, `u(g₃) ∉ {1, 2, 4}` and
`u(g₃)² - 3u(g₃) + 1 ≠ 0`, then `G` contains `SL₂(𝔽_ℓ)`.

Source: A. V. Sutherland, Computing images of Galois representations attached to elliptic curves, Forum Math. Sigma 4 (2016), e4, Proposition 5.8. https://doi.org/10.1017/fms.2015.33 The published statement assumes `ℓ > 7`. -/
theorem sl2_le_of_elements (h5 : 5 ≤ ℓ) (G : Subgroup (GL (Fin 2) (ZMod ℓ)))
    (h : ∃ g₁ ∈ G, ∃ g₂ ∈ G, ∃ g₃ ∈ G, tr g₁ ≠ 0 ∧ tr g₂ ≠ 0 ∧ tr g₃ ≠ 0 ∧
      chi g₁ = 1 ∧ chi g₂ = -1 ∧ uInv g₃ ∉ ({1, 2, 4} : Set (ZMod ℓ)) ∧
      uInv g₃ ^ 2 - 3 * uInv g₃ + 1 ≠ 0) : SL2 ℓ ≤ G :=
  CFSGOutside.SutherlandSmallEll.sl2_le_of_elements h5 G h

/-- Sharpness: for `ℓ = 5, 7` the converse fails, since `SL₂(𝔽_ℓ)` has no element of nonzero trace with
`u ∉ {1, 2, 4}`. -/
theorem no_third_element_in_sl2 (hℓ : ℓ = 5 ∨ ℓ = 7) (g : GL (Fin 2) (ZMod ℓ)) (hg : g ∈ SL2 ℓ)
    (ht : tr g ≠ 0) : uInv g ∈ ({1, 2, 4} : Set (ZMod ℓ)) :=
  CFSGOutside.SutherlandSmallEll.no_third_element_in_sl2 hℓ g hg ht

end CFSGOutsideClean.SutherlandSmallEll
