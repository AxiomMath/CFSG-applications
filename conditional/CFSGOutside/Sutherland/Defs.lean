import Mathlib

/-!
# Sutherland, Proposition 5.8: the statistics `χ` and `u`

A. V. Sutherland, *Computing images of Galois representations attached to elliptic curves*, Forum Math. Sigma 4
(2016), e4, arXiv:1504.07618, §5. For `g ∈ GL₂(𝔽_ℓ)` the proposition uses the Legendre symbol `χ(g)` of the
discriminant `tr(g)² - 4 det(g)` and the quantity `u(g) = tr(g)² / det(g)`.
-/

open scoped MatrixGroups

namespace CFSGOutside.Sutherland

variable {K : Type*} [Field K] {ℓ : ℕ} [Fact ℓ.Prime]

/-- The discriminant `tr² - 4 det` of a `2 × 2` matrix (Sutherland 2016, §5). -/
def disc (M : Matrix (Fin 2) (Fin 2) K) : K := M.trace ^ 2 - 4 * M.det

/-- `χ(g) = ((tr(g)² - 4 det(g)) / ℓ)`, the Legendre symbol of the discriminant of `g` (Sutherland 2016, §5). -/
noncomputable def chi (g : GL (Fin 2) (ZMod ℓ)) : ℤ :=
  quadraticChar (ZMod ℓ) (disc (g : Matrix (Fin 2) (Fin 2) (ZMod ℓ)))

/-- `u(g) = tr(g)² / det(g)` (Sutherland 2016, Proposition 5.8). -/
noncomputable def uInv (g : GL (Fin 2) (ZMod ℓ)) : ZMod ℓ :=
  (g : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).trace ^ 2 / (g : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).det

/-- The trace of `g ∈ GL₂(𝔽_ℓ)`. -/
def tr (g : GL (Fin 2) (ZMod ℓ)) : ZMod ℓ := (g : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).trace

/-- `SL₂(𝔽_ℓ)` inside `GL₂(𝔽_ℓ)`. -/
abbrev SL2 (ℓ : ℕ) : Subgroup (GL (Fin 2) (ZMod ℓ)) :=
  (Matrix.SpecialLinearGroup.toGL :
    Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ) →* GL (Fin 2) (ZMod ℓ)).range

end CFSGOutside.Sutherland
