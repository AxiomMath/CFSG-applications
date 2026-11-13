import Mathlib

/-!
# Kimmerle–Konovalov: definitions used by the statements

The definitions of `CFSGOutside/KimmerleKonovalov/Paper.lean` that Corollary 2.6 mentions: the normalised unit
group `V(ℤG)` and the prime graph. See `Paper.lean` for the paper.
-/

noncomputable section

open MonoidAlgebra Finset

namespace KimmerleKonovalov

open scoped Classical

/-! ## Definitions -/

section Defs

variable (G : Type*) [Group G]

/-- The augmentation map `ℤG → ℤ`. -/
def aug : MonoidAlgebra ℤ G →+* ℤ := (MonoidAlgebra.lift ℤ ℤ G 1).toRingHom

/-- The normalised unit group `V(ℤG)`: units of augmentation one. -/
def V : Subgroup (MonoidAlgebra ℤ G)ˣ := (Units.map (aug G).toMonoidHom).ker

/-- The partial augmentation `ε_x(a)`: the sum of the coefficients of `a` on the class `x^G`. -/
def partialAug [Fintype G] (x : G) (a : MonoidAlgebra ℤ G) : ℤ :=
  ∑ g with IsConj g x, a.coeff g

end Defs

/-- `H` has an element of order `n`. -/
def HasEltOfOrder (H : Type*) [Monoid H] (n : ℕ) : Prop := ∃ h : H, orderOf h = n

/-- `p` is a vertex of the prime graph `Π(H)`. -/
def IsVertex (H : Type*) [Monoid H] (p : ℕ) : Prop := p.Prime ∧ HasEltOfOrder H p

/-- `p` and `q` are joined by an edge in the prime graph `Π(H)`. -/
def IsAdj (H : Type*) [Monoid H] (p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p ≠ q ∧ HasEltOfOrder H (p * q)

/-- The prime graph question (PQ) for `G`: `Π(V(ℤG)) = Π(G)`. -/
def PQ (G : Type*) [Group G] : Prop :=
  (∀ p, IsVertex (V G) p ↔ IsVertex G p) ∧ ∀ p q, IsAdj (V G) p q ↔ IsAdj G p q

end KimmerleKonovalov
