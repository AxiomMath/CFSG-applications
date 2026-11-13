import Mathlib

/-!
# Definitions for Gagola's Theorem 4.5

`SylowAb X`: for every prime `p` with `p ^ 6 ∣ |X|`, every Sylow `p`-subgroup of `X` is abelian.
-/

namespace CFSGOutside.Gagola

/-- The hypothesis of Gagola's Theorem 4.5 on a group `X`. -/
def SylowAb (X : Type*) [Group X] : Prop :=
  ∀ p : ℕ, p.Prime → p ^ 6 ∣ Nat.card X → ∀ P : Sylow p X, IsMulCommutative (P : Subgroup X)

end CFSGOutside.Gagola
