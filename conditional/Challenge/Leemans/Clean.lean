import CFSGOutside.Corpus.Defs.OuterAutomorphisms
import CFSGOutside.Corpus.Defs.Suzuki
import CFSGOutside.Leemans.Defs

/-!
# Leemans (2006), Theorem 1 (clean path)

D. Leemans, *Almost simple groups of Suzuki type acting on polytopes*, Proc. Amer. Math. Soc. **134** (2006),
3649–3651. Let `Sz(q) ≤ G ≤ Aut(Sz(q))` with `q = 2 ^ (2e+1)`, `e > 0`. Then `G` is a C-group if and only if
`G = Sz(q)`; moreover a string C-group representation of `G` has rank `3`.
No hypothesis on the corpus: the clean build proves it from the corpus theorems.
-/

open CFSGOutside.Corpus (suzukiGroup)
open CFSGOutside.Corpus.ComponentClassification
open CFSGOutside.Leemans (IsCGroup IsStringCGroup)

namespace CFSGOutsideClean.Leemans

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem eq_inner_of_closure_involutions
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (G : Subgroup (MulAut (suzukiGroup a K))) (hG : OuterAutomorphisms.inner (suzukiGroup a K) ≤ G)
    (X : Set (MulAut (suzukiGroup a K))) (hX : ∀ x ∈ X, orderOf x = 2)
    (hgen : Subgroup.closure X = G) : G = OuterAutomorphisms.inner (suzukiGroup a K) := sorry

theorem leemans_suzuki (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (G : Subgroup (MulAut (suzukiGroup a K))) (hG : OuterAutomorphisms.inner (suzukiGroup a K) ≤ G)
    {n : ℕ} (ρ : Fin n → G) (hρ : IsStringCGroup ρ) :
    G = OuterAutomorphisms.inner (suzukiGroup a K) ∧ n = 3 := sorry

theorem exists_isStringCGroup_inner (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ ρ : Fin 3 → OuterAutomorphisms.inner (suzukiGroup a K), IsStringCGroup ρ := sorry

theorem leemans_theorem_1 (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (G : Subgroup (MulAut (suzukiGroup a K))) (hG : OuterAutomorphisms.inner (suzukiGroup a K) ≤ G) :
    ((∃ (n : ℕ) (ρ : Fin n → G), IsCGroup ρ) ↔ G = OuterAutomorphisms.inner (suzukiGroup a K)) ∧
      ((∃ (n : ℕ) (ρ : Fin n → G), IsStringCGroup ρ) ↔ G = OuterAutomorphisms.inner (suzukiGroup a K)) ∧
      ∀ (n : ℕ) (ρ : Fin n → G), IsStringCGroup ρ → n = 3 := sorry

end CFSGOutsideClean.Leemans
