import Mathlib

/-!
# Two primes with nontrivial cyclic Sylow subgroups

`TwoCyclicPrimes X` says that two distinct primes have nontrivial cyclic Sylow subgroups in `X`. By
Gagola's Theorem 2.5(a) (`thm_2_5_a`), this is impossible for a simple quotient `H/K` of a fully ramified
triple.
-/

namespace CFSGOutside.Gagola

/-- Two distinct primes `p ≠ r` such that every Sylow `p`-subgroup and every Sylow `r`-subgroup of `X` is
cyclic and nontrivial. -/
def TwoCyclicPrimes (X : Type*) [Group X] : Prop :=
  ∃ p r : ℕ, ∃ _ : Fact p.Prime, ∃ _ : Fact r.Prime, p ≠ r ∧
    (∀ P : Sylow p X, IsCyclic (P : Subgroup X) ∧ Nat.card P ≠ 1) ∧
    (∀ P : Sylow r X, IsCyclic (P : Subgroup X) ∧ Nat.card P ≠ 1)

theorem TwoCyclicPrimes.of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] (φ : X ≃* Y)
    (h : TwoCyclicPrimes Y) : TwoCyclicPrimes X := by
  obtain ⟨p, r, hp, hr, hpr, h1, h2⟩ := h
  have key : ∀ {q : ℕ} [Fact q.Prime], (∀ P : Sylow q Y, IsCyclic (P : Subgroup Y) ∧ Nat.card P ≠ 1) →
      ∀ P : Sylow q X, IsCyclic (P : Subgroup X) ∧ Nat.card P ≠ 1 := by
    intro q _ h P
    let P' := P.mapSurjective (f := φ.toMonoidHom) φ.surjective
    obtain ⟨hc, hn⟩ := h P'
    have hP' : (P' : Subgroup Y) = (P : Subgroup X).map φ.toMonoidHom := Sylow.coe_mapSurjective _ _
    have hc' : IsCyclic ((P : Subgroup X).map φ.toMonoidHom) := hP' ▸ hc
    have hinj : Function.Injective (φ.toMonoidHom.subgroupMap (P : Subgroup X)) := fun a b hab =>
      Subtype.ext (φ.injective (congrArg Subtype.val hab))
    refine ⟨isCyclic_of_injective _ hinj, ?_⟩
    rwa [hP', Subgroup.card_map_of_injective φ.injective] at hn
  exact ⟨p, r, hp, hr, hpr, key h1, key h2⟩

end CFSGOutside.Gagola
