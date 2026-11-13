import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.DoubleCoset

/-!
# Complete mappings: definitions

A *complete mapping* of a group `G` is a bijection `θ : G → G` such that `x ↦ x * θ x` is also a
bijection. `G` is *good* (satisfies the Hall–Paige condition) if its Sylow 2-subgroups are trivial
or non-cyclic.
-/

namespace CFSGOutside.HallPaige

/-- A complete mapping of `G`: a bijection `θ : G → G` with `x ↦ x * θ x` also a bijection. -/
def IsCompleteMapping {G : Type*} [Mul G] (θ : G → G) : Prop :=
  Function.Bijective θ ∧ Function.Bijective fun x => x * θ x

/-- `G` has a complete mapping (is *admissible*). -/
def HasCompleteMapping (G : Type*) [Mul G] : Prop :=
  ∃ θ : G → G, IsCompleteMapping θ

/-- The Hall–Paige condition: every Sylow 2-subgroup is trivial or non-cyclic. -/
def IsGood (G : Type*) [Group G] : Prop :=
  ∀ P : Sylow 2 G, (P : Subgroup G) = ⊥ ∨ ¬ IsCyclic P

section Basic

universe u
variable {G : Type u} [Group G]

/-- Complete mappings in the "triple" form: bijections `a b c : ι ≃ G` with `a i * b i = c i`. -/
theorem hasCompleteMapping_iff_exists_triple :
    HasCompleteMapping G ↔
      ∃ (ι : Type u) (a b c : ι ≃ G), ∀ i, a i * b i = c i := by
  constructor
  · rintro ⟨θ, hθ, hm⟩
    exact ⟨G, Equiv.refl G, Equiv.ofBijective θ hθ, Equiv.ofBijective _ hm, fun _ => rfl⟩
  · rintro ⟨ι, a, b, c, h⟩
    refine ⟨fun x => b (a.symm x), ?_, ?_⟩
    · exact b.bijective.comp a.symm.bijective
    · have : (fun x => x * b (a.symm x)) = c ∘ a.symm := by
        funext x
        simpa using h (a.symm x)
      rw [this]
      exact c.bijective.comp a.symm.bijective

/-- The triple form with an arbitrary index type in any universe. -/
theorem HasCompleteMapping.of_triple {ι : Type*} (a b c : ι ≃ G) (h : ∀ i, a i * b i = c i) :
    HasCompleteMapping G := by
  refine ⟨fun x => b (a.symm x), b.bijective.comp a.symm.bijective, ?_⟩
  have : (fun x => x * b (a.symm x)) = c ∘ a.symm := by
    funext x
    simpa using h (a.symm x)
  rw [this]
  exact c.bijective.comp a.symm.bijective

/-- Complete mappings transport along isomorphisms. -/
theorem HasCompleteMapping.of_mulEquiv {H : Type*} [Group H] (e : G ≃* H)
    (h : HasCompleteMapping G) : HasCompleteMapping H := by
  obtain ⟨θ, hθ, hm⟩ := h
  refine ⟨fun y => e (θ (e.symm y)), ?_, ?_⟩
  · exact e.bijective.comp (hθ.comp e.symm.bijective)
  · have : (fun y => y * e (θ (e.symm y))) = e ∘ (fun x => x * θ x) ∘ e.symm := by
      funext y
      simp
    rw [this]
    exact e.bijective.comp (hm.comp e.symm.bijective)

/-- A finite group of odd order has a complete mapping: the identity (`x ↦ x²` is bijective). -/
theorem hasCompleteMapping_of_odd [Finite G] (h : Odd (Nat.card G)) : HasCompleteMapping G := by
  refine ⟨id, Function.bijective_id, ?_⟩
  have hcop : (Nat.card G).Coprime 2 := Nat.Coprime.symm (Nat.coprime_two_left.mpr h)
  have : (fun x : G => x * id x) = fun x => x ^ 2 := by
    funext x
    simp [pow_two]
  rw [this]
  exact (powCoprime hcop).bijective

end Basic

end CFSGOutside.HallPaige
