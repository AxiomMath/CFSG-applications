import CFSGOutside.HallPaige.Defs

/-!
# Interface statements

Prop-valued statements of the main intermediate results, so that the files proving them and the
files using them can be developed independently. Each `…Statement` is proved (as a theorem named
in its docstring) in the file named there; the final assembly only uses the proved theorems.
-/

namespace CFSGOutside.HallPaige

universe u

open DoubleCoset

/-- **Wilcox, Proposition 14** (generalising Hall–Paige, Theorem 1). If `H ≤ G` has a complete
mapping and there are bijections `x y z : ι ≃ G ⧸ H` (left cosets) with `z i ⊆ x i * y i` for all
`i`, then `G` has a complete mapping. The containment is phrased with representatives.
Proved as `CFSGOutside.HallPaige.hasCompleteMapping_of_cosets` in `results_conditional/CFSGOutside/HallPaige/Cosets.lean`. -/
def CosetStatement : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (H : Subgroup G), HasCompleteMapping H →
    ∀ {ι : Type u} (x y z : ι ≃ G ⧸ H),
      (∀ i, ∃ a b : G, (a : G ⧸ H) = x i ∧ (b : G ⧸ H) = y i ∧ ((a * b : G) : G ⧸ H) = z i) →
      HasCompleteMapping G

/-- **Wilcox–Evans criterion with `φ = id`.** A proper subgroup `H` satisfying the Hall–Paige
condition, and a permutation `ψ` of the double cosets `H \ G / H` preserving their sizes, such that
each `ψ D` meets `D * D`. -/
def WilcoxCriterion (G : Type u) [Group G] : Prop :=
  ∃ H : Subgroup G, H ≠ ⊤ ∧ IsGood H ∧
    ∃ ψ : Quotient (H : Set G) H ≃ Quotient (H : Set G) H,
      (∀ q, Nat.card (quotToDoubleCoset H H (ψ q)) = Nat.card (quotToDoubleCoset H H q)) ∧
      ∀ q, ∃ a b : G, mk H H a = q ∧ mk H H b = q ∧ mk H H (a * b) = ψ q

/-- The hypothesis available inside a minimal counterexample: every proper subgroup satisfying the
Hall–Paige condition has a complete mapping. -/
def ProperSubgroupsAdmissible (G : Type u) [Group G] : Prop :=
  ∀ K : Subgroup G, K ≠ ⊤ → IsGood K → HasCompleteMapping K

/-- **Permutation-labelling form of the Wilcox–Evans criterion** (what the sporadic-group
certificates provide). `ρ` is a transitive action of `G` on `Fin n` with base point `x₀`; `lab`
labels the orbits of the point stabilizer `H`; `σ` permutes the labels preserving orbit sizes; for each
label `k` there are `a, b` with `a•x₀`, `b•x₀` in orbit `k` and `(a*b)•x₀` in orbit `σ k`; `H` is good
and `n ≥ 2`. Proved to imply `WilcoxCriterion G` in `results_conditional/CFSGOutside/HallPaige/DoubleCosets.lean`. -/
def PermLabelling (G : Type u) [Group G] : Prop :=
  ∃ (n : ℕ) (ρ : G →* Equiv.Perm (Fin n)) (x₀ : Fin n) (r : ℕ) (lab : Fin n → Fin r)
    (σ : Equiv.Perm (Fin r)),
    (∀ y, ∃ g, ρ g x₀ = y) ∧
    (∀ y y', lab y = lab y' ↔ ∃ h, ρ h x₀ = x₀ ∧ ρ h y = y') ∧
    (∀ k, Nat.card {y // lab y = σ k} = Nat.card {y // lab y = k}) ∧
    (∀ k, ∃ a b : G, lab (ρ a x₀) = k ∧ lab (ρ b x₀) = k ∧ lab (ρ (a * b) x₀) = σ k) ∧
    IsGood ((MulAction.stabilizer (Equiv.Perm (Fin n)) x₀).comap ρ) ∧
    (∃ y, y ≠ x₀)

end CFSGOutside.HallPaige
