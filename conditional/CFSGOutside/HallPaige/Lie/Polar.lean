import CFSGOutside.HallPaige.DoubleCosets

/-!
# Rank-three actions with a perpendicularity relation

Let `G` act transitively on a finite set `X` with a `G`-invariant relation `R` ("perpendicular"),
so that the stabilizer of a base point `x₀` is transitive on the points `≠ x₀` perpendicular to
`x₀`, and on the points not perpendicular to `x₀`. If both relations contain a triangle through
`x₀` (three distinct mutually perpendicular points; three mutually non-perpendicular points), and
the point stabilizer is good, then `G` satisfies the Wilcox criterion
(`CFSGOutside.HallPaige.wilcoxCriterion_of_polar`). This is the triangle criterion for the action of a
classical group on the points of its polar space.
-/

namespace CFSGOutside.HallPaige

open MulAction

universe u

variable {G : Type u} [Group G] {X : Type*} [MulAction G X]

/-- The three-valued label of a point relative to `x₀`: `0` for `x₀` itself, `1` for the other
points perpendicular to `x₀`, `2` for the points not perpendicular to `x₀`. -/
noncomputable def polarLabel (R : X → X → Prop) (x₀ : X) (y : X) : Fin 3 := by
  classical
  exact if y = x₀ then 0 else if R x₀ y then 1 else 2

/-- **The polar-space criterion.** -/
theorem wilcoxCriterion_of_polar [Finite X] (R : X → X → Prop) (x₀ : X)
    (hrefl : ∀ x, R x x) (hinv : ∀ (g : G) x y, R (g • x) (g • y) ↔ R x y)
    (htrans : ∀ y : X, ∃ g : G, g • x₀ = y)
    (hstab1 : ∀ y y', y ≠ x₀ → y' ≠ x₀ → R x₀ y → R x₀ y' →
      ∃ h : G, h • x₀ = x₀ ∧ h • y = y')
    (hstab2 : ∀ y y', ¬ R x₀ y → ¬ R x₀ y' → ∃ h : G, h • x₀ = x₀ ∧ h • y = y')
    (htri1 : ∃ y z, y ≠ x₀ ∧ z ≠ x₀ ∧ y ≠ z ∧ R x₀ y ∧ R x₀ z ∧ R y z)
    (htri2 : ∃ y z, ¬ R x₀ y ∧ ¬ R x₀ z ∧ ¬ R y z)
    (hgood : IsGood (stabilizer G x₀)) : WilcoxCriterion G := by
  classical
  have hlab_eq : ∀ y, polarLabel R x₀ y = if y = x₀ then 0 else if R x₀ y then 1 else 2 :=
    fun y => by simp only [polarLabel]
  refine wilcoxCriterion_of_labelling_sq x₀ htrans (polarLabel R x₀) ?_ ?_ hgood ?_
  · intro y y'
    constructor
    · intro h
      rw [hlab_eq, hlab_eq] at h
      by_cases hy : y = x₀
      · by_cases hy' : y' = x₀
        · exact ⟨1, Subgroup.one_mem _, by rw [one_smul, hy, hy']⟩
        · simp only [hy, if_true, hy', if_false] at h
          split_ifs at h <;> exact absurd h (by decide)
      · by_cases hy' : y' = x₀
        · simp only [hy, if_false, hy', if_true] at h
          split_ifs at h <;> exact absurd h (by decide)
        · simp only [hy, if_false, hy'] at h
          by_cases hR : R x₀ y
          · have hR' : R x₀ y' := by
              by_contra hR'
              simp [hR, hR'] at h
            obtain ⟨g, hg1, hg2⟩ := hstab1 y y' hy hy' hR hR'
            exact ⟨g, hg1, hg2⟩
          · have hR' : ¬ R x₀ y' := by
              intro hR'
              simp [hR, hR'] at h
            obtain ⟨g, hg1, hg2⟩ := hstab2 y y' hR hR'
            exact ⟨g, hg1, hg2⟩
    · rintro ⟨h, hh, rfl⟩
      rw [mem_stabilizer_iff] at hh
      have h1 : h • y = x₀ ↔ y = x₀ := by
        constructor
        · intro e; rw [← hh] at e; exact smul_left_cancel h e
        · intro e; rw [e, hh]
      have h2 : R x₀ (h • y) ↔ R x₀ y := by
        conv_lhs => rw [← hh]
        exact hinv h x₀ y
      simp only [polarLabel, h1, h2]
  · intro k
    have key : ∀ y z, y ≠ x₀ → z ≠ x₀ → y ≠ z → (R x₀ y ↔ R x₀ z) → (R x₀ z ↔ R y z) →
        ∃ g : G, g • x₀ = y ∧ g • y = z := by
      intro y z hy hz hyz hRyz hRz
      obtain ⟨g₁, hg₁⟩ := htrans y
      have hz' : g₁⁻¹ • z ≠ x₀ := by
        intro e; apply hyz; rw [← hg₁, ← e, smul_inv_smul]
      have hR : R x₀ (g₁⁻¹ • z) ↔ R y z := by
        rw [← hinv g₁, hg₁, smul_inv_smul]
      by_cases hRy : R x₀ y
      · obtain ⟨h, hh1, hh2⟩ := hstab1 y (g₁⁻¹ • z) hy hz' hRy (hR.2 (hRz.1 (hRyz.1 hRy)))
        exact ⟨g₁ * h, by rw [mul_smul, hh1, hg₁], by rw [mul_smul, hh2, smul_inv_smul]⟩
      · have : ¬ R x₀ (g₁⁻¹ • z) := fun h' => hRy (hRyz.2 (hRz.2 (hR.1 h')))
        obtain ⟨h, hh1, hh2⟩ := hstab2 y (g₁⁻¹ • z) hRy this
        exact ⟨g₁ * h, by rw [mul_smul, hh1, hg₁], by rw [mul_smul, hh2, smul_inv_smul]⟩
    fin_cases k
    · exact ⟨1, by simp [polarLabel], by simp [polarLabel]⟩
    · obtain ⟨y, z, hy, hz, hyz, hRy, hRz, hR⟩ := htri1
      obtain ⟨g, hg1, hg2⟩ := key y z hy hz hyz ⟨fun _ => hRz, fun _ => hRy⟩
        ⟨fun _ => hR, fun _ => hRz⟩
      refine ⟨g, ?_, ?_⟩
      · simp [polarLabel, hg1, hy, hRy]
      · rw [mul_smul, hg1, hg2]; simp [polarLabel, hz, hRz]
    · obtain ⟨y, z, hRy, hRz, hR⟩ := htri2
      have hx : ∀ w, ¬ R x₀ w → w ≠ x₀ := fun w hw e => hw (e ▸ hrefl x₀)
      obtain ⟨g, hg1, hg2⟩ := key y z (hx y hRy) (hx z hRz) (fun e => hR (e ▸ hrefl y))
        ⟨fun h => absurd h hRy, fun h => absurd h hRz⟩ ⟨fun h => absurd h hRz, fun h => absurd h hR⟩
      refine ⟨g, ?_, ?_⟩
      · simp [polarLabel, hg1, hx y hRy, hRy]
      · rw [mul_smul, hg1, hg2]; simp [polarLabel, hx z hRz, hRz]
  · obtain ⟨y, -, hy, -⟩ := htri1
    exact ⟨y, hy⟩

end CFSGOutside.HallPaige
