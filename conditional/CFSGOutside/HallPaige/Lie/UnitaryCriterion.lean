import CFSGOutside.HallPaige.Lie.UnitaryPolar

/-!
# The polar-space criterion for `PSU_n`, `n ≥ 4`

Transitivity of `SU_n` on isotropic points, and of the stabilizer of an isotropic point on the
perpendicular and on the non-perpendicular isotropic points; triangles; and the resulting
`CFSGOutside.HallPaige.Unitary.wilcoxCriterion_PSU`.
-/

namespace CFSGOutside.HallPaige.Unitary

open Matrix MulAction Corpus.Lie
open scoped LinearAlgebra.Projectivization

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

/-- Two nonzero vectors pair nontrivially with a common vector. -/
theorem exists_common_herm {b b' : Fin n → K} (hb : b ≠ 0) (hb' : b' ≠ 0) :
    ∃ p : Fin n → K, True ∧ herm σ b p ≠ 0 ∧ herm σ b' p ≠ 0 := by
  obtain ⟨z, hz⟩ := exists_herm_ne_zero σ hb
  obtain ⟨z', hz'⟩ := exists_herm_ne_zero σ hb'
  by_cases h1 : herm σ b' z ≠ 0
  · exact ⟨z, trivial, hz, h1⟩
  by_cases h2 : herm σ b z' ≠ 0
  · exact ⟨z', trivial, h2, hz'⟩
  push Not at h1 h2
  refine ⟨z + z', trivial, ?_, ?_⟩
  · rw [herm_add_right, h2, add_zero]; exact hz
  · rw [herm_add_right, h1, zero_add]; exact hz'

/-- **Moving an isotropic point along a transvection.** If `a, b` are isotropic and
`h(b, a) ≠ 0`, a unitary transvection maps `a` to a nonzero multiple `λ b` of `b` and fixes every
vector perpendicular to `λ b - a`. -/
theorem exists_move (hσ : IsUnitaryInvolution σ) {a b : Fin n → K} (ha : herm σ a a = 0)
    (hb : herm σ b b = 0) (hba : herm σ b a ≠ 0) :
    ∃ (g : SUid σ n) (l : K), l ≠ 0 ∧ g • a = l • b ∧
      ∀ x, herm σ (l • b - a) x = 0 → g • x = x := by
  obtain ⟨t, ht0, ht⟩ := hσ.exists_traceZero
  have hσt : σ t = -t := by linear_combination ht
  set l := σ (t / herm σ b a) with hl
  have hl0 : l ≠ 0 := (map_ne_zero σ).mpr (div_ne_zero ht0 hba)
  have hlba : herm σ (l • b) a = t := by
    rw [herm_smul_left, hl, hσ.invol, div_mul_cancel₀ _ hba]
  have hv : herm σ (l • b - a) (l • b - a) = 0 := by
    have habl : herm σ a (l • b) = σ t := by rw [herm_conj σ hσ.invol, hlba]
    simp only [herm_sub_left, herm_sub_right, hlba, habl, ha]
    rw [herm_smul_left, herm_smul_right, hb, hσt]
    ring
  have hva : herm σ (l • b - a) a = t := by rw [herm_sub_left, hlba, ha, sub_zero]
  have hc : t⁻¹ + σ t⁻¹ = 0 := by rw [map_inv₀, hσt, inv_neg]; ring
  refine ⟨tv hσ.invol hv hc, l, hl0, ?_, fun x hx => ?_⟩
  · rw [tv_smul, hva, inv_mul_cancel₀ ht0, one_smul]
    abel
  · rw [tv_smul, hx, mul_zero, zero_smul, add_zero]

/-- `SU` is transitive on isotropic points. -/
theorem exists_smul_pt_eq (hσ : IsUnitaryInvolution σ) {a b : Fin n → K} (ha0 : a ≠ 0)
    (ha : herm σ a a = 0) (hb0 : b ≠ 0) (hb : herm σ b b = 0) :
    ∃ g : SUid σ n, g • pt a ha0 ha = pt b hb0 hb := by
  by_cases hba : herm σ b a ≠ 0
  · obtain ⟨g, l, hl0, hg, -⟩ := exists_move hσ ha hb hba
    exact ⟨g, by rw [smul_pt]; exact pt_eq_pt_of_smul _ _ _ _ l hg⟩
  push Not at hba
  obtain ⟨d, hd, had, hbd⟩ := exists_cno hσ ha0 ha hb0
  have hda : herm σ d a ≠ 0 := fun h => had (herm_eq_zero_comm σ hσ.invol h)
  obtain ⟨g₁, l₁, hl₁, hg₁, -⟩ := exists_move hσ ha hd hda
  obtain ⟨g₂, l₂, hl₂, hg₂, -⟩ := exists_move hσ hd hb hbd
  refine ⟨g₂ * g₁, ?_⟩
  rw [mul_smul, smul_pt, smul_pt]
  refine pt_eq_pt_of_smul _ _ _ _ (l₁ * l₂) ?_
  rw [hg₁, smul_comm, hg₂, smul_smul]

/-- **The stabilizer of an isotropic vector `a` is transitive on the isotropic points not
perpendicular to `a`.** -/
theorem exists_fix_pt_of_herm_ne_zero (hσ : IsUnitaryInvolution σ) {a b b' : Fin n → K}
    (ha : herm σ a a = 0) (hb0 : b ≠ 0) (hb : herm σ b b = 0) (hb0' : b' ≠ 0)
    (hb' : herm σ b' b' = 0) (hab : herm σ a b ≠ 0) (hab' : herm σ a b' ≠ 0) :
    ∃ g : SUid σ n, g • a = a ∧ g • pt b hb0 hb = pt b' hb0' hb' := by
  obtain ⟨g, hga, hgb⟩ := exists_fix_smul_eq hσ ha hb hb' hab hab'
  exact ⟨g, hga, by rw [smul_pt]; exact pt_eq_pt_of_smul _ _ _ _ _ hgb⟩

/-- **The stabilizer of an isotropic vector `a` is transitive on the isotropic points
perpendicular to `a` and different from `[a]`** (`n ≥ 3`). -/
theorem exists_fix_pt_of_herm_eq_zero (hσ : IsUnitaryInvolution σ) (hn : 3 ≤ n)
    {a b b' : Fin n → K} (ha0 : a ≠ 0) (ha : herm σ a a = 0) (hb0 : b ≠ 0)
    (hb : herm σ b b = 0) (hb0' : b' ≠ 0) (hb' : herm σ b' b' = 0) (hab : herm σ a b = 0)
    (hab' : herm σ a b' = 0) (hba : ∀ c : K, b ≠ c • a) (hba' : ∀ c : K, b' ≠ c • a) :
    ∃ g : SUid σ n, g • a = a ∧ g • pt b hb0 hb = pt b' hb0' hb' := by
  -- partners of `a` perpendicular to `b`, resp. `b'`
  obtain ⟨z, hz, hzb, hza⟩ := exists_isotropic_herm_eq_zero_herm_ne_zero hσ hn ha ha0 hba
  obtain ⟨z', hz', hzb', hza'⟩ := exists_isotropic_herm_eq_zero_herm_ne_zero hσ hn ha ha0 hba'
  have haz : herm σ a z ≠ 0 := fun h => hza (herm_eq_zero_comm σ hσ.invol h)
  have haz' : herm σ a z' ≠ 0 := fun h => hza' (herm_eq_zero_comm σ hσ.invol h)
  obtain ⟨g₁, hg₁a, hg₁z⟩ := exists_fix_smul_eq hσ ha hz hz' haz haz'
  set μ := herm σ a z / herm σ a z' with hμ
  have hμ0 : μ ≠ 0 := div_ne_zero haz haz'
  set b₁ := g₁ • b with hb₁def
  have hb₁0 : b₁ ≠ 0 := (smul_ne_zero_iff_ne g₁).mpr hb0
  have hb₁ : herm σ b₁ b₁ = 0 := by rw [hb₁def, herm_smul_smul, hb]
  have hab₁ : herm σ a b₁ = 0 := by rw [hb₁def, ← hg₁a, herm_smul_smul, hab]
  have hz'b₁ : herm σ z' b₁ = 0 := by
    have h := herm_smul_smul σ g₁ z b
    rw [hg₁z, ← hb₁def, herm_smul_left, hzb] at h
    exact (mul_eq_zero.mp h).resolve_left ((map_ne_zero σ).mpr hμ0)
  have hb₁a : ∀ c : K, b₁ ≠ c • a := by
    intro c hc
    apply hba c
    have := congrArg (g₁⁻¹ • ·) hc
    simp only [hb₁def, inv_smul_smul] at this
    rw [this, smul_comm, ← hg₁a, inv_smul_smul, hg₁a]
  suffices h : ∃ g : SUid σ n, g • a = a ∧ g • pt b₁ hb₁0 hb₁ = pt b' hb0' hb' by
    obtain ⟨g, hga, hgb⟩ := h
    refine ⟨g * g₁, by rw [mul_smul, hg₁a, hga], ?_⟩
    rw [mul_smul, smul_pt]
    exact hgb
  have hb'a : herm σ b' a = 0 := herm_eq_zero_comm σ hσ.invol hab'
  have hb₁a' : herm σ b₁ a = 0 := herm_eq_zero_comm σ hσ.invol hab₁
  by_cases hbb : herm σ b' b₁ ≠ 0
  · obtain ⟨g, l, hl0, hg, hfix⟩ := exists_move hσ hb₁ hb' hbb
    refine ⟨g, hfix a (by rw [herm_sub_left, herm_smul_left, hb'a, hb₁a']; ring), ?_⟩
    rw [smul_pt]; exact pt_eq_pt_of_smul _ _ _ _ l hg
  push Not at hbb
  -- an isotropic `d ⊥ a` pairing nontrivially with `b₁` and `b'`
  set f := (herm σ a z')⁻¹ • z' with hf
  have haf : herm σ a f = 1 := by rw [hf, herm_smul_right, inv_mul_cancel₀ haz']
  have hff : herm σ f f = 0 := by rw [hf, herm_smul_left, herm_smul_right, hz']; ring
  have hfb₁ : herm σ f b₁ = 0 := by rw [hf, herm_smul_left, hz'b₁, mul_zero]
  have hb₁f : herm σ b₁ f = 0 := herm_eq_zero_comm σ hσ.invol hfb₁
  have hb'z : herm σ z' b' = 0 := hzb'
  have hfb' : herm σ f b' = 0 := by rw [hf, herm_smul_left, hb'z, mul_zero]
  have hb'f : herm σ b' f = 0 := herm_eq_zero_comm σ hσ.invol hfb'
  obtain ⟨p, -, hp1, hp2⟩ := exists_common_herm (σ := σ) hb₁0 hb0'
  set q := p - herm σ f p • a - herm σ a p • f with hq
  obtain ⟨haq, -⟩ := herm_proj_pair hσ ha hff haf p
  rw [← hq] at haq
  have hb₁q : herm σ b₁ q = herm σ b₁ p := by
    simp [hq, hb₁a', hb₁f]
  have hb'q : herm σ b' q = herm σ b' p := by
    simp [hq, hb'a, hb'f]
  set q₁ := (herm σ b₁ q)⁻¹ • q with hq₁
  have hb₁q₁ : herm σ b₁ q₁ = 1 := by
    rw [hq₁, herm_smul_right, inv_mul_cancel₀ (by rw [hb₁q]; exact hp1)]
  obtain ⟨c, hc⟩ := exists_isotropize hσ hb₁ hb₁q₁
  set d := q₁ + c • b₁ with hd
  have had : herm σ a d = 0 := by
    rw [hd, herm_add_right, hq₁, herm_smul_right, haq, herm_smul_right, hab₁]; ring
  have hda : herm σ d a = 0 := herm_eq_zero_comm σ hσ.invol had
  have hb₁d : herm σ b₁ d = 1 := by
    rw [hd, herm_add_right, hb₁q₁, herm_smul_right, hb₁, mul_zero, add_zero]
  have hdb₁ : herm σ d b₁ ≠ 0 := by
    rw [herm_conj σ hσ.invol, hb₁d, map_one]; exact one_ne_zero
  have hb'd : herm σ b' d ≠ 0 := by
    rw [hd, herm_add_right, hq₁, herm_smul_right, herm_smul_right, hbb, mul_zero, add_zero,
      hb'q]
    exact mul_ne_zero (inv_ne_zero (by rw [hb₁q]; exact hp1)) hp2
  obtain ⟨g₂, l₂, hl₂, hg₂, hfix₂⟩ := exists_move hσ hb₁ hc hdb₁
  obtain ⟨g₃, l₃, hl₃, hg₃, hfix₃⟩ := exists_move hσ hc hb' hb'd
  refine ⟨g₃ * g₂, ?_, ?_⟩
  · rw [mul_smul, hfix₂ a (by rw [herm_sub_left, herm_smul_left, hda, hb₁a']; ring),
      hfix₃ a (by rw [herm_sub_left, herm_smul_left, hb'a, hda]; ring)]
  · rw [mul_smul, smul_pt, smul_pt]
    refine pt_eq_pt_of_smul _ _ _ _ (l₂ * l₃) ?_
    rw [hg₂, smul_comm, hg₃, smul_smul]

end CFSGOutside.HallPaige.Unitary
