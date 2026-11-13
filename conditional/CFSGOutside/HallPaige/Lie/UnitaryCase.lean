import CFSGOutside.HallPaige.Lie.UnitaryWilcox
import CFSGOutside.HallPaige.Lie.UnitaryFinite
import CFSGOutside.HallPaige.Sporadic.GoodOfKlein
import CFSGOutside.HallPaige.Catalogue
import CFSGOutside.HallPaige.Cosets

/-!
# The catalogue case `²A_r(q)`, `r ≥ 3` (except `r = 3` with `q` odd)

The point stabilizer of `PSU_n(q)` on isotropic points is good: for `q` odd and `n ≥ 5` it contains
the Klein four-group of the sign matrices `diag(-1,-1,1,…)`, `diag(1,1,-1,-1,1,…)`; for `q` even
and `n ≥ 4` it contains two commuting unitary transvections.
-/

namespace CFSGOutside.HallPaige.Unitary

open Matrix MulAction Corpus.Lie TauCeti
open scoped LinearAlgebra.Projectivization

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

/-- An element of `SU` moving some vector `x` by a vector outside `K x` is not a scalar. -/
theorem mk_ne_one_of_smul (g : SUid σ n) {x w : Fin n → K} (hg : g • x = x + w)
    (hw : ∀ c : K, w ≠ c • x) : (g : StatedProj (SUid σ n)) ≠ 1 := by
  rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  rintro ⟨c, hc⟩
  apply hw ((c : K) - 1)
  have : g • x = (c : K) • x := by
    rw [smul_def, ← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    ext k
    simp [Matrix.mulVec_diagonal]
  rw [hg] at this
  rw [sub_smul, one_smul, ← this]
  abel

section Odd

/-- The sign vector `-1` at `i` and `j`. -/
def signU (i j : Fin n) : Fin n → K := fun k => (if k = i then -1 else 1) * (if k = j then -1 else 1)

theorem signU_mul_self (i j : Fin n) : signU (K := K) i j * signU i j = 1 := by
  funext k; simp only [signU, Pi.mul_apply, Pi.one_apply]; split_ifs <;> simp

theorem σ_signU (i j : Fin n) (k : Fin n) : σ (signU (K := K) i j k) = signU i j k := by
  simp only [signU]; split_ifs <;> simp

theorem det_signU {i j : Fin n} (hij : i ≠ j) : (diagonal (signU (K := K) i j)).det = 1 := by
  rw [det_diagonal]
  have : signU (K := K) i j = Pi.mulSingle i (-1) * Pi.mulSingle j (-1) := by
    funext k; simp [signU, Pi.mulSingle_apply]
  rw [this]
  simp only [Pi.mul_apply, Finset.prod_mul_distrib, Finset.prod_pi_mulSingle', Finset.mem_univ,
    if_true]
  norm_num

theorem herm_signU (i j : Fin n) (x y : Fin n → K) :
    herm σ (diagonal (signU i j) *ᵥ x) (diagonal (signU i j) *ᵥ y) = herm σ x y := by
  rw [herm_def, herm_def]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [mulVec_diagonal, map_mul, σ_signU]
  have := congrFun (signU_mul_self (K := K) i j) k
  simp only [Pi.mul_apply, Pi.one_apply] at this
  linear_combination σ (x k) * y k * this

/-- The sign element of `SU`. -/
noncomputable def signSU {i j : Fin n} (hij : i ≠ j) : SUid σ n :=
  mkSU σ (diagonal (signU i j)) (det_signU hij) (herm_signU i j)

theorem signSU_smul {i j : Fin n} (hij : i ≠ j) (x : Fin n → K) :
    signSU (σ := σ) hij • x = diagonal (signU i j) *ᵥ x := rfl

theorem signSU_mul_self {i j : Fin n} (hij : i ≠ j) : signSU (σ := σ) hij * signSU hij = 1 := by
  apply ext_smul; intro x
  rw [mul_smul, signSU_smul, signSU_smul, mulVec_mulVec, diagonal_mul_diagonal', one_smul]
  funext k
  rw [mulVec_diagonal]
  have := congrFun (signU_mul_self (K := K) i j) k
  simp only [Pi.mul_apply, Pi.one_apply] at this
  rw [this, one_mul]

theorem signSU_comm {i j i' j' : Fin n} (hij : i ≠ j) (hij' : i' ≠ j') :
    signSU (σ := σ) hij * signSU hij' = signSU hij' * signSU hij := by
  apply ext_smul; intro x
  rw [mul_smul, mul_smul, signSU_smul, signSU_smul, signSU_smul, signSU_smul, mulVec_mulVec,
    mulVec_mulVec, diagonal_mul_diagonal', diagonal_mul_diagonal']
  congr 2
  funext k; exact mul_comm _ _

end Odd

/-- For `q` odd and `n ≥ 5` the stabilizer of the base point is good. -/
theorem isGood_stabilizer_basePtU_of_odd [Finite K] (hn : 5 ≤ n) {u : K} (hu : σ u * u = -1)
    (hK : (-1 : K) ≠ 1) :
    IsGood (stabilizer (StatedProj (SUid σ n)) (basePtU (σ := σ) (n := n) (by omega) hu)) := by
  have hn2 : 2 ≤ n := by omega
  set i₀ : Fin n := ⟨0, by omega⟩
  set i₁ : Fin n := ⟨1, by omega⟩
  set i₂ : Fin n := ⟨2, by omega⟩
  set i₃ : Fin n := ⟨3, by omega⟩
  set i₄ : Fin n := ⟨4, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have h23 : i₂ ≠ i₃ := by simp [i₂, i₃, Fin.ext_iff]
  set D₁ := signSU (σ := σ) h01
  set D₂ := signSU (σ := σ) h23
  have hsign : ∀ {i j : Fin n} (hij : i ≠ j) (k : Fin n), signU (K := K) i j k =
      (if k = i then -1 else 1) * (if k = j then -1 else 1) := fun _ _ => rfl
  -- both fix the base point
  have hfix : ∀ (D : SUid σ n) (c : K), c ≠ 0 →
      D • baseVec (K := K) hn2 u = c • baseVec hn2 u →
      (D : StatedProj (SUid σ n)) • basePtU (σ := σ) hn2 hu = basePtU hn2 hu := by
    intro D c hc hD
    rw [psu_smul, basePtU, smul_pt]
    exact pt_eq_pt_of_smul _ _ _ _ c hD
  have hbase : baseVec (K := K) hn2 u = Pi.single i₀ 1 + Pi.single i₁ u := rfl
  have hD₁ : D₁ • baseVec (K := K) hn2 u = (-1 : K) • baseVec hn2 u := by
    rw [signSU_smul, hbase]
    funext k
    rw [mulVec_diagonal]; simp only [signU]
    by_cases hk0 : k = i₀
    · subst hk0; simp [Pi.single_apply, h01]
    · by_cases hk1 : k = i₁
      · subst hk1; simp [Pi.single_apply, Ne.symm h01]
      · simp [Pi.single_apply, hk0, hk1]
  have hD₂ : D₂ • baseVec (K := K) hn2 u = (1 : K) • baseVec hn2 u := by
    rw [signSU_smul, hbase, one_smul]
    funext k
    rw [mulVec_diagonal]; simp only [signU]
    by_cases hk0 : k = i₀
    · subst hk0; simp [Pi.single_apply, i₂, i₃, i₀, Fin.ext_iff]
    · by_cases hk1 : k = i₁
      · subst hk1; simp [Pi.single_apply, i₂, i₃, i₁, Fin.ext_iff]
      · simp [Pi.single_apply, hk0, hk1]
  -- non-scalar: `D • e_k = s_k e_k` with distinct signs
  have hns : ∀ (D : SUid σ n) (a b : Fin n) (sa sb : K), a ≠ b → sa ≠ sb →
      D • (Pi.single a 1 : Fin n → K) = sa • Pi.single a 1 →
      D • (Pi.single b 1 : Fin n → K) = sb • Pi.single b 1 → (D : StatedProj (SUid σ n)) ≠ 1 := by
    intro D a b sa sb hab hs ha hb
    rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
    rintro ⟨c, hc⟩
    have hsc : ∀ v : Fin n → K, D • v = (c : K) • v := by
      intro v
      rw [smul_def, ← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
      ext k
      simp [Matrix.mulVec_diagonal]
    have h1 := congrFun ((hsc _).symm.trans ha) a
    have h2 := congrFun ((hsc _).symm.trans hb) b
    simp at h1 h2
    exact hs (h1.symm.trans h2)
  have hDe : ∀ {i j : Fin n} (hij : i ≠ j) (k : Fin n),
      signSU (σ := σ) hij • (Pi.single k 1 : Fin n → K) = signU (K := K) i j k • (Pi.single k 1 : Fin n → K) := by
    intro i j hij k
    rw [signSU_smul]
    funext l
    rw [mulVec_diagonal]
    by_cases hl : l = k
    · subst hl; simp
    · simp [Pi.single_apply, hl]
  have hval : ∀ {i j : Fin n} (k : Fin n), k = i → k ≠ j → signU (K := K) i j k = -1 := by
    intro i j k hki hkj; simp [signU, hki, hki ▸ hkj]
  have hval1 : ∀ {i j : Fin n} (k : Fin n), k ≠ i → k ≠ j → signU (K := K) i j k = 1 := by
    intro i j k hki hkj; simp [signU, hki, hkj]
  have h02 : i₀ ≠ i₂ := by simp [i₀, i₂, Fin.ext_iff]
  have h03 : i₀ ≠ i₃ := by simp [i₀, i₃, Fin.ext_iff]
  have h04 : i₀ ≠ i₄ := by simp [i₀, i₄, Fin.ext_iff]
  have h14 : i₁ ≠ i₄ := by simp [i₁, i₄, Fin.ext_iff]
  have h24 : i₂ ≠ i₄ := by simp [i₂, i₄, Fin.ext_iff]
  have h34 : i₃ ≠ i₄ := by simp [i₃, i₄, Fin.ext_iff]
  have hu1 : (D₁ : StatedProj (SUid σ n)) ≠ 1 :=
    hns D₁ i₀ i₄ (-1) 1 h04 hK (by rw [hDe, hval i₀ rfl h01]) (by rw [hDe, hval1 i₄ h04.symm h14.symm])
  have hv1 : (D₂ : StatedProj (SUid σ n)) ≠ 1 :=
    hns D₂ i₂ i₄ (-1) 1 h24 hK (by rw [hDe, hval i₂ rfl h23]) (by rw [hDe, hval1 i₄ h24.symm h34.symm])
  have huv : (D₁ : StatedProj (SUid σ n)) ≠ D₂ := by
    rw [Ne, QuotientGroup.eq]
    have hinv : D₁⁻¹ = D₁ := inv_eq_of_mul_eq_one_right (signSU_mul_self h01)
    rw [hinv]
    refine fun h => hns (D₁ * D₂) i₀ i₄ (-1) 1 h04 hK ?_ ?_ ((QuotientGroup.eq_one_iff _).2 h)
    · rw [mul_smul, hDe, smul_comm, hDe, hval1 i₀ h02 h03, one_smul, hval i₀ rfl h01]
    · rw [mul_smul, hDe, smul_comm, hDe, hval1 i₄ h24.symm h34.symm, one_smul,
        hval1 i₄ h04.symm h14.symm]
  refine Subgroup.isGood_of_commuting_involutions _ (u := (D₁ : StatedProj (SUid σ n)))
    (v := D₂) (hfix D₁ (-1) (by simpa using hK) hD₁) (hfix D₂ 1 one_ne_zero hD₂) ?_ ?_ ?_
    hu1 hv1 huv
  · rw [sq, ← QuotientGroup.mk_mul, signSU_mul_self, QuotientGroup.mk_one]
  · rw [sq, ← QuotientGroup.mk_mul, signSU_mul_self, QuotientGroup.mk_one]
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, signSU_comm]

/-- For `q` even and `n ≥ 4` the stabilizer of the base point is good: two commuting unitary
transvections. -/
theorem isGood_stabilizer_basePtU_of_two [Finite K] (hσ : IsUnitaryInvolution σ) (hn : 4 ≤ n)
    {u : K} (hu : σ u * u = -1) (h2 : (2 : K) = 0) :
    IsGood (stabilizer (StatedProj (SUid σ n)) (basePtU (σ := σ) (n := n) (by omega) hu)) := by
  have hn2 : 2 ≤ n := by omega
  set i₀ : Fin n := ⟨0, by omega⟩
  set i₁ : Fin n := ⟨1, by omega⟩
  set i₂ : Fin n := ⟨2, by omega⟩
  set i₃ : Fin n := ⟨3, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have h02 : i₀ ≠ i₂ := by simp [i₀, i₂, Fin.ext_iff]
  have h03 : i₀ ≠ i₃ := by simp [i₀, i₃, Fin.ext_iff]
  have h12 : i₁ ≠ i₂ := by simp [i₁, i₂, Fin.ext_iff]
  have h13 : i₁ ≠ i₃ := by simp [i₁, i₃, Fin.ext_iff]
  have h23 : i₂ ≠ i₃ := by simp [i₂, i₃, Fin.ext_iff]
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  set a₀ : Fin n → K := Pi.single i₀ 1 + Pi.single i₁ u with ha₀def
  have hbase : baseVec (K := K) hn2 u = a₀ := rfl
  set b₀ : Fin n → K := Pi.single i₂ 1 + Pi.single i₃ u with hb₀def
  have ha₀ : herm σ a₀ a₀ = 0 := by rw [← hbase]; exact herm_baseVec hn2 hu
  have hb₀ : herm σ b₀ b₀ = 0 := by
    rw [hb₀def, herm_single_add_single_self h23, hu]; ring
  have hab : herm σ a₀ b₀ = 0 := by
    rw [ha₀def, hb₀def, herm_two_two]
    simp [Pi.single_apply, h02, h03, h12, h13]
  have hba : herm σ b₀ a₀ = 0 := herm_eq_zero_comm σ hσ.invol hab
  set v₂ := a₀ + b₀ with hv₂def
  have hv₂ : herm σ v₂ v₂ = 0 := by
    simp only [hv₂def, herm_add_left, herm_add_right, ha₀, hb₀, hab, hba, add_zero]
  have hb₀v₂ : herm σ b₀ v₂ = 0 := by rw [hv₂def, herm_add_right, hba, hb₀, add_zero]
  have hv₂b₀ : herm σ v₂ b₀ = 0 := herm_eq_zero_comm σ hσ.invol hb₀v₂
  have hv₂a₀ : herm σ v₂ a₀ = 0 := by rw [hv₂def, herm_add_left, ha₀, hba, add_zero]
  have hc : (1 : K) + σ 1 = 0 := by rw [map_one, one_add_one_eq_two, h2]
  set T₁ := tv hσ.invol hb₀ hc
  set T₂ := tv hσ.invol hv₂ hc
  have hsq : ∀ {v : Fin n → K} (hv : herm σ v v = 0), tv hσ.invol hv hc * tv hσ.invol hv hc = 1 := by
    intro v hv
    apply ext_smul; intro x
    rw [mul_smul, tv_smul, tv_smul, one_smul, herm_add_right, herm_smul_right, hv, mul_zero,
      add_zero, add_assoc, ← add_smul, ← two_mul, h2, zero_mul, zero_smul, add_zero]
  have hcomm : T₁ * T₂ = T₂ * T₁ := by
    apply ext_smul; intro x
    rw [mul_smul, mul_smul, tv_smul, tv_smul, tv_smul, tv_smul, herm_add_right,
      herm_add_right, herm_smul_right, herm_smul_right, hb₀v₂, hv₂b₀]
    simp only [mul_zero, add_zero]
    abel
  have hfix : ∀ (T : SUid σ n), T • a₀ = a₀ →
      (T : StatedProj (SUid σ n)) • basePtU (σ := σ) hn2 hu = basePtU hn2 hu := by
    intro T hT
    rw [psu_smul, basePtU, smul_pt]
    exact pt_eq_pt_of_smul _ _ _ _ 1 (by rw [hbase, one_smul]; exact hT)
  have hT₁a : T₁ • a₀ = a₀ := by rw [tv_smul, hba, mul_zero, zero_smul, add_zero]
  have hT₂a : T₂ • a₀ = a₀ := by rw [tv_smul, hv₂a₀, mul_zero, zero_smul, add_zero]
  have hT₁ : (T₁ : StatedProj (SUid σ n)) ≠ 1 := by
    refine mk_ne_one_of_smul T₁ (x := Pi.single i₂ 1) (w := b₀) ?_ ?_
    · rw [tv_smul, herm_single_right]
      simp [hb₀def, Pi.single_apply, h23]
    · intro c hc'
      have := congrFun hc' i₃
      simp [hb₀def, Pi.single_apply, h23, Ne.symm h23] at this
      exact hu0 this
  have hT₂ : (T₂ : StatedProj (SUid σ n)) ≠ 1 := by
    refine mk_ne_one_of_smul T₂ (x := Pi.single i₀ 1) (w := v₂) ?_ ?_
    · rw [tv_smul, herm_single_right]
      simp [hv₂def, ha₀def, hb₀def, Pi.single_apply, h01, h02, h03]
    · intro c hc'
      have := congrFun hc' i₂
      simp [hv₂def, ha₀def, hb₀def, Pi.single_apply, h02, h12, Ne.symm h02, Ne.symm h12,
        h23] at this
  have hT₁₂ : (T₁ : StatedProj (SUid σ n)) ≠ T₂ := by
    rw [Ne, QuotientGroup.eq]
    have hinv : T₁⁻¹ = T₁ := inv_eq_of_mul_eq_one_right (hsq hb₀)
    rw [hinv]
    intro h
    refine mk_ne_one_of_smul (T₁ * T₂) (x := Pi.single i₀ 1 + Pi.single i₂ 1) (w := b₀) ?_ ?_
      ((QuotientGroup.eq_one_iff _).2 h)
    · have hx2 : herm σ v₂ (Pi.single i₀ 1 + Pi.single i₂ 1) = 0 := by
        rw [herm_add_right, herm_single_right, herm_single_right]
        simp [hv₂def, ha₀def, hb₀def, Pi.single_apply, h01, h02, h03, Ne.symm h02,
          Ne.symm h12, h23, one_add_one_eq_two, h2]
      have hx1 : herm σ b₀ (Pi.single i₀ 1 + Pi.single i₂ 1) = 1 := by
        rw [herm_add_right, herm_single_right, herm_single_right]
        simp [hb₀def, Pi.single_apply, h02, h03, h23]
      have hT2x : T₂ • (Pi.single i₀ 1 + Pi.single i₂ 1 : Fin n → K) =
          Pi.single i₀ 1 + Pi.single i₂ 1 := by
        rw [tv_smul, hx2, mul_zero, zero_smul, add_zero]
      rw [mul_smul, hT2x, tv_smul, hx1, one_mul, one_smul]
    · intro c hc'
      have := congrFun hc' i₃
      simp [hb₀def, Pi.single_apply, h03, h23, Ne.symm h03, Ne.symm h23] at this
      exact hu0 this
  refine Subgroup.isGood_of_commuting_involutions _ (u := (T₁ : StatedProj (SUid σ n)))
    (v := T₂) (hfix T₁ hT₁a) (hfix T₂ hT₂a) ?_ ?_ ?_ hT₁ hT₂ hT₁₂
  · rw [sq, ← QuotientGroup.mk_mul, hsq hb₀, QuotientGroup.mk_one]
  · rw [sq, ← QuotientGroup.mk_mul, hsq hv₂, QuotientGroup.mk_one]
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm]

/-- **Hall–Paige for `PSU_n`, `n ≥ 4`, `q` even or `n ≥ 5`.** -/
theorem hasCompleteMapping_PSU [Finite K] (hσ : IsUnitaryInvolution σ) (hn : 4 ≤ n)
    (hcase : (2 : K) = 0 ∨ 5 ≤ n) (hG : IsGood (StatedProj (SUid σ n)))
    (hP : ProperSubgroupsAdmissible (StatedProj (SUid σ n))) :
    HasCompleteMapping (StatedProj (SUid σ n)) := by
  obtain ⟨u, hu⟩ := hσ.exists_norm_neg_one
  refine hasCompleteMapping_of_wilcoxCriterion cosetStatement (wilcoxCriterion_PSU hσ hn hu ?_) hP
  by_cases h2 : (2 : K) = 0
  · exact isGood_stabilizer_basePtU_of_two hσ hn hu h2
  · refine isGood_stabilizer_basePtU_of_odd (hcase.resolve_left h2) hu ?_
    intro h
    apply h2
    linear_combination -h

end CFSGOutside.HallPaige.Unitary
