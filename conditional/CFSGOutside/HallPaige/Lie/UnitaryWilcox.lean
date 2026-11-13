import CFSGOutside.HallPaige.Lie.UnitaryCriterion
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# The Wilcox criterion for `PSU_n`, `n ≥ 4`, up to the goodness of the point stabilizer

The base point is `x₀ = [e₀ + u e₁]` with `σ(u) u = -1`.
-/

namespace CFSGOutside.HallPaige.Unitary

open Matrix MulAction Corpus.Lie
open scoped LinearAlgebra.Projectivization

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

/-- The hermitian product of two "two-term" vectors. -/
theorem herm_two_two (i j k l : Fin n) (a b c d : K) :
    herm σ (Pi.single i a + Pi.single j b) (Pi.single k c + Pi.single l d) =
      σ a * (Pi.single k c + Pi.single l d : Fin n → K) i +
        σ b * (Pi.single k c + Pi.single l d : Fin n → K) j := by
  rw [herm_add_left, herm_single_left, herm_single_left]

/-- An isotropic vector supported on two coordinates. -/
theorem herm_single_add_single_self {i j : Fin n} (hij : i ≠ j) (t : K) :
    herm σ (Pi.single i 1 + Pi.single j t) (Pi.single i 1 + Pi.single j t) = 1 + σ t * t := by
  rw [herm_two_two]
  simp [Pi.single_apply, hij, Ne.symm hij]

theorem single_add_single_ne_zero {i j : Fin n} (hij : i ≠ j) (t : K) :
    (Pi.single i 1 + Pi.single j t : Fin n → K) ≠ 0 := by
  intro h
  have := congrFun h i
  simp [Pi.single_apply, hij] at this

/-- The base vector `e₀ + u e₁`. -/
noncomputable def baseVec (hn : 2 ≤ n) (u : K) : Fin n → K :=
  Pi.single ⟨0, by omega⟩ 1 + Pi.single ⟨1, hn⟩ u

theorem baseVec_ne_zero (hn : 2 ≤ n) (u : K) : baseVec (K := K) hn u ≠ 0 :=
  single_add_single_ne_zero (by simp [Fin.ext_iff]) u

theorem herm_baseVec (hn : 2 ≤ n) {u : K} (hu : σ u * u = -1) :
    herm σ (baseVec hn u) (baseVec hn u) = 0 := by
  rw [baseVec, herm_single_add_single_self (by simp [Fin.ext_iff]), hu]; ring

/-- The base point. -/
noncomputable def basePtU (hn : 2 ≤ n) {u : K} (hu : σ u * u = -1) : isoPts σ n :=
  pt (baseVec hn u) (baseVec_ne_zero hn u) (herm_baseVec hn hu)

theorem ne_smul_of_pt_ne {a w : Fin n → K} (ha0 : a ≠ 0) (ha : herm σ a a = 0) (hw0 : w ≠ 0)
    (hw : herm σ w w = 0) (h : pt w hw0 hw ≠ pt a ha0 ha) : ∀ c : K, w ≠ c • a := by
  intro c hc
  apply h
  exact pt_eq_pt_of_smul _ _ _ _ c hc

/-- **The polar-space criterion for `PSU_n`, `n ≥ 4`.** -/
theorem wilcoxCriterion_PSU [Finite K] (hσ : IsUnitaryInvolution σ) (hn : 4 ≤ n) {u : K}
    (hu : σ u * u = -1)
    (hgood : IsGood (stabilizer (StatedProj (SUid σ n)) (basePtU (σ := σ) (n := n) (by omega) hu))) :
    WilcoxCriterion (StatedProj (SUid σ n)) := by
  have hn2 : 2 ≤ n := by omega
  set a₀ := baseVec (K := K) hn2 u with ha₀def
  have ha₀0 : a₀ ≠ 0 := baseVec_ne_zero hn2 u
  have ha₀ : herm σ a₀ a₀ = 0 := herm_baseVec hn2 hu
  have hx₀ : basePtU (σ := σ) hn2 hu = pt a₀ ha₀0 ha₀ := rfl
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin n := ⟨1, by omega⟩ with hi₁
  set i₂ : Fin n := ⟨2, by omega⟩ with hi₂
  set i₃ : Fin n := ⟨3, by omega⟩ with hi₃
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have h02 : i₀ ≠ i₂ := by simp [i₀, i₂, Fin.ext_iff]
  have h03 : i₀ ≠ i₃ := by simp [i₀, i₃, Fin.ext_iff]
  have h12 : i₁ ≠ i₂ := by simp [i₁, i₂, Fin.ext_iff]
  have h13 : i₁ ≠ i₃ := by simp [i₁, i₃, Fin.ext_iff]
  have h23 : i₂ ≠ i₃ := by simp [i₂, i₃, Fin.ext_iff]
  have ha₀eq : a₀ = Pi.single i₀ 1 + Pi.single i₁ u := rfl
  have : Finite (isoPts σ n) := by
    have : Finite (ℙ K (Fin n → K)) := inferInstance
    exact Subtype.finite
  refine wilcoxCriterion_of_polar perpU (basePtU hn2 hu) perpU_refl perpU_psu_smul ?_ ?_ ?_ ?_ ?_
    hgood
  · intro y
    induction y using isoPts_ind with
    | h w hw hiso =>
    obtain ⟨g, hg⟩ := exists_smul_pt_eq hσ ha₀0 ha₀ hw hiso
    exact ⟨g, by rw [psu_smul, hx₀, hg]⟩
  · intro y y' hy hy' hRy hRy'
    induction y using isoPts_ind with
    | h w hw hiso =>
    induction y' using isoPts_ind with
    | h w' hw' hiso' =>
    rw [hx₀, perpU_pt] at hRy hRy'
    rw [hx₀] at hy hy'
    obtain ⟨g, hga, hgw⟩ := exists_fix_pt_of_herm_eq_zero hσ (by omega) ha₀0 ha₀ hw hiso hw'
      hiso' hRy hRy' (ne_smul_of_pt_ne ha₀0 ha₀ hw hiso hy) (ne_smul_of_pt_ne ha₀0 ha₀ hw' hiso' hy')
    refine ⟨g, ?_, by rw [psu_smul, hgw]⟩
    rw [psu_smul, hx₀, smul_pt]
    exact pt_eq_pt_of_smul _ _ _ _ 1 (by rw [hga, one_smul])
  · intro y y' hRy hRy'
    induction y using isoPts_ind with
    | h w hw hiso =>
    induction y' using isoPts_ind with
    | h w' hw' hiso' =>
    rw [hx₀, perpU_pt] at hRy hRy'
    obtain ⟨g, hga, hgw⟩ := exists_fix_pt_of_herm_ne_zero hσ ha₀ hw hiso hw' hiso' hRy hRy'
    refine ⟨g, ?_, by rw [psu_smul, hgw]⟩
    rw [psu_smul, hx₀, smul_pt]
    exact pt_eq_pt_of_smul _ _ _ _ 1 (by rw [hga, one_smul])
  · -- the perpendicular triangle `[a₀], [b₀], [a₀ + b₀]`
    set b₀ : Fin n → K := Pi.single i₂ 1 + Pi.single i₃ u with hb₀def
    have hb₀0 : b₀ ≠ 0 := single_add_single_ne_zero h23 u
    have hb₀ : herm σ b₀ b₀ = 0 := by
      rw [hb₀def, herm_single_add_single_self h23, hu]; ring
    have hab : herm σ a₀ b₀ = 0 := by
      rw [ha₀eq, hb₀def, herm_two_two]
      simp [Pi.single_apply, h02, h03, h12, h13]
    have hba : herm σ b₀ a₀ = 0 := herm_eq_zero_comm σ hσ.invol hab
    have hs : herm σ (a₀ + b₀) (a₀ + b₀) = 0 := by
      simp only [herm_add_left, herm_add_right, ha₀, hb₀, hab, hba, add_zero]
    have hs0 : a₀ + b₀ ≠ 0 := by
      intro h
      have := congrFun h i₀
      simp [ha₀eq, hb₀def, Pi.single_apply, h01, h02, h03] at this
    refine ⟨pt b₀ hb₀0 hb₀, pt (a₀ + b₀) hs0 hs, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hx₀, Ne, pt_eq_pt_iff]
      rintro ⟨c, hc⟩
      have := congrFun hc i₂
      simp [ha₀eq, hb₀def, Pi.single_apply, Ne.symm h02, Ne.symm h12, h23] at this
    · rw [hx₀, Ne, pt_eq_pt_iff]
      rintro ⟨c, hc⟩
      have := congrFun hc i₂
      simp [ha₀eq, hb₀def, Pi.single_apply, Ne.symm h02, Ne.symm h12, h23] at this
    · rw [Ne, pt_eq_pt_iff]
      rintro ⟨c, hc⟩
      have := congrFun hc i₀
      simp [ha₀eq, hb₀def, Pi.single_apply, h01, h02, h03] at this
      rw [this, zero_smul] at hc
      exact hb₀0 hc.symm
    · rw [hx₀, perpU_pt]; exact hab
    · rw [hx₀, perpU_pt, herm_add_right, ha₀, hab, add_zero]
    · rw [perpU_pt, herm_add_right, hba, hb₀, add_zero]
  · -- the non-perpendicular triangle `[a₀], [e₀ + ω u e₁], [e₀ + u e₂]`
    obtain ⟨ω, hω, hω1⟩ := hσ.exists_norm_one_ne_one
    set c₁ : Fin n → K := Pi.single i₀ 1 + Pi.single i₁ (ω * u) with hc₁def
    set c₂ : Fin n → K := Pi.single i₀ 1 + Pi.single i₂ u with hc₂def
    have hc₁0 : c₁ ≠ 0 := single_add_single_ne_zero h01 _
    have hc₂0 : c₂ ≠ 0 := single_add_single_ne_zero h02 _
    have hc₁ : herm σ c₁ c₁ = 0 := by
      rw [hc₁def, herm_single_add_single_self h01, map_mul,
        show σ ω * σ u * (ω * u) = (σ ω * ω) * (σ u * u) by ring, hω, hu]; ring
    have hc₂ : herm σ c₂ c₂ = 0 := by rw [hc₂def, herm_single_add_single_self h02, hu]; ring
    refine ⟨pt c₁ hc₁0 hc₁, pt c₂ hc₂0 hc₂, ?_, ?_, ?_⟩
    · have key : herm σ a₀ c₁ = 1 - ω := by
        rw [ha₀eq, hc₁def, herm_two_two]
        simp only [Pi.add_apply, Pi.single_apply, if_true, if_neg (Ne.symm h01), if_neg h01,
          map_one, one_mul, add_zero, zero_add]
        linear_combination ω * hu
      rw [hx₀, perpU_pt, key]
      exact sub_ne_zero.2 (Ne.symm hω1)
    · rw [hx₀, perpU_pt, ha₀eq, hc₂def, herm_two_two]
      simp [Pi.single_apply, h01, h02, h12, Ne.symm h01, Ne.symm h02, Ne.symm h12]
    · rw [perpU_pt, hc₁def, hc₂def, herm_two_two]
      simp [Pi.single_apply, h01, h02, h12, Ne.symm h01, Ne.symm h02, Ne.symm h12]

end CFSGOutside.HallPaige.Unitary
