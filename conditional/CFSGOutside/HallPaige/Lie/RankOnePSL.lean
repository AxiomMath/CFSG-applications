import CFSGOutside.HallPaige.Lie.RankOne
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import CFSGOutside.HallPaige.Lie.TypeA

/-!
# `PSL₂(q)` for `q ≡ 1 (mod 4)`

`CFSGOutside.HallPaige.hasCompleteMapping_PSL_two_of_mod_four_eq_one`: for a finite field `K` with
`|K| ≡ 1 (mod 4)`, `PSL₂(K)` has a complete mapping. This is Wilcox, Lemma 23, via
`CFSGOutside.HallPaige.hasCompleteMapping_of_rankOne_split` with `U` the upper unitriangular matrices,
`T` the diagonal matrices and `n = [[0, 1], [-1, 0]]`; the identity
`diag(l, l⁻¹) n = ±x(l) n x(l⁻¹) n x(l)` gives `T n ⊆ UnUnU`.
-/

namespace CFSGOutside.HallPaige

open Matrix

namespace PSLTwo

variable {K : Type} [Field K]

local notation "SL2" => Matrix.SpecialLinearGroup (Fin 2) K
local notation "PSL2" => ProjectiveSpecialLinearGroup (Fin 2) K

/-- The upper unitriangular matrix `x(b)`. -/
def xu (b : K) : SL2 := ⟨!![1, b; 0, 1], by simp [det_fin_two]⟩

/-- The diagonal matrix `diag(l, l⁻¹)`. -/
def dg (l : Kˣ) : SL2 := ⟨!![(l : K), 0; 0, ((l⁻¹ : Kˣ) : K)], by simp [det_fin_two]⟩

/-- The Weyl element `[[0, 1], [-1, 0]]`. -/
def wn : SL2 := ⟨!![0, 1; -1, 0], by simp [det_fin_two]⟩

theorem coe_xu (b : K) : ((xu b : SL2) : Matrix (Fin 2) (Fin 2) K) = !![1, b; 0, 1] := rfl
theorem coe_dg (l : Kˣ) :
    ((dg l : SL2) : Matrix (Fin 2) (Fin 2) K) = !![(l : K), 0; 0, ((l⁻¹ : Kˣ) : K)] := rfl
theorem coe_wn : ((wn : SL2) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] := rfl

/-- `x` as a homomorphism from the additive group. -/
def xuHom : Multiplicative K →* SL2 where
  toFun b := xu (Multiplicative.toAdd b)
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_mul' a b := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_xu, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/-- `diag` as a homomorphism from the units. -/
def dgHom : Kˣ →* SL2 where
  toFun := dg
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp [coe_dg]
  map_mul' a b := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_dg, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

/-- The unipotent subgroup `U` of `PSL₂`. -/
def Usub : Subgroup PSL2 := ((QuotientGroup.mk' _).comp (xuHom (K := K))).range

/-- The diagonal torus `T` of `PSL₂`. -/
def Tsub : Subgroup PSL2 := ((QuotientGroup.mk' _).comp (dgHom (K := K))).range

theorem mk_xu_mem (b : K) : ((xu b : SL2) : PSL2) ∈ Usub := ⟨Multiplicative.ofAdd b, rfl⟩
theorem mk_dg_mem (l : Kˣ) : ((dg l : SL2) : PSL2) ∈ Tsub := ⟨l, rfl⟩

theorem mem_Usub {g : PSL2} : g ∈ Usub ↔ ∃ b : K, ((xu b : SL2) : PSL2) = g :=
  ⟨fun ⟨b, hb⟩ => ⟨Multiplicative.toAdd b, hb⟩, fun ⟨b, hb⟩ => ⟨Multiplicative.ofAdd b, hb⟩⟩

theorem mem_Tsub {g : PSL2} : g ∈ Tsub ↔ ∃ l : Kˣ, ((dg l : SL2) : PSL2) = g := Iff.rfl

/-- Equality in `PSL₂`: up to a scalar `r` with `r² = 1`. -/
theorem mk_eq_mk_iff (A B : SL2) :
    (A : PSL2) = (B : PSL2) ↔ ∃ r : K, r ^ 2 = 1 ∧
      (B : Matrix (Fin 2) (Fin 2) K) = (A : Matrix (Fin 2) (Fin 2) K) * scalar (Fin 2) r := by
  rw [QuotientGroup.eq, Matrix.SpecialLinearGroup.mem_center_iff, Fintype.card_fin]
  constructor
  · rintro ⟨r, hr, h⟩
    refine ⟨r, hr, ?_⟩
    rw [h, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
      mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
  · rintro ⟨r, hr, h⟩
    refine ⟨r, hr, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, h, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]

theorem entry_of_mk_eq {A B : SL2} (h : (A : PSL2) = (B : PSL2)) :
    ∃ r : K, r ^ 2 = 1 ∧ ∀ i j, (B : Matrix (Fin 2) (Fin 2) K) i j =
      (A : Matrix (Fin 2) (Fin 2) K) i j * r := by
  obtain ⟨r, hr, h⟩ := (mk_eq_mk_iff A B).1 h
  refine ⟨r, hr, fun i j => ?_⟩
  rw [h]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, scalar_apply, Matrix.diagonal_apply]

variable [Finite K]

theorem dg_conj_xu (l : Kˣ) (b : K) :
    dg l * xu b * (dg l)⁻¹ = xu ((l : K) * l * b) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_dg, coe_xu, Matrix.mul_apply, Fin.sum_univ_two, mul_comm, mul_assoc]

theorem hTU : ∀ t ∈ (Tsub : Subgroup PSL2), ∀ u ∈ (Usub : Subgroup PSL2), t * u * t⁻¹ ∈ Usub := by
  rintro _ ⟨l, rfl⟩ _ ⟨b, rfl⟩
  refine mem_Usub.2 ⟨(l : K) * l * Multiplicative.toAdd b, ?_⟩
  rw [← dg_conj_xu]
  rfl

theorem xu_zero : (xu 0 : SL2) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem hUT : ∀ u ∈ (Usub : Subgroup PSL2), u ∈ (Tsub : Subgroup PSL2) → u = 1 := by
  intro u hu ht
  obtain ⟨b, rfl⟩ := mem_Usub.1 hu
  obtain ⟨l, hl⟩ := mem_Tsub.1 ht
  obtain ⟨r, -, h⟩ := entry_of_mk_eq hl
  have h01 := h 0 1
  simp [coe_dg, coe_xu] at h01
  rw [h01, xu_zero]
  rfl

/-- The Weyl element of `PSL₂`. -/
def nP : PSL2 := ((wn : SL2) : PSL2)

theorem nP_mul_nP : (nP : PSL2) * nP = 1 := by
  change ((wn * wn : SL2) : PSL2) = ((1 : SL2) : PSL2)
  rw [mk_eq_mk_iff]
  refine ⟨-1, by ring, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_wn, Matrix.mul_apply, Fin.sum_univ_two]

theorem nP_not_mem : nP ∉ borelOf (Usub : Subgroup PSL2) Tsub hTU := by
  rintro ⟨_, ⟨l, rfl⟩, _, ⟨b, rfl⟩, h⟩
  change ((wn : SL2) : PSL2) = ((dg l * xu (Multiplicative.toAdd b) : SL2) : PSL2) at h
  obtain ⟨r, hr, h⟩ := entry_of_mk_eq h.symm
  have h10 := h 1 0
  simp [coe_dg, coe_xu, coe_wn, Matrix.mul_apply, Fin.sum_univ_two] at h10

theorem hV : ∀ u ∈ (Usub : Subgroup PSL2), nP * u * nP ∈ borelOf Usub Tsub hTU → u = 1 := by
  rintro _ ⟨b, rfl⟩ ⟨_, ⟨l, rfl⟩, _, ⟨c, rfl⟩, h⟩
  change ((wn * xu (Multiplicative.toAdd b) * wn : SL2) : PSL2) =
    ((dg l * xu (Multiplicative.toAdd c) : SL2) : PSL2) at h
  obtain ⟨r, hr, h⟩ := entry_of_mk_eq h.symm
  have h10 := h 1 0
  simp [coe_dg, coe_xu, coe_wn, Matrix.mul_apply, Fin.sum_univ_two] at h10
  change ((xu (Multiplicative.toAdd b) : SL2) : PSL2) = 1
  rw [h10, toAdd_one, xu_zero]
  rfl

theorem hcover (g : PSL2) : g ∈ borelOf Usub Tsub hTU ∨
    ∃ u ∈ (Usub : Subgroup PSL2), ∃ t ∈ (Tsub : Subgroup PSL2), ∃ u' ∈ (Usub : Subgroup PSL2),
      g = u * nP * t * u' := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective g
  have hdet : (A : Matrix (Fin 2) (Fin 2) K) 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    rw [← det_fin_two]; exact A.2
  by_cases hc : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · left
    have ha : (A : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by
      rintro h; rw [h, hc] at hdet; simp at hdet
    rw [hc, mul_zero, sub_zero] at hdet
    refine ⟨_, mk_dg_mem (Units.mk0 _ ha), _, mk_xu_mem ((A : Matrix (Fin 2) (Fin 2) K) 0 1 /
      (A : Matrix (Fin 2) (Fin 2) K) 0 0), ?_⟩
    change ((A : SL2) : PSL2) = ((dg (Units.mk0 _ ha) * xu _ : SL2) : PSL2)
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_dg, coe_xu, Matrix.mul_apply, Fin.sum_univ_two, hc]
    all_goals first
      | (field_simp; done)
      | (field_simp; linear_combination hdet)
  · right
    refine ⟨_, mk_xu_mem ((A : Matrix (Fin 2) (Fin 2) K) 0 0 / A 1 0), _,
      mk_dg_mem (Units.mk0 (-(A : Matrix (Fin 2) (Fin 2) K) 1 0) (neg_ne_zero.2 hc)), _,
      mk_xu_mem ((A : Matrix (Fin 2) (Fin 2) K) 1 1 / A 1 0), ?_⟩
    change ((A : SL2) : PSL2) = ((xu _ * wn * dg (Units.mk0 _ (neg_ne_zero.2 hc)) * xu _ : SL2) : PSL2)
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_dg, coe_xu, coe_wn, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first
      | (field_simp; done)
      | (field_simp; linear_combination hdet)
      | (field_simp; linear_combination -hdet)
      | (field_simp; linear_combination (A : Matrix (Fin 2) (Fin 2) K) 1 0 * hdet)
      | (field_simp; linear_combination -(A : Matrix (Fin 2) (Fin 2) K) 1 0 * hdet)

theorem hTn : ∀ t ∈ (Tsub : Subgroup PSL2), ∃ a ∈ (Usub : Subgroup PSL2),
    ∃ b ∈ (Usub : Subgroup PSL2), ∃ c ∈ (Usub : Subgroup PSL2), t * nP = a * nP * b * nP * c := by
  rintro _ ⟨l, rfl⟩
  refine ⟨_, mk_xu_mem (l : K), _, mk_xu_mem ((l⁻¹ : Kˣ) : K), _, mk_xu_mem (l : K), ?_⟩
  change ((dg l * wn : SL2) : PSL2) =
    ((xu (l : K) * wn * xu ((l⁻¹ : Kˣ) : K) * wn * xu (l : K) : SL2) : PSL2)
  rw [mk_eq_mk_iff]
  refine ⟨-1, by ring, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_dg, coe_xu, coe_wn, Matrix.mul_apply, Fin.sum_univ_two]

theorem isCyclic_Tsub : IsCyclic (Tsub : Subgroup PSL2) :=
  isCyclic_of_surjective _ ((QuotientGroup.mk' _).comp (dgHom (K := K))).rangeRestrict_surjective

theorem odd_card_Usub (hK : Odd (Nat.card K)) : Odd (Nat.card (Usub : Subgroup PSL2)) := by
  have hdvd : Nat.card (Usub : Subgroup PSL2) ∣ Nat.card (Multiplicative K) :=
    Subgroup.card_dvd_of_surjective (f := ((QuotientGroup.mk' _).comp (xuHom (K := K))).rangeRestrict)
      (hf := ((QuotientGroup.mk' _).comp (xuHom (K := K))).rangeRestrict_surjective)
  exact Odd.of_dvd_nat hK hdvd

theorem even_card_Tsub (hK : Nat.card K % 4 = 1) : Even (Nat.card (Tsub : Subgroup PSL2)) := by
  have := Fintype.ofFinite K
  have hsq : IsSquare (-1 : K) := by
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card]; omega
  obtain ⟨i, hi⟩ := hsq
  have hi0 : i ≠ 0 := by rintro rfl; simp at hi
  have hchar : (-1 : K) ≠ 1 := neg_one_ne_one_of_odd_card (Nat.odd_iff.2 (by omega))
  let τ : (Tsub : Subgroup PSL2) := ⟨_, mk_dg_mem (Units.mk0 i hi0)⟩
  have hτ : orderOf τ = 2 := by
    apply orderOf_eq_prime
    · rw [sq]
      apply Subtype.ext
      change ((dg (Units.mk0 i hi0) * dg (Units.mk0 i hi0) : SL2) : PSL2) = ((1 : SL2) : PSL2)
      rw [mk_eq_mk_iff]
      refine ⟨-1, by ring, ?_⟩
      ext a b
      fin_cases a <;> fin_cases b <;> simp [coe_dg, Matrix.mul_apply, Fin.sum_univ_two] <;>
        field_simp <;> linear_combination -hi
    · intro h
      have h' : ((dg (Units.mk0 i hi0) : SL2) : PSL2) = ((1 : SL2) : PSL2) :=
        congrArg Subtype.val h
      obtain ⟨r, hr, h⟩ := entry_of_mk_eq h'.symm
      have h00 := h 0 0
      have h11 := h 1 1
      simp [coe_dg] at h00 h11
      apply hchar
      have : i * i = 1 := by
        rw [← h00] at h11
        field_simp at h11
        linear_combination -h11
      rw [hi, this]
  have := orderOf_dvd_natCard τ
  rw [hτ] at this
  exact (even_iff_two_dvd).2 this

end PSLTwo

open PSLTwo in
/-- **Hall–Paige for `PSL₂(q)`, `q ≡ 1 (mod 4)`** (Wilcox, Lemma 23): `PSL₂(K)` has a complete
mapping. -/
theorem hasCompleteMapping_PSL_two_of_mod_four_eq_one {K : Type} [Field K] [Finite K]
    (hK : Nat.card K % 4 = 1) : HasCompleteMapping (ProjectiveSpecialLinearGroup (Fin 2) K) :=
  hasCompleteMapping_of_rankOne_split (U := Usub) (T := Tsub) (hTU := hTU) nP
    (odd_card_Usub (Nat.odd_iff.2 (by omega))) nP_mul_nP hUT nP_not_mem hV hcover hTn
    isCyclic_Tsub (even_card_Tsub hK)

end CFSGOutside.HallPaige
