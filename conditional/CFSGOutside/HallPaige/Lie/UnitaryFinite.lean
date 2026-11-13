import CFSGOutside.HallPaige.Lie.UnitaryForm
import CFSGOutside.Corpus.HallPaige.LieUnitary
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.CharP.Frobenius

/-!
# The unitary involution of `𝔽_{q²}`

`x ↦ x^q` on a field with `q²` elements is a unitary involution (norm and trace onto the fixed
field), and the corpus group `StatedSU n q K` is the special unitary group `SUid` of the standard
hermitian form. Proofs ported from AxiomMath/CFSG @ 69cb972,
CFSG/LieType/BorelTits/UnitaryForm.lean and CFSG/ClassicalGroups/Unitary/Finite.lean.
-/

namespace CFSGOutside.HallPaige.Unitary

open Matrix Corpus.Lie

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

variable (K p f) in
/-- The unitary involution `x ↦ x^{p^f}`. -/
noncomputable abbrev unitaryInvolution : K ≃+* K :=
  iterateFrobeniusEquiv K p f

theorem unitaryInvolution_apply (c : K) : unitaryInvolution K p f c = c ^ p ^ f := by
  rw [unitaryInvolution, iterateFrobeniusEquiv_apply, iterateFrobenius_def]

theorem unitaryInvolution_involutive (hK : Nat.card K = (p ^ f) ^ 2) (c : K) :
    unitaryInvolution K p f (unitaryInvolution K p f c) = c := by
  have := Fintype.ofFinite K
  rw [unitaryInvolution_apply, unitaryInvolution_apply, ← pow_mul, ← sq, ← hK,
    Nat.card_eq_fintype_card, FiniteField.pow_card]

omit [Fact p.Prime] [CharP K p] in
theorem one_lt_pow_of_card (hK : Nat.card K = (p ^ f) ^ 2) : 1 < p ^ f := by
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  rw [hK] at h1
  by_contra h
  have : p ^ f ≤ 1 := not_lt.mp h
  nlinarith [Nat.zero_le (p ^ f)]

theorem exists_unitaryInvolution_ne (hK : Nat.card K = (p ^ f) ^ 2) :
    ∃ a : K, unitaryInvolution K p f a ≠ a := by
  classical
  have := Fintype.ofFinite K
  have hq := one_lt_pow_of_card hK
  by_contra! h
  have hP := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (Polynomial.X ^ p ^ f - Polynomial.X : Polynomial K) (f := id) Function.injective_id
    (fun a => by
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, id]
      rw [← unitaryInvolution_apply, h a, sub_self])
    (by rw [FiniteField.X_pow_card_sub_X_natDegree_eq K hq, ← Nat.card_eq_fintype_card, hK]
        nlinarith)
  have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq K hq
  rw [hP, Polynomial.natDegree_zero] at hdeg
  omega

theorem exists_add_unitaryInvolution_eq (hK : Nat.card K = (p ^ f) ^ 2) {a : K}
    (ha : unitaryInvolution K p f a = a) : ∃ c : K, c + unitaryInvolution K p f c = a := by
  classical
  have := Fintype.ofFinite K
  have hq := one_lt_pow_of_card hK
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : K, c₀ + unitaryInvolution K p f c₀ ≠ 0 := by
    by_contra! h
    have hdeg : (Polynomial.X ^ p ^ f + Polynomial.X : Polynomial K).natDegree = p ^ f := by
      rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt] <;>
        simp [hq]
    have hP := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (Polynomial.X ^ p ^ f + Polynomial.X : Polynomial K) (f := id) Function.injective_id
      (fun c => by
        have := h c
        simp only [unitaryInvolution_apply] at this
        simp [add_comm, this])
      (by rw [hdeg, ← Nat.card_eq_fintype_card, hK]; nlinarith)
    rw [hP, Polynomial.natDegree_zero] at hdeg
    omega
  set t := c₀ + unitaryInvolution K p f c₀ with ht
  have htσ : unitaryInvolution K p f t = t := by
    rw [ht, map_add, unitaryInvolution_involutive hK, add_comm]
  refine ⟨(a / t) * c₀, ?_⟩
  rw [map_mul, map_div₀, ha, htσ, ← mul_add, ← ht, div_mul_cancel₀ a hc₀]

omit [Fact p.Prime] [CharP K p] in
theorem card_units_of_card (hK : Nat.card K = (p ^ f) ^ 2) :
    Nat.card Kˣ = (p ^ f) ^ 2 - 1 := by
  classical
  have := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]

theorem sq_sub_one_eq (q : ℕ) (hq : 1 ≤ q) : q ^ 2 - 1 = (q + 1) * (q - 1) := by
  zify [hq, Nat.one_le_pow 2 q (by omega)]
  ring

theorem exists_norm_eq_of_fixed (hK : Nat.card K = (p ^ f) ^ 2) {d : K}
    (hd : unitaryInvolution K p f d = d) (hd0 : d ≠ 0) :
    ∃ c : K, unitaryInvolution K p f c * c = d := by
  have hq := one_lt_pow_of_card hK
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, card_units_of_card hK]
  set D : Kˣ := Units.mk0 d hd0 with hD
  obtain ⟨k, hk⟩ : ∃ k : ℕ, g ^ k = D :=
    (mem_powers_iff_mem_zpowers.mpr (hg D))
  have hDq : D ^ (p ^ f) = D := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hD, Units.val_mk0, ← unitaryInvolution_apply, hd]
  have hDq1 : D ^ (p ^ f - 1) = 1 := by
    have h := hDq
    rw [← Nat.sub_add_cancel hq.le, pow_succ] at h
    exact mul_eq_right.mp h
  have hdvd : (p ^ f) ^ 2 - 1 ∣ k * (p ^ f - 1) := by
    rw [← hord]
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, hk, hDq1]
  rw [sq_sub_one_eq _ hq.le] at hdvd
  obtain ⟨j, rfl⟩ : p ^ f + 1 ∣ k :=
    Nat.dvd_of_mul_dvd_mul_right (by omega) hdvd
  refine ⟨((g ^ j : Kˣ) : K), ?_⟩
  rw [unitaryInvolution_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, ← pow_mul,
    mul_comm j, hk, hD, Units.val_mk0]

theorem isUnitaryInvolution_unitaryInvolution (hK : Nat.card K = (p ^ f) ^ 2) :
    IsUnitaryInvolution (unitaryInvolution K p f) where
  invol := unitaryInvolution_involutive hK
  exists_ne := exists_unitaryInvolution_ne hK
  trace_surj _ ha := exists_add_unitaryInvolution_eq hK ha
  norm_surj _ hd hd0 := exists_norm_eq_of_fixed hK hd hd0

theorem conjTr_eq_map_pow {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    conjTr (unitaryInvolution K p f) A = (A.map (· ^ p ^ f))ᵀ := by
  ext i j
  simp only [conjTr, transpose_apply, map_apply]
  exact unitaryInvolution_apply _

/-- **The corpus group `StatedSU` is `SUid`.** -/
theorem SUid_eq_statedSU (n : ℕ) :
    SUid (unitaryInvolution K p f) n = StatedSU n (p ^ f) K := by
  ext B
  constructor
  · intro hB
    refine Subgroup.subset_closure ⟨hB.1, ?_⟩
    rw [← conjTr_eq_map_pow]
    exact hB.2
  · intro hB
    induction hB using Subgroup.closure_induction with
    | mem A hA => exact ⟨hA.1, by rw [conjTr_eq_map_pow]; exact hA.2⟩
    | one => exact (SUid _ n).one_mem
    | mul A B _ _ hA hB => exact (SUid _ n).mul_mem hA hB
    | inv A _ hA => exact (SUid _ n).inv_mem hA

end CFSGOutside.HallPaige.Unitary
