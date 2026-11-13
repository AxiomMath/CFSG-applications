import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

/-!
# Hermitian forms and the special unitary group

The standard hermitian form `h(x, y) = ∑ σ(xᵢ) yᵢ` on `Kⁿ` for an involutive automorphism `σ`
with the norm and trace surjective onto the fixed field, the special unitary group `SU_n`, and
the existence of isotropic vectors with prescribed pairings.

Ported (proofs copied, names unchanged) from AxiomMath/CFSG @ 69cb972,
CFSG/ClassicalGroups/Unitary/Form.lean and CFSG/LieType/Universal/Unitary/{Basic,Comparison}.lean
(`conjTr`, `SUid`). No corpus axioms are used.
-/

namespace CFSGOutside.HallPaige.Unitary

open Matrix

section General

variable {F : Type*} [Field F] (σ : F ≃+* F)

/-- The conjugate transpose. -/
def conjTr {n : ℕ} (A : Matrix (Fin n) (Fin n) F) : Matrix (Fin n) (Fin n) F :=
  (A.map σ)ᵀ

theorem conjTr_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) F) :
    conjTr σ (A * B) = conjTr σ B * conjTr σ A := by
  simp only [conjTr, Matrix.map_mul, transpose_mul]

theorem conjTr_one {n : ℕ} : conjTr σ (1 : Matrix (Fin n) (Fin n) F) = 1 := by
  simp [conjTr]

/-- The special unitary group of the standard hermitian form. -/
def SUid (n : ℕ) : Subgroup (GL (Fin n) F) where
  carrier := {B | (B : Matrix (Fin n) (Fin n) F).det = 1 ∧
    conjTr σ (B : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F) = 1}
  mul_mem' {A B} hA hB := by
    refine ⟨by rw [Units.val_mul, det_mul, hA.1, hB.1, one_mul], ?_⟩
    have e : conjTr σ ((A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F)) *
        ((A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F)) =
        conjTr σ (B : Matrix (Fin n) (Fin n) F) *
          (conjTr σ (A : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F)) *
            (B : Matrix (Fin n) (Fin n) F) := by
      rw [conjTr_mul]
      simp only [Matrix.mul_assoc]
    rw [Units.val_mul, e, hA.2, Matrix.mul_one, hB.2]
  one_mem' := ⟨by simp, by simp [conjTr_one]⟩
  inv_mem' {A} hA := by
    have hAB : (A : Matrix (Fin n) (Fin n) F) * ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    refine ⟨?_, ?_⟩
    · have := congrArg Matrix.det hAB
      rw [det_mul, det_one, hA.1, one_mul] at this
      exact this
    · have key : conjTr σ ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F) *
          (conjTr σ (A : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F)) *
            ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F) =
          conjTr σ ((A : Matrix _ _ F) * ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F)) *
            ((A : Matrix _ _ F) * ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F)) := by
        rw [conjTr_mul]
        simp only [Matrix.mul_assoc]
      rw [hA.2, Matrix.mul_one, hAB, conjTr_one, Matrix.one_mul] at key
      exact key

variable {σ}

theorem mem_SUid {n : ℕ} {B : GL (Fin n) F} :
    B ∈ SUid σ n ↔ (B : Matrix (Fin n) (Fin n) F).det = 1 ∧
      conjTr σ (B : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F) = 1 :=
  Iff.rfl

end General

open Matrix

variable {K : Type*} [Field K]

structure IsUnitaryInvolution (σ : K ≃+* K) : Prop where
  invol : ∀ c, σ (σ c) = c
  exists_ne : ∃ c, σ c ≠ c
  trace_surj : ∀ a, σ a = a → ∃ c, c + σ c = a
  norm_surj : ∀ d, σ d = d → d ≠ 0 → ∃ c, σ c * c = d

namespace IsUnitaryInvolution

variable {σ : K ≃+* K} (hσ : IsUnitaryInvolution σ)
include hσ

theorem exists_traceZero : ∃ τ : K, τ ≠ 0 ∧ τ + σ τ = 0 := by
  obtain ⟨c, hc⟩ := hσ.exists_ne
  refine ⟨c - σ c, sub_ne_zero.mpr (Ne.symm hc), ?_⟩
  rw [map_sub, hσ.invol]
  ring

theorem exists_norm {d : K} (hd : σ d = d) : ∃ c : K, σ c * c = d := by
  by_cases h0 : d = 0
  · exact ⟨0, by rw [h0, map_zero, zero_mul]⟩
  · exact hσ.norm_surj d hd h0

theorem exists_norm_neg_one : ∃ u : K, σ u * u = -1 :=
  hσ.exists_norm (by rw [map_neg, map_one])

theorem exists_norm_one_ne_one : ∃ ω : K, σ ω * ω = 1 ∧ ω ≠ 1 := by
  obtain ⟨c, hc⟩ := hσ.exists_ne
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc (map_zero σ)
  have hσc0 : σ c ≠ 0 := (map_ne_zero σ).mpr hc0
  refine ⟨c / σ c, ?_, ?_⟩
  · rw [map_div₀, hσ.invol]
    field_simp
  · intro h
    rw [div_eq_one_iff_eq hσc0] at h
    exact hc h.symm

end IsUnitaryInvolution

variable (σ : K ≃+* K) {n : ℕ}

def herm (x y : Fin n → K) : K := ∑ i, σ (x i) * y i

theorem herm_def (x y : Fin n → K) : herm σ x y = ∑ i, σ (x i) * y i := rfl

@[simp] theorem herm_add_left (x x' y : Fin n → K) :
    herm σ (x + x') y = herm σ x y + herm σ x' y := by
  simp only [herm, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

@[simp] theorem herm_add_right (x y y' : Fin n → K) :
    herm σ x (y + y') = herm σ x y + herm σ x y' := by
  simp only [herm, Pi.add_apply, mul_add, Finset.sum_add_distrib]

@[simp] theorem herm_smul_left (c : K) (x y : Fin n → K) :
    herm σ (c • x) y = σ c * herm σ x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

@[simp] theorem herm_smul_right (c : K) (x y : Fin n → K) :
    herm σ x (c • y) = c * herm σ x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by ring

@[simp] theorem herm_neg_left (x y : Fin n → K) : herm σ (-x) y = -herm σ x y := by
  simp only [herm, Pi.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]

@[simp] theorem herm_neg_right (x y : Fin n → K) : herm σ x (-y) = -herm σ x y := by
  simp only [herm, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

@[simp] theorem herm_sub_left (x x' y : Fin n → K) :
    herm σ (x - x') y = herm σ x y - herm σ x' y := by
  rw [sub_eq_add_neg, herm_add_left, herm_neg_left, ← sub_eq_add_neg]

@[simp] theorem herm_sub_right (x y y' : Fin n → K) :
    herm σ x (y - y') = herm σ x y - herm σ x y' := by
  rw [sub_eq_add_neg, herm_add_right, herm_neg_right, ← sub_eq_add_neg]

@[simp] theorem herm_zero_left (y : Fin n → K) : herm σ 0 y = 0 := by
  simp [herm]

@[simp] theorem herm_zero_right (x : Fin n → K) : herm σ x 0 = 0 := by
  simp [herm]

theorem herm_single_left (i : Fin n) (c : K) (y : Fin n → K) :
    herm σ (Pi.single i c) y = σ c * y i := by
  rw [herm, Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
  simp

theorem herm_single_right (x : Fin n → K) (i : Fin n) (c : K) :
    herm σ x (Pi.single i c) = σ (x i) * c := by
  rw [herm, Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
  simp

def hermL (x : Fin n → K) : (Fin n → K) →ₗ[K] K where
  toFun := herm σ x
  map_add' := herm_add_right σ x
  map_smul' c y := herm_smul_right σ c x y

@[simp] theorem hermL_apply (x y : Fin n → K) : hermL σ x y = herm σ x y := rfl

theorem herm_conj (hσ : ∀ c, σ (σ c) = c) (x y : Fin n → K) :
    herm σ y x = σ (herm σ x y) := by
  rw [herm, herm, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, hσ, mul_comm]

theorem herm_self_fixed (hσ : ∀ c, σ (σ c) = c) (x : Fin n → K) :
    σ (herm σ x x) = herm σ x x :=
  (herm_conj σ hσ x x).symm

theorem herm_eq_zero_comm (hσ : ∀ c, σ (σ c) = c) {x y : Fin n → K} (h : herm σ x y = 0) :
    herm σ y x = 0 := by
  rw [herm_conj σ hσ, h, map_zero]

theorem eq_zero_of_herm {x : Fin n → K} (h : ∀ y, herm σ x y = 0) : x = 0 := by
  funext i
  have := h (Pi.single i 1)
  rw [herm_single_right, mul_one] at this
  simpa using (map_eq_zero_iff σ σ.injective).mp this

theorem exists_herm_ne_zero {x : Fin n → K} (hx : x ≠ 0) : ∃ y, herm σ x y ≠ 0 := by
  by_contra! h
  exact hx (eq_zero_of_herm σ h)

theorem exists_herm_eq_one {x : Fin n → K} (hx : x ≠ 0) : ∃ y, herm σ x y = 1 := by
  obtain ⟨y, hy⟩ := exists_herm_ne_zero σ hx
  exact ⟨(herm σ x y)⁻¹ • y, by rw [herm_smul_right, inv_mul_cancel₀ hy]⟩

theorem herm_mulVec (A : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    herm σ (A *ᵥ x) (A *ᵥ y) = herm σ x ((conjTr σ A * A) *ᵥ y) := by
  have h1 : (fun i => σ ((A *ᵥ x) i)) = A.map σ *ᵥ fun i => σ (x i) := by
    funext i
    simp [mulVec, dotProduct, map_sum]
  have e1 : herm σ (A *ᵥ x) (A *ᵥ y) = (fun i => σ ((A *ᵥ x) i)) ⬝ᵥ (A *ᵥ y) := rfl
  have e2 : herm σ x ((conjTr σ A * A) *ᵥ y) =
      (fun i => σ (x i)) ⬝ᵥ ((conjTr σ A * A) *ᵥ y) := rfl
  rw [e1, e2, h1, conjTr, ← mulVec_mulVec, dotProduct_mulVec (fun i => σ (x i)),
    vecMul_transpose]

theorem conjTr_mul_self_of_isometry {A : Matrix (Fin n) (Fin n) K}
    (h : ∀ x y, herm σ (A *ᵥ x) (A *ᵥ y) = herm σ x y) : conjTr σ A * A = 1 := by
  ext j k
  have hjk := h (Pi.single j 1) (Pi.single k 1)
  rw [herm_mulVec, herm_single_left, map_one, one_mul, mulVec_single_one, herm_single_left,
    map_one, one_mul] at hjk
  rw [one_apply]
  simpa [col_apply, Pi.single_apply, eq_comm] using hjk

theorem mem_SUid_iff {B : GL (Fin n) K} :
    B ∈ SUid σ n ↔ (B : Matrix (Fin n) (Fin n) K).det = 1 ∧
      ∀ x y, herm σ ((B : Matrix (Fin n) (Fin n) K) *ᵥ x)
        ((B : Matrix (Fin n) (Fin n) K) *ᵥ y) = herm σ x y := by
  rw [mem_SUid]
  refine and_congr_right fun _ => ⟨fun h x y => ?_, conjTr_mul_self_of_isometry σ⟩
  rw [herm_mulVec, h, one_mulVec]

instance instSMulSUid : SMul (SUid σ n) (Fin n → K) := inferInstance

instance instMulActionSUid : MulAction (SUid σ n) (Fin n → K) := inferInstance

instance instDistribMulActionSUid : DistribMulAction (SUid σ n) (Fin n → K) := inferInstance

instance instSMulCommClassSUid : SMulCommClass (SUid σ n) K (Fin n → K) := inferInstance

noncomputable def mkSU (M : Matrix (Fin n) (Fin n) K) (hdet : M.det = 1)
    (hiso : ∀ x y, herm σ (M *ᵥ x) (M *ᵥ y) = herm σ x y) : SUid σ n :=
  ⟨GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero),
    (mem_SUid_iff σ).mpr ⟨hdet, hiso⟩⟩

theorem smul_def (g : SUid σ n) (v : Fin n → K) :
    g • v = ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v := rfl

@[simp] theorem mkSU_smul (M : Matrix (Fin n) (Fin n) K) (hdet : M.det = 1)
    (hiso : ∀ x y, herm σ (M *ᵥ x) (M *ᵥ y) = herm σ x y) (v : Fin n → K) :
    mkSU σ M hdet hiso • v = M *ᵥ v := rfl

theorem herm_smul_smul (g : SUid σ n) (x y : Fin n → K) :
    herm σ (g • x) (g • y) = herm σ x y :=
  ((mem_SUid_iff σ).mp g.2).2 x y

theorem ext_smul {g g' : SUid σ n} (H : ∀ v : Fin n → K, g • v = g' • v) : g = g' :=
  Subtype.ext (Units.ext (Matrix.ext_of_mulVec_single fun _ => H _))

variable {σ}

theorem herm_eq_zero_of_forall_isotropic (hσ : IsUnitaryInvolution σ)
    {S : Submodule K (Fin n → K)} (hS : ∀ s ∈ S, herm σ s s = 0) {a b : Fin n → K}
    (ha : a ∈ S) (hb : b ∈ S) : herm σ a b = 0 := by
  obtain ⟨c, hc⟩ := hσ.exists_ne
  have h1 := hS (a + b) (S.add_mem ha hb)
  have h2 := hS (a + c • b) (S.add_mem ha (S.smul_mem c hb))
  have hab := herm_conj σ hσ.invol a b
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hS a ha,
    hS b hb] at h1 h2
  rw [hab] at h1 h2
  have h3 : (c - σ c) * herm σ a b = 0 := by linear_combination h2 - σ c * h1
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hc
  · exact h

theorem exists_aniso_of_lt (hσ : IsUnitaryInvolution σ) {k : ℕ} (hk : k < n)
    (s : Fin k → (Fin n → K)) (P : (Fin n → K) →ₗ[K] (Fin n → K))
    (hP : ∀ y, y - P y ∈ Submodule.span K (Set.range s))
    (hPs : ∀ y j, herm σ (s j) (P y) = 0) : ∃ y, herm σ (P y) (P y) ≠ 0 := by
  by_contra! h
  have hpol : ∀ y y', herm σ (P y) (P y') = 0 := fun y y' =>
    herm_eq_zero_of_forall_isotropic hσ (S := LinearMap.range P)
      (by rintro _ ⟨z, rfl⟩; exact h z) ⟨y, rfl⟩ ⟨y', rfl⟩
  have hspan : ∀ y, ∀ w ∈ Submodule.span K (Set.range s), herm σ (P y) w = 0 := by
    intro y w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨j, rfl⟩ := hw
      exact herm_eq_zero_comm σ hσ.invol (hPs y j)
    | zero => exact herm_zero_right σ _
    | add w w' _ _ h1 h2 => rw [herm_add_right, h1, h2, add_zero]
    | smul c w _ h1 => rw [herm_smul_right, h1, mul_zero]
  have hP0 : ∀ y, P y = 0 := by
    intro y
    apply eq_zero_of_herm σ
    intro y'
    have : y' = P y' + (y' - P y') := by abel
    rw [this, herm_add_right, hpol, hspan y _ (hP y'), add_zero]
  have htop : Submodule.span K (Set.range s) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    simpa [hP0 y] using hP y
  have hle := finrank_range_le_card (R := K) s
  rw [Set.finrank, htop, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at hle
  omega

theorem exists_smul_norm_one (hσ : IsUnitaryInvolution σ) {z : Fin n → K}
    (hz : herm σ z z ≠ 0) : ∃ c : K, herm σ (c • z) (c • z) = 1 := by
  obtain ⟨c, hc⟩ := hσ.norm_surj (herm σ z z)⁻¹
    (by rw [map_inv₀, herm_self_fixed σ hσ.invol]) (inv_ne_zero hz)
  refine ⟨c, ?_⟩
  rw [herm_smul_left, herm_smul_right, ← mul_assoc, hc, inv_mul_cancel₀ hz]

theorem exists_norm_one_perp_pair (hσ : IsUnitaryInvolution σ) (hn : 3 ≤ n) {a f : Fin n → K}
    (ha : herm σ a a = 0) (hf : herm σ f f = 0) (haf : herm σ a f = 1) :
    ∃ z, herm σ z z = 1 ∧ herm σ a z = 0 ∧ herm σ f z = 0 := by
  have hfa : herm σ f a = 1 := by rw [herm_conj σ hσ.invol, haf, map_one]
  set P : (Fin n → K) →ₗ[K] (Fin n → K) :=
    LinearMap.id - (hermL σ f).smulRight a - (hermL σ a).smulRight f with hPdef
  have hPy : ∀ y, P y = y - herm σ f y • a - herm σ a y • f := fun y => rfl
  obtain ⟨y, hy⟩ := exists_aniso_of_lt hσ (k := 2) (by omega) ![a, f] P
    (fun y => by
      rw [hPy, show y - (y - herm σ f y • a - herm σ a y • f) =
        herm σ f y • a + herm σ a y • f by abel]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))
    (fun y j => by
      fin_cases j <;> simp [hPy, ha, hf, haf, hfa])
  obtain ⟨c, hc⟩ := exists_smul_norm_one hσ hy
  refine ⟨c • P y, hc, ?_, ?_⟩ <;> simp [hPy, ha, hf, haf, hfa]

theorem exists_isotropize (hσ : IsUnitaryInvolution σ) {a y : Fin n → K}
    (ha : herm σ a a = 0) (hay : herm σ a y = 1) :
    ∃ c : K, herm σ (y + c • a) (y + c • a) = 0 := by
  obtain ⟨c, hc⟩ := hσ.trace_surj (-herm σ y y)
    (by rw [map_neg, herm_self_fixed σ hσ.invol])
  refine ⟨c, ?_⟩
  have hya : herm σ y a = 1 := by rw [herm_conj σ hσ.invol, hay, map_one]
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, ha, hya, hay]
  linear_combination hc

theorem exists_partner (hσ : IsUnitaryInvolution σ) {a : Fin n → K} (ha0 : a ≠ 0)
    (ha : herm σ a a = 0) : ∃ f, herm σ f f = 0 ∧ herm σ a f = 1 := by
  obtain ⟨y, hy⟩ := exists_herm_eq_one σ ha0
  obtain ⟨c, hc⟩ := exists_isotropize hσ ha hy
  exact ⟨y + c • a, hc, by rw [herm_add_right, herm_smul_right, ha, mul_zero, add_zero, hy]⟩

theorem exists_partner_perp (hσ : IsUnitaryInvolution σ) {x a : Fin n → K}
    (hx : herm σ x x = 1) (ha0 : a ≠ 0) (ha : herm σ a a = 0) (hxa : herm σ x a = 0) :
    ∃ v, herm σ x v = 0 ∧ herm σ v v = 0 ∧ herm σ a v = 1 := by
  obtain ⟨y, hy⟩ := exists_herm_eq_one σ ha0
  have hax : herm σ a x = 0 := herm_eq_zero_comm σ hσ.invol hxa
  have hy2 : herm σ a (y - herm σ x y • x) = 1 := by
    rw [herm_sub_right, herm_smul_right, hax, mul_zero, sub_zero, hy]
  obtain ⟨c, hc⟩ := exists_isotropize hσ ha hy2
  refine ⟨y - herm σ x y • x + c • a, ?_, hc, ?_⟩
  · simp [hx, hxa]
  · rw [herm_add_right, hy2, herm_smul_right, ha, mul_zero, add_zero]

theorem herm_proj_pair (hσ : IsUnitaryInvolution σ) {a f : Fin n → K}
    (ha : herm σ a a = 0) (hf : herm σ f f = 0) (haf : herm σ a f = 1) (y : Fin n → K) :
    herm σ a (y - herm σ f y • a - herm σ a y • f) = 0 ∧
      herm σ f (y - herm σ f y • a - herm σ a y • f) = 0 := by
  have hfa : herm σ f a = 1 := by rw [herm_conj σ hσ.invol, haf, map_one]
  constructor <;> simp [ha, hf, haf, hfa]

theorem exists_cno (hσ : IsUnitaryInvolution σ) {a b : Fin n → K} (ha0 : a ≠ 0)
    (ha : herm σ a a = 0) (hb0 : b ≠ 0) :
    ∃ d, herm σ d d = 0 ∧ herm σ a d ≠ 0 ∧ herm σ b d ≠ 0 := by
  obtain ⟨f, hf, haf⟩ := exists_partner hσ ha0 ha
  have hfa : herm σ f a = 1 := by rw [herm_conj σ hσ.invol, haf, map_one]
  by_cases hbf : herm σ b f ≠ 0
  · exact ⟨f, hf, by rw [haf]; exact one_ne_zero, hbf⟩
  push Not at hbf
  by_cases hba : herm σ b a ≠ 0
  · obtain ⟨τ, hτ0, hτ⟩ := hσ.exists_traceZero
    refine ⟨f + τ • a, ?_, ?_, ?_⟩
    · simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, ha, hf, haf,
        hfa]
      linear_combination hτ
    · simp [ha, haf]
    · simp only [herm_add_right, herm_smul_right, hbf, zero_add]
      exact mul_ne_zero hτ0 hba
  push Not at hba
  obtain ⟨y₀, hy₀⟩ := exists_herm_ne_zero σ hb0
  set y := y₀ - herm σ f y₀ • a - herm σ a y₀ • f with hy
  obtain ⟨hay, hfy⟩ := herm_proj_pair hσ ha hf haf y₀
  rw [← hy] at hay hfy
  have hby : herm σ b y = herm σ b y₀ := by simp [hy, hba, hbf]
  have hya : herm σ y a = 0 := herm_eq_zero_comm σ hσ.invol hay
  have hyf : herm σ y f = 0 := herm_eq_zero_comm σ hσ.invol hfy
  have hay1 : herm σ a (f + y) = 1 := by rw [herm_add_right, haf, hay, add_zero]
  obtain ⟨c, hc⟩ := exists_isotropize hσ ha hay1
  refine ⟨f + y + c • a, hc, ?_, ?_⟩
  · rw [herm_add_right, hay1, herm_smul_right, ha, mul_zero, add_zero]
    exact one_ne_zero
  · simp only [herm_add_right, herm_smul_right, hbf, hba, hby, zero_add, mul_zero, add_zero]
    exact hy₀

theorem exists_iso_perp (hσ : IsUnitaryInvolution σ) {a b : Fin n → K} (ha0 : a ≠ 0)
    (ha : herm σ a a = 0) (hb : herm σ b b = 0) (hab : herm σ a b = 0)
    (hba : ∀ c : K, b ≠ c • a) :
    ∃ d, herm σ d d = 0 ∧ herm σ a d = 0 ∧ herm σ b d ≠ 0 := by
  obtain ⟨f, hf, haf⟩ := exists_partner hσ ha0 ha
  have hfa : herm σ f a = 1 := by rw [herm_conj σ hσ.invol, haf, map_one]
  have hba' : herm σ b a = 0 := herm_eq_zero_comm σ hσ.invol hab
  set w := b - herm σ f b • a with hw
  have hw0 : w ≠ 0 := fun h => hba (herm σ f b) (sub_eq_zero.mp h)
  have haw : herm σ a w = 0 := by simp [hw, ha, hab]
  have hfw : herm σ f w = 0 := by simp [hw, hfa]
  have hww : herm σ w w = 0 := by simp [hw, ha, hb, hab, hba']
  have hwa : herm σ w a = 0 := herm_eq_zero_comm σ hσ.invol haw
  have hwf : herm σ w f = 0 := herm_eq_zero_comm σ hσ.invol hfw
  obtain ⟨y₀, hy₀⟩ := exists_herm_ne_zero σ hw0
  set y := y₀ - herm σ f y₀ • a - herm σ a y₀ • f with hy
  obtain ⟨hay, -⟩ := herm_proj_pair hσ ha hf haf y₀
  rw [← hy] at hay
  have hwy : herm σ w y = herm σ w y₀ := by simp [hy, hwa, hwf]
  set y₁ := (herm σ w y)⁻¹ • y with hy₁
  have hwy₁ : herm σ w y₁ = 1 := by
    rw [hy₁, herm_smul_right, inv_mul_cancel₀ (by rw [hwy]; exact hy₀)]
  have hay₁ : herm σ a y₁ = 0 := by rw [hy₁, herm_smul_right, hay, mul_zero]
  obtain ⟨c, hc⟩ := exists_isotropize hσ hww hwy₁
  refine ⟨y₁ + c • w, hc, ?_, ?_⟩
  · rw [herm_add_right, hay₁, herm_smul_right, haw, mul_zero, add_zero]
  · have hbw : b = w + herm σ f b • a := by rw [hw]; abel
    rw [hbw]
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hwy₁, hww,
      hay₁, haw]
    simp

end CFSGOutside.HallPaige.Unitary
