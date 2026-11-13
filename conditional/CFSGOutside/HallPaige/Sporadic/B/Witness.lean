import CFSGOutside.HallPaige.Sporadic.B.Model
import CFSGOutside.HallPaige.Sporadic.B.KP
import CFSGOutside.HallPaige.Sporadic.B.KM0
import CFSGOutside.HallPaige.Sporadic.B.KN2
import CFSGOutside.HallPaige.Sporadic.B.KV2
import CFSGOutside.HallPaige.Sporadic.B.KW2
import CFSGOutside.HallPaige.Sporadic.B.KU
import CFSGOutside.HallPaige.Sporadic.B.KM0sq
import CFSGOutside.HallPaige.Sporadic.B.KM0rk
import CFSGOutside.HallPaige.Sporadic.B.KN2sq
import CFSGOutside.HallPaige.Sporadic.B.KN2rk
import CFSGOutside.HallPaige.Sporadic.B.KV2sq
import CFSGOutside.HallPaige.Sporadic.B.KV2rk
import CFSGOutside.HallPaige.Sporadic.B.KW2sq
import CFSGOutside.HallPaige.Sporadic.B.KW2rk
import CFSGOutside.HallPaige.Sporadic.B.KUsq
import CFSGOutside.HallPaige.Sporadic.B.KUrk
import CFSGOutside.HallPaige.Sporadic.B.Kwf

/-!
# The witness triangles of `B`, from the kernel checks

The kernel checks `Sporadic/B/K*.lean` and the corpus soundness theorems of the strip engine
(`stripMat_mul_of_allStrips`, `stripMat_mul_eq_one`, `rank_sub_one_of_cert`) give, with
`p = a₁ τ₁ a₁⁻¹`:

* `s₄ · e s₄ e⁻¹ ∈ 2B` (orbital `0`);
* `α s₄ ∈ 2C` (orbital `1`);
* `(α p)²`, `(τ₁ p)²`, `(p s₄)² ∈ 2B` with `αp`, `τ₁p`, `ps₄` of order 4 (orbital `3`).
-/

namespace CFSGOutside.HallPaige.B

open CFSGOutside.Corpus.B CFSGOutside.Corpus.B.Blueprint CFSGOutside.Corpus.B.Monster.GMS
  CFSGOutside.Corpus.B.KC.BM

local notation "𝔹" => NativeSporadic.B

section Kernel

variable [Theorems]

theorem prod_eq {Ws : List (List Nat)} {A C : List Nat} (hW : ∀ W ∈ Ws, wfMat W = true)
    (hA : wfMat A = true) (h : allStripsB Ws A C = true) :
    (Ws.map stripMat).foldl (· * ·) (stripMat A) = stripMat C :=
  Theorems.stripMat_mul_of_allStrips hW hA (allStrips_of_allStripsB h)

theorem sq_eq_one {A : List Nat} (hA : wfMat A = true) (h : allStripsB [A] A idStrips = true) :
    stripMat A * stripMat A = 1 := by
  simpa using Theorems.stripMat_mul_eq_one (Ws := [A]) (by simpa using hA) hA
    (allStrips_of_allStripsB h)

theorem rank_eq {M P R : List Nat} {k : Nat} (hk : k ≤ 4370) (hM : wfMat M = true)
    (h : rankChk M P R k = true) : (stripMat M - 1).rank = k := by
  obtain ⟨hP, hR, hX, hs, he⟩ := rankChk_spec h
  exact Theorems.rank_sub_one_of_cert hk hM hP hR hX hs he

theorem matP : stripMat Seeds.A1 * stripMat Seven.t1 * stripMat Seeds.A1 = stripMat Cert.P := by
  simpa using prod_eq (by simp [wf_t1, wf_A1]) wf_A1 kP

theorem matM0 : stripMat SevenLocal.s4 * stripMat Seven.e3 * stripMat SevenLocal.s4 *
    stripMat Seven.e3 * stripMat Seven.e3 = stripMat Cert.M0 := by
  simpa using prod_eq (by simp [wf_e3, wf_s4]) wf_s4 kM0

theorem matN2 : stripMat Cert.P * stripMat SevenLocal.s4 * stripMat Cert.P * stripMat SevenLocal.s4 =
    stripMat Cert.N2 := by
  simpa using prod_eq (by simp [wf_s4, wf_P]) wf_P kN2

theorem matV2 : stripMat Seven.al * stripMat Cert.P * stripMat Seven.al * stripMat Cert.P =
    stripMat Cert.V2 := by
  simpa using prod_eq (by simp [wf_al, wf_P]) wf_al kV2

theorem matW2 : stripMat Seven.t1 * stripMat Cert.P * stripMat Seven.t1 * stripMat Cert.P =
    stripMat Cert.W2 := by
  simpa using prod_eq (by simp [wf_t1, wf_P]) wf_t1 kW2

theorem matU : stripMat Seven.al * stripMat SevenLocal.s4 = stripMat Cert.U := by
  simpa using prod_eq (by simp [wf_s4]) wf_al kU

theorem mat_pp' : mat pp = stripMat Cert.P := by rw [mat_pp, matP]

/-- `s₄ · e s₄ e⁻¹ ∈ 2B`. -/
theorem sFour_conj_orbit : BabyOrbit 0 sFour (ee * sFour * ee⁻¹) := by
  have e : mat (sFour * (ee * sFour * ee⁻¹)) = stripMat Cert.M0 := by
    rw [mat_mul, mat_mul, mat_mul, mat_ee_inv, mat_sFour, mat_ee, pow_two, ← matM0]
    simp only [mul_assoc]
  refine babyOrbit_zero_of ?_ ?_ <;> rw [e]
  · exact sq_eq_one wf_M0 kM0sq
  · exact rank_eq (by norm_num) wf_M0 kM0rk

/-- `α s₄ ∈ 2C`. -/
theorem alpha_sFour_orbit : BabyOrbit 1 alpha sFour := by
  have e : mat (alpha * sFour) = stripMat Cert.U := matU
  refine babyOrbit_one_of ?_ ?_ <;> rw [e]
  · exact sq_eq_one wf_U kUsq
  · exact rank_eq (by norm_num) wf_U kUrk

/-- `(p s₄)² ∈ 2B`, `p s₄` of order 4. -/
theorem pp_sFour_orbit : BabyOrbit 3 pp sFour := by
  have e : mat ((pp * sFour) ^ 2) = stripMat Cert.N2 := by
    rw [mat_sq, mat_mul, mat_pp', mat_sFour, ← matN2]
    simp only [mul_assoc]
  refine babyOrbit_three_of ?_ ?_ <;> rw [e]
  · exact sq_eq_one wf_N2 kN2sq
  · exact rank_eq (by norm_num) wf_N2 kN2rk

/-- `(α p)² ∈ 2B`, `α p` of order 4. -/
theorem alpha_pp_orbit : BabyOrbit 3 alpha pp := by
  have e : mat ((alpha * pp) ^ 2) = stripMat Cert.V2 := by
    rw [mat_sq, mat_mul, mat_pp', mat_alpha, ← matV2]
    simp only [mul_assoc]
  refine babyOrbit_three_of ?_ ?_ <;> rw [e]
  · exact sq_eq_one wf_V2 kV2sq
  · exact rank_eq (by norm_num) wf_V2 kV2rk

/-- `(τ₁ p)² ∈ 2B`, `τ₁ p` of order 4. -/
theorem tau_pp_orbit : BabyOrbit 3 tau pp := by
  have e : mat ((tau * pp) ^ 2) = stripMat Cert.W2 := by
    rw [mat_sq, mat_mul, mat_pp', mat_tau, ← matW2]
    simp only [mul_assoc]
  refine babyOrbit_three_of ?_ ?_ <;> rw [e]
  · exact sq_eq_one wf_W2 kW2sq
  · exact rank_eq (by norm_num) wf_W2 kW2rk

end Kernel

end CFSGOutside.HallPaige.B
