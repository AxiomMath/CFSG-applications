import CFSGOutside.Sutherland.Defs

/-!
# 2×2 matrix lemmas for Sutherland's criterion

Elementary facts about `2 × 2` matrices over a field: Cayley–Hamilton, centralizers of
non-scalar matrices, discriminants, and powers.
-/

open Matrix

namespace CFSGOutside.Sutherland

variable {K : Type*} [Field K]

/-- A `2 × 2` matrix is scalar. -/
def IsScalar (M : Matrix (Fin 2) (Fin 2) K) : Prop :=
  M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 0 0 = M 1 1

theorem trace_two (M : Matrix (Fin 2) (Fin 2) K) : M.trace = M 0 0 + M 1 1 := by
  simp [Matrix.trace_fin_two]

theorem det_two (M : Matrix (Fin 2) (Fin 2) K) : M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 :=
  Matrix.det_fin_two M

theorem trace_smul_one_add (a b : K) (c : Matrix (Fin 2) (Fin 2) K) :
    (a • (1 : Matrix (Fin 2) (Fin 2) K) + b • c).trace = 2 * a + b * c.trace := by
  simp [trace_two]
  ring

theorem det_smul_one_add (a b : K) (c : Matrix (Fin 2) (Fin 2) K) :
    (a • (1 : Matrix (Fin 2) (Fin 2) K) + b • c).det =
      a ^ 2 + a * b * c.trace + b ^ 2 * c.det := by
  simp [det_two, trace_two]
  ring

theorem disc_smul_one_add (a b : K) (c : Matrix (Fin 2) (Fin 2) K) :
    disc (a • (1 : Matrix (Fin 2) (Fin 2) K) + b • c) = b ^ 2 * disc c := by
  rw [disc, disc, trace_smul_one_add, det_smul_one_add]
  ring

/-- The centralizer of a non-scalar `2 × 2` matrix `c` is `K[c]`. -/
theorem exists_eq_of_commute {c g : Matrix (Fin 2) (Fin 2) K} (hc : ¬ IsScalar c)
    (hgc : g * c = c * g) : ∃ a b : K, g = a • 1 + b • c := by
  have e00 := congrFun (congrFun hgc 0) 0
  have e01 := congrFun (congrFun hgc 0) 1
  have e10 := congrFun (congrFun hgc 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  -- `(g 0 1, g 1 0, g 0 0 - g 1 1)` is proportional to `(c 0 1, c 1 0, c 0 0 - c 1 1)`
  obtain ⟨b, hb1, hb2, hb3⟩ : ∃ b : K, g 0 1 = b * c 0 1 ∧ g 1 0 = b * c 1 0 ∧
      g 0 0 - g 1 1 = b * (c 0 0 - c 1 1) := by
    unfold IsScalar at hc
    by_cases h1 : c 0 1 = 0
    · by_cases h2 : c 1 0 = 0
      · have h3 : c 0 0 - c 1 1 ≠ 0 := fun h => hc ⟨h1, h2, sub_eq_zero.mp h⟩
        refine ⟨(g 0 0 - g 1 1) / (c 0 0 - c 1 1), ?_, ?_, ?_⟩
        · have : g 0 1 * (c 0 0 - c 1 1) = 0 := by rw [h1] at e01; linear_combination -e01
          rw [h1, mul_zero]
          exact (mul_eq_zero.mp this).resolve_right h3
        · have : g 1 0 * (c 0 0 - c 1 1) = 0 := by rw [h2] at e10; linear_combination e10
          rw [h2, mul_zero]
          exact (mul_eq_zero.mp this).resolve_right h3
        · field_simp
      · refine ⟨g 1 0 / c 1 0, ?_, ?_, ?_⟩
        · rw [h1, mul_zero]
          have : g 0 1 * c 1 0 = 0 := by rw [h1] at e00; linear_combination e00
          exact (mul_eq_zero.mp this).resolve_right h2
        · field_simp
        · field_simp
          linear_combination -e10
    · refine ⟨g 0 1 / c 0 1, ?_, ?_, ?_⟩
      · field_simp
      · field_simp
        linear_combination -e00
      · field_simp
        linear_combination e01
  refine ⟨g 1 1 - b * c 1 1, b, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination hb3
  · exact hb1
  · exact hb2

theorem sub_half_trace_sq (h2 : (2 : K) ≠ 0) (c : Matrix (Fin 2) (Fin 2) K) :
    (c - (c.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) K)) *
      (c - (c.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) K)) =
      (disc c / 4) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, disc, trace_two, det_two] <;>
    field_simp <;> ring

/-- If `g` normalises `K[c]` (`c` with nonzero discriminant) by sending `c` to `tr c - c`, then
`tr g = 0`. -/
theorem trace_eq_zero_of_anticommute (h2 : (2 : K) ≠ 0) {c g : Matrix (Fin 2) (Fin 2) K}
    (hd : disc c ≠ 0) (h : g * c + c * g = c.trace • g) : g.trace = 0 := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  set c₀ := c - (c.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) K)
  have hanti : g * c₀ = -(c₀ * g) := by
    rw [eq_neg_iff_add_eq_zero]
    calc g * c₀ + c₀ * g = (g * c + c * g) - (c.trace / 2 + c.trace / 2) • g := by
          simp only [c₀, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
          rw [add_smul]
          abel
      _ = 0 := by
          rw [h, show c.trace / 2 + c.trace / 2 = c.trace by
            rw [← add_div, div_eq_iff h2]; ring, sub_self]
  have hsq : c₀ * c₀ = (disc c / 4) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [c₀, Matrix.mul_apply, Fin.sum_univ_two, disc, trace_two, det_two] <;>
      field_simp <;> ring
  have htr : (c₀ * g * c₀).trace = (c₀ * (c₀ * g)).trace := Matrix.trace_mul_comm _ _
  rw [mul_assoc, hanti, mul_neg, Matrix.trace_neg, ← mul_assoc, hsq, smul_mul_assoc, one_mul,
    Matrix.trace_smul, smul_eq_mul] at htr
  have h0 : 2 * (disc c / 4 * g.trace) = 0 := by linear_combination -htr
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd h h2
  · exact (mul_eq_zero.mp h).resolve_left (div_ne_zero hd h4)

/-- A matrix commuting with `c` with the same trace and determinant as `c` (of nonzero
discriminant, `c` non-scalar) is `c` or `tr c - c`. -/
theorem eq_or_eq_of_commute (h2 : (2 : K) ≠ 0) {c c' : Matrix (Fin 2) (Fin 2) K}
    (hc : ¬ IsScalar c) (hd : disc c ≠ 0) (hcc : c' * c = c * c') (htr : c'.trace = c.trace)
    (hdet : c'.det = c.det) :
    c' = c ∨ c' = c.trace • (1 : Matrix (Fin 2) (Fin 2) K) - c := by
  obtain ⟨a, b, rfl⟩ := exists_eq_of_commute hc hcc
  rw [trace_smul_one_add] at htr
  rw [det_smul_one_add] at hdet
  have hb : (b - 1) * (b + 1) * disc c = 0 := by
    unfold disc
    linear_combination (-(4 : K)) * hdet + (2 * a + b * c.trace + c.trace) * htr
  rcases mul_eq_zero.mp hb with hb | hb
  · rcases mul_eq_zero.mp hb with hb | hb
    · have hb1 : b = 1 := by linear_combination hb
      subst hb1
      have ha : a = 0 := by
        have : 2 * a = 0 := by linear_combination htr
        exact (mul_eq_zero.mp this).resolve_left h2
      left
      simp [ha]
    · have hb1 : b = -1 := by linear_combination hb
      subst hb1
      have ha : a = c.trace := by
        have : 2 * (a - c.trace) = 0 := by linear_combination htr
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2)
      right
      rw [ha, neg_one_smul, sub_eq_add_neg]
  · exact absurd hb hd

/-- If `a • M + b • 1` is scalar and `M` is not, then `a = 0`. -/
theorem eq_zero_of_isScalar {M : Matrix (Fin 2) (Fin 2) K} (hM : ¬ IsScalar M) {a b : K}
    (h : IsScalar (a • M + b • (1 : Matrix (Fin 2) (Fin 2) K))) : a = 0 := by
  obtain ⟨h1, h2, h3⟩ := h
  simp at h1 h2 h3
  by_contra ha
  apply hM
  exact ⟨h1.resolve_left ha, h2.resolve_left ha, h3.resolve_right ha⟩

theorem pow_two_eq (M : Matrix (Fin 2) (Fin 2) K) :
    M ^ 2 = M.trace • M + (-M.det) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, trace_two, det_two] <;> ring

theorem pow_three_eq (M : Matrix (Fin 2) (Fin 2) K) :
    M ^ 3 = (M.trace ^ 2 - M.det) • M +
      (-(M.trace * M.det)) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, trace_two, det_two] <;> ring

theorem pow_four_eq (M : Matrix (Fin 2) (Fin 2) K) :
    M ^ 4 = (M.trace ^ 3 - 2 * M.trace * M.det) • M +
      (-((M.trace ^ 2 - M.det) * M.det)) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, trace_two, det_two] <;> ring

theorem pow_five_eq (M : Matrix (Fin 2) (Fin 2) K) :
    M ^ 5 = (M.trace ^ 4 - 3 * M.trace ^ 2 * M.det + M.det ^ 2) • M +
      (-((M.trace ^ 3 - 2 * M.trace * M.det) * M.det)) •
        (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, trace_two, det_two] <;> ring

/-- If `M^k` is scalar for some `1 ≤ k ≤ 5`, then `u = tr² / det` is `0`, `1`, `2` or `4`, or
satisfies `u² - 3u + 1 = 0`. -/
theorem u_cases (h2 : (2 : K) ≠ 0) {M : Matrix (Fin 2) (Fin 2) K} (hd : M.det ≠ 0) {k : ℕ}
    (hk1 : 1 ≤ k) (hk5 : k ≤ 5) (hs : IsScalar (M ^ k)) :
    let u := M.trace ^ 2 / M.det
    u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 4 ∨ u ^ 2 - 3 * u + 1 = 0 := by
  intro u
  by_cases hM : IsScalar M
  · -- `M = m • 1`, so `u = 4`
    right; right; right; left
    obtain ⟨h01, h10, h00⟩ := hM
    have htr : M.trace = 2 * M 1 1 := by rw [trace_two, h00]; ring
    have hdet : M.det = M 1 1 ^ 2 := by rw [det_two, h00, h01, h10]; ring
    have hm : M 1 1 ≠ 0 := fun h => hd (by rw [hdet, h]; ring)
    simp only [u, htr, hdet]
    field_simp
    norm_num
  · interval_cases k
    · exact absurd (by simpa using hs) hM
    · rw [pow_two_eq] at hs
      have := eq_zero_of_isScalar hM hs
      left
      simp [u, this]
    · rw [pow_three_eq] at hs
      have := eq_zero_of_isScalar hM hs
      right; left
      simp only [u]
      rw [div_eq_one_iff_eq hd]
      linear_combination this
    · rw [pow_four_eq] at hs
      have h := eq_zero_of_isScalar hM hs
      have : M.trace * (M.trace ^ 2 - 2 * M.det) = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h' | h'
      · left; simp only [u]; rw [h']; simp
      · right; right; left
        simp only [u]
        rw [div_eq_iff hd]
        linear_combination h'
    · rw [pow_five_eq] at hs
      have h := eq_zero_of_isScalar hM hs
      right; right; right; right
      have e : u ^ 2 - 3 * u + 1 =
          (M.trace ^ 4 - 3 * M.trace ^ 2 * M.det + M.det ^ 2) / M.det ^ 2 := by
        simp only [u]; field_simp
      rw [e, h, zero_div]

/-- An eigenvector with eigenvalue in the field makes the discriminant a square. -/
theorem disc_eq_sq_of_eigen {M : Matrix (Fin 2) (Fin 2) K} {w : Fin 2 → K} (hw : w ≠ 0)
    {c : K} (h : M *ᵥ w = c • w) : disc M = (2 * c - M.trace) ^ 2 := by
  have h0 : (M - c • (1 : Matrix (Fin 2) (Fin 2) K)) *ᵥ w = 0 := by
    rw [Matrix.sub_mulVec, h, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
  have hdet : (M - c • (1 : Matrix (Fin 2) (Fin 2) K)).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hw, h0⟩
  rw [det_two] at hdet
  simp at hdet
  rw [disc, trace_two, det_two]
  linear_combination (-4 : K) * hdet

/-- A non-scalar `M` with zero discriminant and `M ^ m = 1` has `(m : K) = 0`. -/
theorem natCast_eq_zero_of_disc_eq_zero (h2 : (2 : K) ≠ 0) {M : Matrix (Fin 2) (Fin 2) K}
    (hM : ¬ IsScalar M) (hd : disc M = 0) (hdet : M.det ≠ 0) {m : ℕ}
    (hm : M ^ m = 1) : (m : K) = 0 := by
  set l := M.trace / 2
  set N := M - l • (1 : Matrix (Fin 2) (Fin 2) K)
  have hN : N * N = 0 := by
    rw [sub_half_trace_sq h2, hd, zero_div, zero_smul]
  have hMN : M = l • (1 : Matrix (Fin 2) (Fin 2) K) + N := by simp [N]
  have hpow : ∀ n : ℕ, M ^ (n + 1) = (l ^ (n + 1)) • (1 : Matrix (Fin 2) (Fin 2) K) +
      ((n + 1 : K) * l ^ n) • N := by
    intro n
    induction n with
    | zero => simp [hMN]
    | succ n ih =>
      rw [pow_succ, ih, hMN]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul,
        hN, smul_zero, add_zero]
      push_cast
      module
  have hNs : ¬ IsScalar N := by
    intro ⟨h1, h2', h3⟩
    apply hM
    simp [N] at h1 h2' h3
    exact ⟨h1, h2', by linear_combination h3⟩
  have hl : l ≠ 0 := by
    intro hl
    apply hdet
    unfold disc at hd
    have : M.trace = 0 := by
      have := hl; simp only [l] at this; field_simp at this; simpa using this
    rw [this] at hd
    have h4 : (4 : K) ≠ 0 := by
      rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
    have : 4 * M.det = 0 := by linear_combination -hd
    exact (mul_eq_zero.mp this).resolve_left h4
  rcases m with _ | m
  · simp
  · rw [hpow m] at hm
    have hs : IsScalar (((m + 1 : K) * l ^ m) • N + (l ^ (m + 1)) •
        (1 : Matrix (Fin 2) (Fin 2) K)) := by
      rw [add_comm, hm]; exact ⟨by simp, by simp, by simp⟩
    have := eq_zero_of_isScalar hNs hs
    push_cast
    exact (mul_eq_zero.mp this).resolve_right (pow_ne_zero _ hl)

/-- The fixed vectors of a non-identity `2 × 2` matrix lie on a line. -/
theorem eq_smul_of_fixed {X : Matrix (Fin 2) (Fin 2) K} (hX : X ≠ 1) {w v : Fin 2 → K}
    (hw : w ≠ 0) (hXw : X *ᵥ w = w) (hXv : X *ᵥ v = v) : ∃ c : K, v = c • w := by
  have ew0 := congrFun hXw 0
  have ew1 := congrFun hXw 1
  have ev0 := congrFun hXv 0
  have ev1 := congrFun hXv 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at ew0 ew1 ev0 ev1
  by_cases hD : w 0 * v 1 - w 1 * v 0 = 0
  · by_cases h0 : w 0 = 0
    · have h1 : w 1 ≠ 0 := by
        intro h1; apply hw; ext i; fin_cases i <;> simp [h0, h1]
      refine ⟨v 1 / w 1, ?_⟩
      ext i
      fin_cases i
      · simp [h0]
        have : w 1 * v 0 = 0 := by linear_combination -hD + v 1 * h0
        exact (mul_eq_zero.mp this).resolve_left h1
      · simp; field_simp
    · refine ⟨v 0 / w 0, ?_⟩
      ext i
      fin_cases i
      · simp; field_simp
      · simp; field_simp; linear_combination hD
  · exfalso
    apply hX
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · have : (X 0 0 - 1) * (w 0 * v 1 - w 1 * v 0) = 0 := by
        linear_combination v 1 * ew0 - w 1 * ev0
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hD)
    · have : X 0 1 * (w 0 * v 1 - w 1 * v 0) = 0 := by
        linear_combination w 0 * ev0 - v 0 * ew0
      exact (mul_eq_zero.mp this).resolve_right hD
    · have : X 1 0 * (w 0 * v 1 - w 1 * v 0) = 0 := by
        linear_combination v 1 * ew1 - w 1 * ev1
      exact (mul_eq_zero.mp this).resolve_right hD
    · have : (X 1 1 - 1) * (w 0 * v 1 - w 1 * v 0) = 0 := by
        linear_combination w 0 * ev1 - v 0 * ew1
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hD)

end CFSGOutside.Sutherland
