import CFSGOutside.VanDamHaemersGD12.Cage

/-!
# The Tutte 12-cage has the spectrum of van Dam-Haemers, Table 4, entry `GD(1,2)`

Every eigenvalue `λ` of `A` satisfies `λ⁷ + 84 λ³ = 17 λ⁵ + 108 λ`, so it is one of `0, ±3, ±√6, ±√2`. The
traces of `A^0, …, A^6` then fix the seven multiplicities, and the characteristic polynomial is
`(x - 3)(x + 3) x²⁸ (x² - 6)²¹ (x² - 2)²⁷`.
-/

namespace CFSGOutside.VanDamHaemersGD12

open Matrix Polynomial Finset CFSGOutside.VanDamHaemers

local notation "e" => eig cage

lemma eig_root (i : Fin 126) : e i ^ 7 + 84 * e i ^ 3 = 17 * e i ^ 5 + 108 * e i := by
  have h := minpoly_eq
  simp only [adj_pow_eq cage, conj_smul, conj_add] at h
  have h' := congrArg (fun M => star (U cage) * M * U cage) h
  have key : ∀ d : Fin 126 → ℝ, star (U cage) * (U cage * diagonal d * star (U cage)) * U cage = diagonal d := by
    intro d
    simp only [← Matrix.mul_assoc, U_star_mul cage, Matrix.one_mul]
    rw [Matrix.mul_assoc, U_star_mul cage, Matrix.mul_one]
  simp only [key] at h'
  have := congrFun (diagonal_injective h') i
  simpa using this

lemma sqrt6_pos : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
lemma sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
lemma sqrt2_lt_sqrt6 : Real.sqrt 2 < Real.sqrt 6 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
lemma sqrt6_lt_three : Real.sqrt 6 < 3 := by
  rw [show (3 : ℝ) = Real.sqrt 9 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

lemma eig_cases (i : Fin 126) : e i = 3 ∨ e i = -3 ∨ e i = 0 ∨ e i = Real.sqrt 6 ∨ e i = -Real.sqrt 6 ∨
    e i = Real.sqrt 2 ∨ e i = -Real.sqrt 2 := by
  have h := eig_root i
  have hf : e i * (e i ^ 2 - 9) * (e i ^ 2 - 6) * (e i ^ 2 - 2) = 0 := by linear_combination h
  rcases mul_eq_zero.1 hf with hf | h2
  · rcases mul_eq_zero.1 hf with hf | h6
    · rcases mul_eq_zero.1 hf with h0 | h9
      · exact Or.inr (Or.inr (Or.inl h0))
      · have : (e i - 3) * (e i + 3) = 0 := by linear_combination h9
        rcases mul_eq_zero.1 this with h | h
        · exact Or.inl (by linarith)
        · exact Or.inr (Or.inl (by linarith))
    · have : (e i - Real.sqrt 6) * (e i + Real.sqrt 6) = 0 := by
        linear_combination h6 - Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))
  · have : (e i - Real.sqrt 2) * (e i + Real.sqrt 2) = 0 := by
      linear_combination h2 - Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by linarith))))))

/-- The multiplicity of `r` as an eigenvalue, as a real number. -/
noncomputable def mult (r : ℝ) : ℝ := ∑ i, if e i = r then 1 else 0

lemma decomp (f : ℝ → ℝ) : ∑ i, f (e i) = mult 3 * f 3 + mult (-3) * f (-3) + mult 0 * f 0 +
    mult (Real.sqrt 6) * f (Real.sqrt 6) + mult (-Real.sqrt 6) * f (-Real.sqrt 6) +
    mult (Real.sqrt 2) * f (Real.sqrt 2) + mult (-Real.sqrt 2) * f (-Real.sqrt 2) := by
  have h6 := sqrt6_pos; have h2 := sqrt2_pos; have h26 := sqrt2_lt_sqrt6; have h63 := sqrt6_lt_three
  have pt : ∀ i, f (e i) = (if e i = 3 then 1 else 0) * f 3 + (if e i = -3 then 1 else 0) * f (-3) +
      (if e i = 0 then 1 else 0) * f 0 + (if e i = Real.sqrt 6 then 1 else 0) * f (Real.sqrt 6) +
      (if e i = -Real.sqrt 6 then 1 else 0) * f (-Real.sqrt 6) +
      (if e i = Real.sqrt 2 then 1 else 0) * f (Real.sqrt 2) +
      (if e i = -Real.sqrt 2 then 1 else 0) * f (-Real.sqrt 2) := by
    intro i
    rcases eig_cases i with h | h | h | h | h | h | h <;> rw [h] <;>
      split_ifs <;> first | contradiction | (exfalso; linarith) | ring
  simp only [pt, Finset.sum_add_distrib, ← Finset.sum_mul, mult]

lemma mult_eqs : mult 3 = 1 ∧ mult (-3) = 1 ∧ mult 0 = 28 ∧ mult (Real.sqrt 6) = 21 ∧
    mult (-Real.sqrt 6) = 21 ∧ mult (Real.sqrt 2) = 27 ∧ mult (-Real.sqrt 2) = 27 := by
  have tr : ∀ k, ∑ i, e i ^ k = (traceW k : ℝ) := fun k => by
    rw [← trace_eq_traceW, adj_pow_eq, VanDamHaemers.trace_conj]; rfl
  have hk : ∀ k, mult 3 * 3 ^ k + mult (-3) * (-3) ^ k + mult 0 * 0 ^ k +
      mult (Real.sqrt 6) * Real.sqrt 6 ^ k + mult (-Real.sqrt 6) * (-Real.sqrt 6) ^ k +
      mult (Real.sqrt 2) * Real.sqrt 2 ^ k + mult (-Real.sqrt 2) * (-Real.sqrt 2) ^ k = (traceW k : ℝ) :=
    fun k => by rw [← tr, decomp (· ^ k)]
  have ha2 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hb2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set a := Real.sqrt 6
  set b := Real.sqrt 2
  set n3 := mult 3; set m3 := mult (-3); set n0 := mult 0
  set na := mult a; set ma := mult (-a); set nb := mult b; set mb := mult (-b)
  have h0 := hk 0; have h1 := hk 1; have h2 := hk 2; have h3 := hk 3; have h4 := hk 4
  have h5 := hk 5; have h6 := hk 6
  rw [traceW_0] at h0; rw [traceW_1] at h1; rw [traceW_2] at h2; rw [traceW_3] at h3
  rw [traceW_4] at h4; rw [traceW_5] at h5; rw [traceW_6] at h6
  push_cast at h0 h1 h2 h3 h4 h5 h6
  have e0 : m3 + ma + mb + n0 + n3 + na + nb = 126 := by linear_combination h0
  have e1 : -a*ma + a*na - b*mb + b*nb - 3*m3 + 3*n3 = 0 := by linear_combination h1
  have e2 : 9*m3 + 6*ma + 2*mb + 9*n3 + 6*na + 2*nb = 378 := by
    linear_combination h2 - (ma + na) * ha2 - (mb + nb) * hb2
  have e3 : -6*a*ma + 6*a*na - 2*b*mb + 2*b*nb - 27*m3 + 27*n3 = 0 := by
    linear_combination h3 + a * (ma - na) * ha2 + b * (mb - nb) * hb2
  have e4 : 81*m3 + 36*ma + 4*mb + 81*n3 + 36*na + 4*nb = 1890 := by
    linear_combination h4 - (a ^ 2 + 6) * (ma + na) * ha2 - (b ^ 2 + 2) * (mb + nb) * hb2
  have e5 : -36*a*ma + 36*a*na - 4*b*mb + 4*b*nb - 243*m3 + 243*n3 = 0 := by
    linear_combination h5 + a * (a ^ 2 + 6) * (ma - na) * ha2 + b * (b ^ 2 + 2) * (mb - nb) * hb2
  have e6 : 729*m3 + 216*ma + 8*mb + 729*n3 + 216*na + 8*nb = 10962 := by
    linear_combination h6 - (ma + na) * (a ^ 4 + 6 * a ^ 2 + 36) * ha2 -
      (mb + nb) * (b ^ 4 + 2 * b ^ 2 + 4) * hb2
  have d3 : n3 - m3 = 0 := by linarith
  have da : a * (na - ma) = 0 := by linarith
  have db : b * (nb - mb) = 0 := by linarith
  have da' : na - ma = 0 := (mul_eq_zero.1 da).resolve_left sqrt6_pos.ne'
  have db' : nb - mb = 0 := (mul_eq_zero.1 db).resolve_left sqrt2_pos.ne'
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

lemma count_cast (s : Multiset ℝ) (x : ℝ) :
    (s.count x : ℝ) = (s.map fun y => if y = x then (1 : ℝ) else 0).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.count_cons, Multiset.map_cons, Multiset.sum_cons]
    push_cast
    rw [ih]
    by_cases h : a = x
    · subst h; simp; ring
    · simp [h, Ne.symm h]

/-- The eigenvalues of the Tutte 12-cage form the multiset `tutteSpectrum`. -/
lemma eig_multiset_cage : Finset.univ.val.map e = tutteSpectrum := by
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := mult_eqs
  ext x
  apply Nat.cast_injective (R := ℝ)
  rw [count_cast, count_cast, sum_tutteSpectrum, Multiset.map_map]
  have := decomp (fun y => if y = x then (1 : ℝ) else 0)
  simp only [Function.comp_def]
  rw [show (Finset.univ.val.map fun i => if e i = x then (1 : ℝ) else 0).sum =
      ∑ i, (if e i = x then (1 : ℝ) else 0) from rfl, this, m1, m2, m3, m4, m5, m6, m7]
  ring

/-- **The Tutte 12-cage has the spectrum of van Dam-Haemers, Table 4, entry `GD(1,2)`:** its adjacency
characteristic polynomial is `(x - 3)(x + 3) x²⁸ (x² - 6)²¹ (x² - 2)²⁷`. -/
theorem cage_charpoly : (cage.adjMatrix ℝ).charpoly = spectrumPoly := by
  rw [(adj_isHermitian cage).charpoly_eq, spectrumPoly, ← eig_multiset_cage, Multiset.map_map,
    Finset.prod_eq_multiset_prod]
  simp only [RCLike.ofReal_real_eq_id, id, Function.comp_def]

end CFSGOutside.VanDamHaemersGD12
