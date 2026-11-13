import CFSGOutside.HallPaige.Lie.Good
import CFSGOutside.HallPaige.DoubleCosets
import CFSGOutside.HallPaige.Cosets
import CFSGOutside.HallPaige.Sporadic.GoodOfKlein
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import CFSGOutside.HallPaige.Reduction

/-!
# The projective special linear groups

`PSL_n(K)` (`n ≥ 2`, `K` finite) acts 2-transitively on the `1 + q + ⋯ + q^{n-1} ≥ 3` points of
the projective space `ℙ(Kⁿ)`. The point stabilizer is good when `q` is even or `n` is odd (it has
odd index) and when `q` is odd and `n ≥ 4` is even (it contains a Klein four-group of diagonal
matrices). In these cases a good `PSL_n(K)` whose proper good subgroups are admissible has a
complete mapping (`CFSGOutside.HallPaige.hasCompleteMapping_PSL`).
-/

namespace CFSGOutside.HallPaige

open Matrix MulAction

section Parity

/-- The geometric sum `1 + q + ⋯ + q^{n-1}` is odd when `q` is even and `n ≥ 1`. -/
theorem odd_sum_range_pow_of_even {q : ℕ} (hq : Even q) {n : ℕ} (hn : 1 ≤ n) :
    Odd (∑ i ∈ Finset.range n, q ^ i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · simp
    · exact (ih hn').add_even ((hq.pow_of_ne_zero hn'.ne'))

/-- For odd `q`, the geometric sum `1 + q + ⋯ + q^{n-1}` has the parity of `n`. -/
theorem odd_sum_range_pow_iff_of_odd {q : ℕ} (hq : Odd q) (n : ℕ) :
    Odd (∑ i ∈ Finset.range n, q ^ i) ↔ Odd n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.odd_add, ih]
    have h2 : ¬ Even (q ^ n) := Nat.not_even_iff_odd.mpr hq.pow
    rw [Nat.odd_add_one]
    tauto

end Parity

variable {K : Type} [Field K] [Finite K]

/-- The projective special linear group acts 2-transitively on projective space. -/
theorem psl_two_transitive (n : ℕ) :
    ∀ x y x' y' : Projectivization K (Fin n → K), x ≠ y → x' ≠ y' →
      ∃ g : ProjectiveSpecialLinearGroup (Fin n) K, g • x = x' ∧ g • y = y' := by
  intro x y x' y' hxy hxy'
  obtain ⟨g, hg1, hg2⟩ := (MulAction.is_two_pretransitive_iff.1
    (inferInstance : IsMultiplyPretransitive (SpecialLinearGroup (Fin n) K)
      (Projectivization K (Fin n → K)) 2)) hxy hxy'
  exact ⟨g, by rw [ProjectiveSpecialLinearGroup.smul_proj_mk, hg1],
    by rw [ProjectiveSpecialLinearGroup.smul_proj_mk, hg2]⟩

/-- The number of points of `ℙ(Kⁿ)`. -/
theorem card_projectivization (n : ℕ) :
    Nat.card (Projectivization K (Fin n → K)) = ∑ i ∈ Finset.range n, Nat.card K ^ i :=
  Projectivization.card_of_finrank K (Fin n → K) (by simp)

/-- The base point `[e₀]` of `ℙ(Kⁿ)`. -/
noncomputable def basePoint (n : ℕ) : Projectivization K (Fin (n + 1) → K) :=
  Projectivization.mk K (Pi.single 0 1) (by simp)

/-- The stabilizer of a point has index the number of points. -/
theorem index_stabilizer_basePoint (n : ℕ) :
    (stabilizer (ProjectiveSpecialLinearGroup (Fin (n + 1)) K) (basePoint (K := K) n)).index =
      ∑ i ∈ Finset.range (n + 1), Nat.card K ^ i := by
  rw [index_stabilizer, ← card_projectivization]
  have horb : orbit (ProjectiveSpecialLinearGroup (Fin (n + 1)) K) (basePoint (K := K) n) =
      Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    by_cases hy : y = basePoint n
    · rw [hy]; exact mem_orbit_self _
    · obtain ⟨g, hg, -⟩ := psl_two_transitive (n + 1) (basePoint n) y y (basePoint n)
        (Ne.symm hy) hy
      exact ⟨g, hg⟩
  rw [horb, Set.ncard_univ]

section Klein

variable (m : ℕ)

/-- The sign vector with entries `-1` at `i` and `j` and `1` elsewhere. -/
def signVec (i j : Fin (m + 4)) : Fin (m + 4) → K :=
  fun k => (if k = i then -1 else 1) * (if k = j then -1 else 1)

omit [Finite K] in
theorem signVec_mul_self (i j : Fin (m + 4)) : signVec (K := K) m i j * signVec m i j = 1 := by
  funext k
  simp only [signVec, Pi.mul_apply, Pi.one_apply]
  split_ifs <;> simp

omit [Finite K] in
theorem prod_signVec (i j : Fin (m + 4)) (hij : i ≠ j) : ∏ k, signVec (K := K) m i j k = 1 := by
  have : signVec (K := K) m i j = Pi.mulSingle i (-1) * Pi.mulSingle j (-1) := by
    funext k; simp [signVec, Pi.mulSingle_apply]
  rw [this]
  simp only [Pi.mul_apply, Finset.prod_mul_distrib, Finset.prod_pi_mulSingle', Finset.mem_univ,
    if_true]
  norm_num

/-- The diagonal matrix with entries `-1` at `i` and `j` and `1` elsewhere. -/
noncomputable def diagNegTwo (i j : Fin (m + 4)) (hij : i ≠ j) :
    SpecialLinearGroup (Fin (m + 4)) K :=
  ⟨Matrix.diagonal (signVec m i j), by rw [det_diagonal, prod_signVec m i j hij]⟩

variable {m}

theorem coe_diagNegTwo (i j : Fin (m + 4)) (hij : i ≠ j) :
    (diagNegTwo (K := K) m i j hij : Matrix (Fin (m + 4)) (Fin (m + 4)) K) =
      Matrix.diagonal (signVec m i j) := rfl

theorem diagNegTwo_mul_self (i j : Fin (m + 4)) (hij : i ≠ j) :
    diagNegTwo (K := K) m i j hij * diagNegTwo m i j hij = 1 := by
  apply Subtype.ext
  change Matrix.diagonal (signVec (K := K) m i j) * Matrix.diagonal (signVec m i j) = 1
  rw [diagonal_mul_diagonal', ← diagonal_one]
  congr 1
  funext k
  exact congrFun (signVec_mul_self m i j) k

theorem diagNegTwo_comm (i j i' j' : Fin (m + 4)) (hij : i ≠ j) (hij' : i' ≠ j') :
    diagNegTwo (K := K) m i j hij * diagNegTwo m i' j' hij' =
      diagNegTwo m i' j' hij' * diagNegTwo m i j hij := by
  apply Subtype.ext
  change Matrix.diagonal (signVec (K := K) m i j) * Matrix.diagonal (signVec m i' j') =
    Matrix.diagonal (signVec m i' j') * Matrix.diagonal (signVec m i j)
  rw [diagonal_mul_diagonal', diagonal_mul_diagonal']
  congr 1
  funext k
  exact mul_comm _ _

/-- A diagonal matrix fixes the base point `[e₀]`. -/
theorem diagNegTwo_smul_basePoint (i j : Fin (m + 4)) (hij : i ≠ j) :
    (diagNegTwo (K := K) m i j hij : ProjectiveSpecialLinearGroup (Fin (m + 4)) K) •
      basePoint (K := K) (m + 3) = basePoint (m + 3) := by
  rw [ProjectiveSpecialLinearGroup.smul_proj_mk, basePoint, Projectivization.smul_mk,
    Projectivization.mk_eq_mk_iff]
  have h0 : signVec (K := K) m i j 0 ≠ 0 := by
    simp only [signVec]; split_ifs <;> simp
  refine ⟨Units.mk0 (signVec (K := K) m i j 0) h0, ?_⟩
  funext k
  change _ = (Matrix.diagonal (signVec (K := K) m i j) *ᵥ Pi.single 0 1) k
  rw [mulVec_diagonal]
  by_cases hk : k = 0
  · subst hk; simp
  · simp [hk]

/-- An element of `SL` whose diagonal entries at `a` and `b` differ is not central. -/
theorem not_mem_center_of_diag_ne (g : SpecialLinearGroup (Fin (m + 4)) K) {a b : Fin (m + 4)}
    (h : (g : Matrix _ _ K) a a ≠ (g : Matrix _ _ K) b b) :
    g ∉ Subgroup.center (SpecialLinearGroup (Fin (m + 4)) K) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  rintro ⟨r, -, hr⟩
  rw [← hr] at h
  simp at h

/-- **The diagonal Klein four-group.** For `q` odd and `n ≥ 4`, the point stabilizer in
`PSL_n(K)` is good. -/
theorem isGood_stabilizer_basePoint_of_four_le (hK : (-1 : K) ≠ 1) :
    IsGood (stabilizer (ProjectiveSpecialLinearGroup (Fin (m + 4)) K) (basePoint (K := K) (m + 3))) := by
  let i0 : Fin (m + 4) := ⟨0, by omega⟩
  let i1 : Fin (m + 4) := ⟨1, by omega⟩
  let i2 : Fin (m + 4) := ⟨2, by omega⟩
  let i3 : Fin (m + 4) := ⟨3, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  let u := diagNegTwo (K := K) m i0 i1 h01
  let v := diagNegTwo (K := K) m i1 i2 h12
  have hneg : ∀ {x y : K}, x = -1 → y = 1 → x ≠ y := fun hx hy => hx ▸ hy ▸ hK
  have hu1 : (u : ProjectiveSpecialLinearGroup (Fin (m + 4)) K) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    refine not_mem_center_of_diag_ne u (a := i0) (b := i2) (hneg ?_ ?_) <;>
      simp [u, coe_diagNegTwo, signVec, i0, i1, i2, Fin.ext_iff]
  have hv1 : (v : ProjectiveSpecialLinearGroup (Fin (m + 4)) K) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    refine not_mem_center_of_diag_ne v (a := i1) (b := i0) (hneg ?_ ?_) <;>
      simp [v, coe_diagNegTwo, signVec, i0, i1, i2, Fin.ext_iff]
  have huv : (u : ProjectiveSpecialLinearGroup (Fin (m + 4)) K) ≠ v := by
    rw [Ne, QuotientGroup.eq]
    have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_right (diagNegTwo_mul_self _ _ _)
    rw [hu]
    refine not_mem_center_of_diag_ne (u * v) (a := i0) (b := i3) (hneg ?_ ?_) <;>
      simp [u, v, coe_diagNegTwo, signVec, diagonal_mul_diagonal', i0, i1, i2, i3, Fin.ext_iff]
  refine Subgroup.isGood_of_commuting_involutions _ (u := (u : ProjectiveSpecialLinearGroup _ K))
    (v := v) (diagNegTwo_smul_basePoint _ _ _) (diagNegTwo_smul_basePoint _ _ _) ?_ ?_ ?_ hu1 hv1 huv
  · rw [sq, ← QuotientGroup.mk_mul, diagNegTwo_mul_self, QuotientGroup.mk_one]
  · rw [sq, ← QuotientGroup.mk_mul, diagNegTwo_mul_self, QuotientGroup.mk_one]
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, diagNegTwo_comm]

end Klein

section PSLTwo

/-- An element of `SL₂(K)` fixing the line `[e₀]` has `g₁₀ = 0`. -/
theorem SL_entry_eq_zero_of_smul_basePoint (g : SpecialLinearGroup (Fin 2) K)
    (hg : (g : ProjectiveSpecialLinearGroup (Fin 2) K) • basePoint (K := K) 1 = basePoint 1) :
    (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
  rw [ProjectiveSpecialLinearGroup.smul_proj_mk, basePoint, Projectivization.smul_mk,
    Projectivization.mk_eq_mk_iff] at hg
  obtain ⟨c, hc⟩ := hg
  have := congrFun hc 1
  change _ = ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ Pi.single 0 1) 1 at this
  simpa [mulVec, dotProduct, Fin.sum_univ_two] using this.symm

/-- **The Borel subgroup of `PSL₂(q)`, `q ≡ 3 (mod 4)`, has no involutions.** -/
theorem PSL_two_stabilizer_no_involution (hK : ¬ IsSquare (-1 : K))
    (x : ProjectiveSpecialLinearGroup (Fin 2) K) (hx : x • basePoint (K := K) 1 = basePoint 1)
    (hx2 : x ^ 2 = 1) : x = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := SL_entry_eq_zero_of_smul_basePoint g hx
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
    Matrix.SpecialLinearGroup.mem_center_iff] at hx2
  obtain ⟨r, -, hr⟩ := hx2
  rw [QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff]
  set a := (g : Matrix (Fin 2) (Fin 2) K) 0 0
  set b := (g : Matrix (Fin 2) (Fin 2) K) 0 1
  set d := (g : Matrix (Fin 2) (Fin 2) K) 1 1
  have hdet : a * d = 1 := by
    have := g.2
    rw [Matrix.det_fin_two] at this
    rw [hc, mul_zero, sub_zero] at this
    exact this
  have hsq : ∀ i j, ((g : Matrix (Fin 2) (Fin 2) K) ^ 2) i j = scalar (Fin 2) r i j := by
    intro i j; rw [hr]; rfl
  have e00 := hsq 0 0
  have e01 := hsq 0 1
  have e11 := hsq 1 1
  simp only [sq, mul_apply, Fin.sum_univ_two, scalar_apply, diagonal_apply_eq,
    diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1), hc] at e00 e01 e11
  -- e00 : a * a + b * 0 = r, e01 : a * b + b * d = 0, e11 : 0 * b + d * d = r
  have ha2 : a * a = r := by simpa using e00
  have hd2 : d * d = r := by simpa using e11
  by_cases hs : a + d = 0
  · exact absurd ⟨a, by linear_combination hdet - a * hs⟩ hK
  · have hb : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e01
      exact (mul_eq_zero.1 this).resolve_right hs
    have had : a = d := by
      have : (a - d) * (a + d) = 0 := by linear_combination ha2 - hd2
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hs)
    refine ⟨a, by rw [Fintype.card_fin, sq]; nth_rewrite 2 [had]; exact hdet, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a, b, d, hc] at hb had ⊢ <;> first | exact hb.symm | exact had | skip

/-- For `q ≡ 3 (mod 4)` the Borel subgroup of `PSL₂(q)` has odd order, hence is good. -/
theorem isGood_stabilizer_basePoint_two (hq : Nat.card K % 4 = 3) :
    IsGood (stabilizer (ProjectiveSpecialLinearGroup (Fin 2) K) (basePoint (K := K) 1)) := by
  have := Fintype.ofFinite K
  have hK : ¬ IsSquare (-1 : K) := by
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card]; omega
  apply isGood_of_odd
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite (stabilizer (ProjectiveSpecialLinearGroup (Fin 2) K) (basePoint (K := K) 1))
  rw [Nat.card_eq_fintype_card] at h2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 2 h2
  have hx1 : (x : ProjectiveSpecialLinearGroup (Fin 2) K) = 1 :=
    PSL_two_stabilizer_no_involution hK _ x.2 (by
      have h := pow_orderOf_eq_one x
      rw [hx] at h
      simpa using congrArg Subtype.val h)
  have : x = 1 := Subtype.ext hx1
  rw [this, orderOf_one] at hx
  omega

end PSLTwo

section Main

/-- Projective space of dimension at least one over a finite field has at least three points. -/
theorem three_le_card_projectivization (m : ℕ) :
    3 ≤ Nat.card (Projectivization K (Fin (m + 2) → K)) := by
  rw [card_projectivization]
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  calc 3 ≤ ∑ i ∈ Finset.range 2, Nat.card K ^ i := by
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one]; omega
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))

/-- In a finite field of odd order, `-1 ≠ 1`. -/
theorem neg_one_ne_one_of_odd_card (h : Odd (Nat.card K)) : (-1 : K) ≠ 1 := by
  have := Fintype.ofFinite K
  rw [Ne, neg_one_eq_one_iff, FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card]
  intro h2
  exact (Nat.not_even_iff_odd.2 h) (Nat.even_iff.2 h2)

/-- **Hall–Paige for `PSL_n(K)`, `n ≥ 2`, except `n = 2` with `q` odd.** -/
theorem hasCompleteMapping_PSL (m : ℕ) (hcase : Even (Nat.card K) ∨ 1 ≤ m ∨ Nat.card K % 4 = 3)
    (hG : IsGood (ProjectiveSpecialLinearGroup (Fin (m + 2)) K))
    (hP : ProperSubgroupsAdmissible (ProjectiveSpecialLinearGroup (Fin (m + 2)) K)) :
    HasCompleteMapping (ProjectiveSpecialLinearGroup (Fin (m + 2)) K) := by
  have h3 := three_le_card_projectivization (K := K) m
  refine hasCompleteMapping_of_two_transitive cosetStatement (basePoint (m + 1))
    (psl_two_transitive _) h3 (hP _ ?_ ?_)
  · intro htop
    obtain ⟨y, hy⟩ : ∃ y, y ≠ basePoint (K := K) (m + 1) := by
      by_contra h
      push Not at h
      have : Subsingleton (Projectivization K (Fin (m + 2) → K)) :=
        ⟨fun a b => (h a).trans (h b).symm⟩
      have := Finite.card_le_one_iff_subsingleton.2 this
      omega
    obtain ⟨g, hg, -⟩ := psl_two_transitive _ (basePoint (m + 1)) y y (basePoint (m + 1))
      (Ne.symm hy) hy
    have hgs : g ∈ stabilizer (ProjectiveSpecialLinearGroup (Fin (m + 2)) K)
        (basePoint (K := K) (m + 1)) := htop ▸ Subgroup.mem_top g
    exact hy (hg.symm.trans hgs)
  · by_cases hodd : Odd (∑ i ∈ Finset.range (m + 2), Nat.card K ^ i)
    · exact isGood_of_index_odd hG _ (by rw [index_stabilizer_basePoint]; exact hodd)
    · have hqodd : Odd (Nat.card K) := by
        rcases Nat.even_or_odd (Nat.card K) with he | ho
        · exact absurd (odd_sum_range_pow_of_even he (by omega)) hodd
        · exact ho
      have hm : ¬ Odd (m + 2) := by rwa [← odd_sum_range_pow_iff_of_odd hqodd]
      rcases Nat.eq_zero_or_pos m with rfl | hmpos
      · have h3' : Nat.card K % 4 = 3 := by
          rcases hcase with h | h | h
          · exact absurd h (Nat.not_even_iff_odd.2 hqodd)
          · omega
          · exact h
        exact isGood_stabilizer_basePoint_two h3'
      · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by
          rcases Nat.even_or_odd m with ⟨j, hj⟩ | ho
          · omega
          · exact absurd (ho.add_even (by decide : Even 2)) hm⟩
        exact isGood_stabilizer_basePoint_of_four_le (m := k) (neg_one_ne_one_of_odd_card hqodd)

end Main

end CFSGOutside.HallPaige
