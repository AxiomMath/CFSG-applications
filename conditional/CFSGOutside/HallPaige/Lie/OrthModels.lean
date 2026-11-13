import CFSGOutside.HallPaige.Lie.OrthGood
import CFSGOutside.HallPaige.Cosets
import Mathlib.FieldTheory.Finite.Basic

/-!
# The corpus orthogonal models

The corpus quadratic forms `StatedQuadOdd n K` (`q` odd), `StatedQuadPlus n K` and
`StatedQuadMinus n K b c` (`t² + b t + c` irreducible) are quadratic forms with nondegenerate
polar form and a frame of `n` (resp. `n`, `n - 1`) hyperbolic pairs given by the coordinate
vectors. Hence `PΩ` of each satisfies the Wilcox criterion
(`CFSGOutside.HallPaige.Orth.hasCompleteMapping_POmegaOdd`, `_POmegaPlus`, `_POmegaMinus`).
-/

namespace CFSGOutside.HallPaige.Orth

open Matrix QuadraticMap Corpus.Lie

variable {K : Type} [Field K]

/-- The minimal-counterexample step for `PΩ(Q₀)`, `Q₀` a quadratic form with a frame. -/
theorem hasCompleteMapping_omega {ι : Type} [Fintype ι] [DecidableEq ι] [Finite K]
    {Q₀ : (ι → K) → K} (Q : QuadraticForm K (ι → K)) (hQ : ⇑Q = Q₀) {m : ℕ} (F : Frame Q m)
    (hm : 3 ≤ m) (hnd : ∀ y : ι → K, y ≠ 0 → ∃ w, polar Q y w ≠ 0)
    (hP : ProperSubgroupsAdmissible (StatedProj (StatedOmega Q₀))) :
    HasCompleteMapping (StatedProj (StatedOmega Q₀)) := by
  subst hQ
  exact hasCompleteMapping_of_wilcoxCriterion cosetStatement (wilcoxCriterion_omega F hm hnd) hP

/-- The product of two coordinates, as a quadratic form. -/
noncomputable abbrev coordMul {ι : Type} (k l : ι) : QuadraticForm K (ι → K) :=
  linMulLin (LinearMap.proj k) (LinearMap.proj l)

theorem sum_apply' {ι α : Type} (s : Finset α) (f : α → QuadraticForm K (ι → K)) (v : ι → K) :
    (∑ i ∈ s, f i) v = ∑ i ∈ s, f i v := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, QuadraticMap.add_apply, ih]

theorem polar_hyp_sum {ι : Type} {n : ℕ} (a b : Fin n → ι) (x y : ι → K) :
    ∑ i, (x (a i) + y (a i)) * (x (b i) + y (b i)) - ∑ i, x (a i) * x (b i) -
      ∑ i, y (a i) * y (b i) = ∑ i, (x (a i) * y (b i) + y (a i) * x (b i)) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### `Ω_{2n+1}` -/

section Odd

variable {n : ℕ}

/-- The quadratic form `StatedQuadOdd n K`. -/
noncomputable def oddQ (n : ℕ) (K : Type) [Field K] : QuadraticForm K (Fin n ⊕ Fin n ⊕ Unit → K) :=
  ∑ i, coordMul (.inl i) (.inr (.inl i)) + coordMul (.inr (.inr ())) (.inr (.inr ()))

theorem oddQ_apply (v : Fin n ⊕ Fin n ⊕ Unit → K) :
    oddQ n K v = ∑ i, v (.inl i) * v (.inr (.inl i)) + v (.inr (.inr ())) * v (.inr (.inr ())) := by
  rw [oddQ, QuadraticMap.add_apply, sum_apply']; rfl

theorem coe_oddQ : ⇑(oddQ n K) = StatedQuadOdd n K := funext fun v => by
  rw [oddQ_apply, StatedQuadOdd, _root_.sq]

theorem polar_oddQ (x y : Fin n ⊕ Fin n ⊕ Unit → K) :
    polar (oddQ n K) x y = ∑ i, (x (.inl i) * y (.inr (.inl i)) + y (.inl i) * x (.inr (.inl i))) +
      2 * (x (.inr (.inr ())) * y (.inr (.inr ()))) := by
  rw [polar, oddQ_apply, oddQ_apply, oddQ_apply]
  simp only [Pi.add_apply]
  rw [← polar_hyp_sum (fun i => Sum.inl i) (fun i => Sum.inr (Sum.inl i)) x y]
  ring

theorem polar_oddQ_e (x : Fin n ⊕ Fin n ⊕ Unit → K) (j : Fin n) :
    polar (oddQ n K) x (Pi.single (.inl j) 1) = x (.inr (.inl j)) := by
  simp [polar_oddQ, Pi.single_apply]

theorem polar_oddQ_f (x : Fin n ⊕ Fin n ⊕ Unit → K) (j : Fin n) :
    polar (oddQ n K) x (Pi.single (.inr (.inl j)) 1) = x (.inl j) := by
  simp [polar_oddQ, Pi.single_apply]

theorem polar_oddQ_z (x : Fin n ⊕ Fin n ⊕ Unit → K) :
    polar (oddQ n K) x (Pi.single (.inr (.inr ())) 1) = 2 * x (.inr (.inr ())) := by
  simp [polar_oddQ, Pi.single_apply]

/-- The coordinate frame of `StatedQuadOdd n K`. -/
noncomputable def oddFrame (n : ℕ) (K : Type) [Field K] : Frame (oddQ n K) n where
  e i := Pi.single (.inl i) 1
  f i := Pi.single (.inr (.inl i)) 1
  qe i := by simp [oddQ_apply, Pi.single_apply]
  qf i := by simp [oddQ_apply, Pi.single_apply]
  ee i j := by rw [polar_oddQ_e]; simp [Pi.single_apply]
  ff i j := by rw [polar_oddQ_f]; simp [Pi.single_apply]
  ef i j := by rw [polar_oddQ_f]; simp [Pi.single_apply, eq_comm]

theorem nondeg_oddQ (h2 : (2 : K) ≠ 0) (y : Fin n ⊕ Fin n ⊕ Unit → K) (hy : y ≠ 0) :
    ∃ w, polar (oddQ n K) y w ≠ 0 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hy
  rcases k with i | i | ⟨⟩
  · exact ⟨_, by rw [polar_oddQ_f]; exact hk⟩
  · exact ⟨_, by rw [polar_oddQ_e]; exact hk⟩
  · exact ⟨_, by rw [polar_oddQ_z]; exact mul_ne_zero h2 hk⟩

/-- **Hall–Paige for `PΩ_{2n+1}(q)`, `q` odd, `n ≥ 3`.** -/
theorem hasCompleteMapping_POmegaOdd [Finite K] (hn : 3 ≤ n) (h2 : (2 : K) ≠ 0)
    (hP : ProperSubgroupsAdmissible (StatedProj (StatedOmega (StatedQuadOdd n K)))) :
    HasCompleteMapping (StatedProj (StatedOmega (StatedQuadOdd n K))) :=
  hasCompleteMapping_omega (oddQ n K) coe_oddQ (oddFrame n K) hn (nondeg_oddQ h2) hP

end Odd

/-! ### `Ω⁺_{2n}` -/

section Plus

variable {n : ℕ}

/-- The quadratic form `StatedQuadPlus n K`. -/
noncomputable def plusQ (n : ℕ) (K : Type) [Field K] : QuadraticForm K (Fin n ⊕ Fin n → K) :=
  ∑ i, coordMul (.inl i) (.inr i)

theorem plusQ_apply (v : Fin n ⊕ Fin n → K) :
    plusQ n K v = ∑ i, v (.inl i) * v (.inr i) := by
  rw [plusQ, sum_apply']; rfl

theorem coe_plusQ : ⇑(plusQ n K) = StatedQuadPlus n K := funext fun v => by
  rw [plusQ_apply, StatedQuadPlus]

theorem polar_plusQ (x y : Fin n ⊕ Fin n → K) :
    polar (plusQ n K) x y = ∑ i, (x (.inl i) * y (.inr i) + y (.inl i) * x (.inr i)) := by
  rw [polar, plusQ_apply, plusQ_apply, plusQ_apply]
  simp only [Pi.add_apply]
  exact polar_hyp_sum (fun i => Sum.inl i) (fun i => Sum.inr i) x y

theorem polar_plusQ_e (x : Fin n ⊕ Fin n → K) (j : Fin n) :
    polar (plusQ n K) x (Pi.single (.inl j) 1) = x (.inr j) := by
  simp [polar_plusQ, Pi.single_apply]

theorem polar_plusQ_f (x : Fin n ⊕ Fin n → K) (j : Fin n) :
    polar (plusQ n K) x (Pi.single (.inr j) 1) = x (.inl j) := by
  simp [polar_plusQ, Pi.single_apply]

/-- The coordinate frame of `StatedQuadPlus n K`. -/
noncomputable def plusFrame (n : ℕ) (K : Type) [Field K] : Frame (plusQ n K) n where
  e i := Pi.single (.inl i) 1
  f i := Pi.single (.inr i) 1
  qe i := by simp [plusQ_apply, Pi.single_apply]
  qf i := by simp [plusQ_apply, Pi.single_apply]
  ee i j := by rw [polar_plusQ_e]; simp [Pi.single_apply]
  ff i j := by rw [polar_plusQ_f]; simp [Pi.single_apply]
  ef i j := by rw [polar_plusQ_f]; simp [Pi.single_apply, eq_comm]

theorem nondeg_plusQ (y : Fin n ⊕ Fin n → K) (hy : y ≠ 0) :
    ∃ w, polar (plusQ n K) y w ≠ 0 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hy
  rcases k with i | i
  · exact ⟨_, by rw [polar_plusQ_f]; exact hk⟩
  · exact ⟨_, by rw [polar_plusQ_e]; exact hk⟩

/-- **Hall–Paige for `PΩ⁺_{2n}(q)`, `n ≥ 3`.** -/
theorem hasCompleteMapping_POmegaPlus [Finite K] (hn : 3 ≤ n)
    (hP : ProperSubgroupsAdmissible (StatedProj (StatedOmega (StatedQuadPlus n K)))) :
    HasCompleteMapping (StatedProj (StatedOmega (StatedQuadPlus n K))) :=
  hasCompleteMapping_omega (plusQ n K) coe_plusQ (plusFrame n K) hn nondeg_plusQ hP

end Plus

/-! ### `Ω⁻_{2n}` -/

section Minus

variable {n : ℕ} {b c : K}

/-- The quadratic form `StatedQuadMinus n K b c`. -/
noncomputable def minusQ (n : ℕ) (K : Type) [Field K] (b c : K) : QuadraticForm K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :=
  ∑ i, coordMul (.inl i) (.inr (.inl i)) + coordMul (.inr (.inr 0)) (.inr (.inr 0)) +
    b • coordMul (.inr (.inr 0)) (.inr (.inr 1)) + c • coordMul (.inr (.inr 1)) (.inr (.inr 1))

theorem minusQ_apply (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    minusQ n K b c v = ∑ i, v (.inl i) * v (.inr (.inl i)) +
      v (.inr (.inr 0)) * v (.inr (.inr 0)) + b * (v (.inr (.inr 0)) * v (.inr (.inr 1))) +
      c * (v (.inr (.inr 1)) * v (.inr (.inr 1))) := by
  rw [minusQ, QuadraticMap.add_apply, QuadraticMap.add_apply, QuadraticMap.add_apply,
    sum_apply', QuadraticMap.smul_apply, QuadraticMap.smul_apply]
  rfl

theorem coe_minusQ : ⇑(minusQ n K b c) = StatedQuadMinus n K b c := funext fun v => by
  rw [minusQ_apply, StatedQuadMinus]; ring

theorem polar_minusQ (x y : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    polar (minusQ n K b c) x y =
      ∑ i, (x (.inl i) * y (.inr (.inl i)) + y (.inl i) * x (.inr (.inl i))) +
      2 * (x (.inr (.inr 0)) * y (.inr (.inr 0))) +
      b * (x (.inr (.inr 0)) * y (.inr (.inr 1)) + y (.inr (.inr 0)) * x (.inr (.inr 1))) +
      2 * c * (x (.inr (.inr 1)) * y (.inr (.inr 1))) := by
  rw [polar, minusQ_apply, minusQ_apply, minusQ_apply]
  simp only [Pi.add_apply]
  rw [← polar_hyp_sum (fun i => Sum.inl i) (fun i => Sum.inr (Sum.inl i)) x y]
  ring

theorem polar_minusQ_e (x : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) (j : Fin (n - 1)) :
    polar (minusQ n K b c) x (Pi.single (.inl j) 1) = x (.inr (.inl j)) := by
  simp [polar_minusQ, Pi.single_apply]

theorem polar_minusQ_f (x : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) (j : Fin (n - 1)) :
    polar (minusQ n K b c) x (Pi.single (.inr (.inl j)) 1) = x (.inl j) := by
  simp [polar_minusQ, Pi.single_apply]

theorem polar_minusQ_z0 (x : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    polar (minusQ n K b c) x (Pi.single (.inr (.inr 0)) 1) =
      2 * x (.inr (.inr 0)) + b * x (.inr (.inr 1)) := by
  simp [polar_minusQ, Pi.single_apply]

theorem polar_minusQ_z1 (x : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    polar (minusQ n K b c) x (Pi.single (.inr (.inr 1)) 1) =
      b * x (.inr (.inr 0)) + 2 * c * x (.inr (.inr 1)) := by
  simp [polar_minusQ, Pi.single_apply]

/-- The coordinate frame of `StatedQuadMinus n K b c`. -/
noncomputable def minusFrame (n : ℕ) (K : Type) [Field K] (b c : K) : Frame (minusQ n K b c) (n - 1) where
  e i := Pi.single (.inl i) 1
  f i := Pi.single (.inr (.inl i)) 1
  qe i := by simp [minusQ_apply, Pi.single_apply]
  qf i := by simp [minusQ_apply, Pi.single_apply]
  ee i j := by rw [polar_minusQ_e]; simp [Pi.single_apply]
  ff i j := by rw [polar_minusQ_f]; simp [Pi.single_apply]
  ef i j := by rw [polar_minusQ_f]; simp [Pi.single_apply, eq_comm]

/-- In a finite field, `t² + b t + c` with `2 = 0` and `b = 0` has a root. -/
theorem exists_root_of_two_eq_zero [Finite K] (h2 : (2 : K) = 0) (c : K) :
    ∃ t : K, t ^ 2 + 0 * t + c = 0 := by
  have hchar : ringChar K = 2 := by
    have hd : ringChar K ∣ 2 := (ringChar.spec K 2).1 (by exact_mod_cast h2)
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact absurd h CharP.ringChar_ne_one
    · exact h
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two hchar c
  refine ⟨s, ?_⟩
  rw [hs, zero_mul, add_zero, _root_.sq, ← two_mul, h2, zero_mul]

theorem nondeg_minusQ [Finite K] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (y : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) (hy : y ≠ 0) :
    ∃ w, polar (minusQ n K b c) y w ≠ 0 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hy
  rcases k with i | i | k
  · exact ⟨_, by rw [polar_minusQ_f]; exact hk⟩
  · exact ⟨_, by rw [polar_minusQ_e]; exact hk⟩
  by_contra hall
  push Not at hall
  have e0 := hall (Pi.single (.inr (.inr 0)) 1)
  have e1 := hall (Pi.single (.inr (.inr 1)) 1)
  rw [polar_minusQ_z0] at e0
  rw [polar_minusQ_z1] at e1
  set y0 := y (.inr (.inr 0))
  set y1 := y (.inr (.inr 1))
  have hb : (2 : K) = 0 → b = 0 → False := fun h2 hb0 => by
    obtain ⟨t, ht⟩ := exists_root_of_two_eq_zero h2 c
    exact hirr t (by rw [hb0]; exact ht)
  have hy01 : y0 ≠ 0 ∨ y1 ≠ 0 := by
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr hk
  by_cases hy1 : y1 = 0
  · have hy0 : y0 ≠ 0 := hy01.resolve_right (not_not.2 hy1)
    rw [hy1, mul_zero, add_zero] at e0
    rw [hy1, mul_zero, add_zero] at e1
    exact hb ((mul_eq_zero.1 e0).resolve_right hy0) ((mul_eq_zero.1 e1).resolve_right hy0)
  · by_cases h2 : (2 : K) = 0
    · rw [h2, zero_mul, zero_add] at e0
      exact hb h2 ((mul_eq_zero.1 e0).resolve_right hy1)
    · apply hirr (y0 / y1)
      have key : 2 * (y0 ^ 2 + b * y0 * y1 + c * y1 ^ 2) = 0 := by
        linear_combination y0 * e0 + y1 * e1
      have key' : y0 ^ 2 + b * y0 * y1 + c * y1 ^ 2 = 0 :=
        (mul_eq_zero.1 key).resolve_left h2
      field_simp
      linear_combination key'

/-- **Hall–Paige for `PΩ⁻_{2n}(q)`, `n ≥ 4`.** -/
theorem hasCompleteMapping_POmegaMinus [Finite K] (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hP : ProperSubgroupsAdmissible (StatedProj (StatedOmega (StatedQuadMinus n K b c)))) :
    HasCompleteMapping (StatedProj (StatedOmega (StatedQuadMinus n K b c))) :=
  hasCompleteMapping_omega (minusQ n K b c) coe_minusQ (minusFrame n K b c) (by omega)
    (nondeg_minusQ hirr) hP

end Minus

end CFSGOutside.HallPaige.Orth
