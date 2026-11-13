import CFSGOutside.VanDamHaemers.Spectrum

/-!
# Combinatorial consequences of the spectrum: cubic, bipartite, connected
-/

namespace CFSGOutside.VanDamHaemers

open Matrix Finset

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma conj_sub (d e : V → ℝ) :
    U G * diagonal d * star (U G) - U G * diagonal e * star (U G) =
      U G * diagonal (d - e) * star (U G) := by
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]; rfl

lemma sq_sqrt6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
lemma sq_sqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

variable (hspec : (G.adjMatrix ℝ).charpoly = spectrumPoly)
include hspec

lemma trace_adj_pow (k : ℕ) : (G.adjMatrix ℝ ^ k).trace = (tutteSpectrum.map (· ^ k)).sum := by
  rw [adj_pow_eq, trace_conj, ← sum_eig G hspec]
  rfl

lemma sum_degree : ∑ v, (G.degree v : ℝ) = 378 := by
  have h := trace_adj_pow G hspec 2
  rw [sum_tutteSpectrum] at h
  have h' : (G.adjMatrix ℝ ^ 2).trace = ∑ v, (G.degree v : ℝ) := by
    rw [sq, Matrix.trace]
    simp only [Matrix.diag, SimpleGraph.adjMatrix_mul_self_apply_self]
  rw [h'] at h
  rw [h]
  simp only [neg_sq, sq_sqrt6, sq_sqrt2]
  norm_num

lemma sum_degree_sq_le : ∑ v, (G.degree v : ℝ) ^ 2 ≤ 9 * 126 := by
  set A := G.adjMatrix ℝ
  set x : V → ℝ := fun _ => 1
  have hAx : A *ᵥ x = fun v => (G.degree v : ℝ) := by
    funext v; simp [A, x, SimpleGraph.adjMatrix_mulVec_const_apply]
  have hsymm : A.transpose = A := G.isSymm_adjMatrix
  have h1 : ∑ v, (G.degree v : ℝ) ^ 2 = x ⬝ᵥ ((A ^ 2) *ᵥ x) := by
    rw [sq, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm,
      hAx, dotProduct]
    simp [sq]
  rw [h1, adj_pow_eq, dot_conj]
  have hy : ∑ i, (star (U G) *ᵥ x) i ^ 2 = 126 := by
    have := dot_conj G 1 x
    rw [conj_one] at this
    simp only [Pi.one_apply, one_mul, Matrix.one_mulVec] at this
    rw [← this]
    simp [x, dotProduct, card_eq G hspec]
  rw [← hy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hb : eig G i ^ 2 ≤ 9 := by
    rcases mem_tutteSpectrum (eig_mem G hspec i) with h | h | h | h | h <;> rw [h] <;> norm_num
  simp only [Pi.pow_apply]
  exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)

/-- A graph with the spectrum of the Tutte 12-cage is cubic. -/
theorem degree_eq_three (v : V) : G.degree v = 3 := by
  have h1 := sum_degree G hspec
  have h2 := sum_degree_sq_le G hspec
  have h3 : ∑ w, ((G.degree w : ℝ) - 3) ^ 2 = 0 := by
    have e : ∀ w, ((G.degree w : ℝ) - 3) ^ 2 = (G.degree w : ℝ) ^ 2 - 6 * (G.degree w : ℝ) + 9 :=
      fun w => by ring
    have : ∑ w, ((G.degree w : ℝ) - 3) ^ 2 =
        ∑ w, (G.degree w : ℝ) ^ 2 - 6 * ∑ w, (G.degree w : ℝ) + (Fintype.card V : ℝ) * 9 := by
      simp_rw [e]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    have hc : (Fintype.card V : ℝ) = 126 := by exact_mod_cast card_eq G hspec
    rw [this, h1, hc]
    have h0 : 0 ≤ ∑ w, ((G.degree w : ℝ) - 3) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).1 h3 v (mem_univ v)
  have h4 := (pow_eq_zero_iff two_ne_zero).1 this
  have : (G.degree v : ℝ) = 3 := by linarith
  exact_mod_cast this

/-- A graph with the spectrum of the Tutte 12-cage is bipartite. -/
theorem nonempty_coloring : Nonempty (G.Coloring Bool) := by
  have hcol : G.Colorable 2 := by
    rw [SimpleGraph.two_colorable_iff_forall_loop_even]
    intro u w
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    set k := w.length
    have htr := trace_adj_pow G hspec k
    rw [sum_tutteSpectrum, hodd.neg_pow, hodd.neg_pow, hodd.neg_pow,
      zero_pow (Nat.pos_of_ne_zero (by rintro h; rw [h] at hodd; exact absurd hodd (by decide))).ne'] at htr
    have h0 : (G.adjMatrix ℝ ^ k).trace = 0 := by rw [htr]; ring
    rw [trace] at h0
    have hnn : ∀ v ∈ univ, 0 ≤ (G.adjMatrix ℝ ^ k).diag v := by
      intro v _
      rw [Matrix.diag, SimpleGraph.adjMatrix_pow_apply_eq_card_walk]
      positivity
    have hu := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 u (mem_univ u)
    rw [Matrix.diag, SimpleGraph.adjMatrix_pow_apply_eq_card_walk] at hu
    have : 0 < Fintype.card {p : G.Walk u u | p.length = k} :=
      Fintype.card_pos_iff.2 ⟨⟨w, rfl⟩⟩
    have : (0 : ℝ) < Fintype.card {p : G.Walk u u | p.length = k} := by exact_mod_cast this
    linarith
  obtain ⟨c⟩ := hcol
  exact ⟨SimpleGraph.Coloring.mk (fun v => finTwoEquiv (c v))
    (fun h he => c.valid h (finTwoEquiv.injective he))⟩

open Classical in
/-- A graph with the spectrum of the Tutte 12-cage is connected. -/
theorem connected : G.Connected := by
  -- the unique index with eigenvalue `3`
  have hcount : (univ.filter fun i => eig G i = 3).card = 1 := by
    have h := sum_eig G hspec (fun x => if x = 3 then (1 : ℝ) else 0)
    have h6 : Real.sqrt 6 ≠ 3 := by intro h; have := sq_sqrt6; rw [h] at this; norm_num at this
    have h6' : -Real.sqrt 6 ≠ 3 := by have := Real.sqrt_nonneg 6; intro h; linarith
    have h2 : Real.sqrt 2 ≠ 3 := by intro h; have := sq_sqrt2; rw [h] at this; norm_num at this
    have h2' : -Real.sqrt 2 ≠ 3 := by have := Real.sqrt_nonneg 2; intro h; linarith
    rw [sum_tutteSpectrum] at h
    simp only [h6, h6', h2, h2', if_true, if_false, show (-3 : ℝ) ≠ 3 by norm_num,
      show (0 : ℝ) ≠ 3 by norm_num] at h
    norm_num at h
    exact_mod_cast h
  obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.1 hcount
  have hi : ∀ i, eig G i = 3 → i = i₀ := by
    intro i hi
    have : i ∈ univ.filter fun i => eig G i = 3 := by simp [hi]
    rw [hi₀] at this
    exact Finset.mem_singleton.1 this
  -- eigenvectors of `3` are multiples of the `i₀`-th column of `U`
  have key : ∀ x : V → ℝ, G.adjMatrix ℝ *ᵥ x = (3 : ℝ) • x → ∀ v, x v = U G v i₀ * (star (U G) *ᵥ x) i₀ := by
    intro x hx
    set y := star (U G) *ᵥ x
    have h3 : (3 : ℝ) • (1 : Matrix V V ℝ) = U G * diagonal ((3 : ℝ) • (1 : V → ℝ)) * star (U G) := by
      rw [← conj_smul, conj_one]
    have hB : (G.adjMatrix ℝ) - (3 : ℝ) • (1 : Matrix V V ℝ) = U G * diagonal (eig G - (3 : ℝ) • (1 : V → ℝ)) * star (U G) := by
      rw [h3, adj_eq, conj_sub]
    have hsq : ((G.adjMatrix ℝ) - (3 : ℝ) • (1 : Matrix V V ℝ)) * ((G.adjMatrix ℝ) - (3 : ℝ) • (1 : Matrix V V ℝ)) =
        U G * diagonal ((eig G - (3 : ℝ) • (1 : V → ℝ)) * (eig G - (3 : ℝ) • (1 : V → ℝ))) * star (U G) := by
      rw [hB, conj_mul]
    have hz : ((G.adjMatrix ℝ) - (3 : ℝ) • (1 : Matrix V V ℝ)) *ᵥ x = 0 := by
      simp [Matrix.sub_mulVec, hx, Matrix.smul_mulVec]
    have hq : x ⬝ᵥ ((((G.adjMatrix ℝ) - (3 : ℝ) • (1 : Matrix V V ℝ)) * ((G.adjMatrix ℝ) - (3 : ℝ) • (1 : Matrix V V ℝ))) *ᵥ x) = 0 := by
      rw [← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero, dotProduct_zero]
    rw [hsq, dot_conj] at hq
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by
      simp only [Pi.mul_apply]; exact mul_nonneg (mul_self_nonneg _) (sq_nonneg _))).1 hq
    have hy0 : ∀ i, i ≠ i₀ → y i = 0 := by
      intro i hne
      have h := hterm i (mem_univ i)
      have h3 : eig G i - 3 ≠ 0 := fun h' => hne (hi i (by linarith))
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul,
        mul_one] at h
      have : (eig G i - 3) * (eig G i - 3) ≠ 0 := mul_ne_zero h3 h3
      exact (pow_eq_zero_iff two_ne_zero).1 ((mul_eq_zero.1 h).resolve_left this)
    have hxU : x = U G *ᵥ y := by
      rw [Matrix.mulVec_mulVec, U_mul_star, Matrix.one_mulVec]
    intro v
    rw [hxU, mulVec, dotProduct, Finset.sum_eq_single i₀]
    · intro i _ hne; rw [hy0 i hne, mul_zero]
    · simp
  -- the all-ones vector
  have hdeg := degree_eq_three G hspec
  have h1 : (G.adjMatrix ℝ) *ᵥ (fun _ => (1 : ℝ)) = (3 : ℝ) • (fun _ => (1 : ℝ)) := by
    funext v; simp [SimpleGraph.adjMatrix_mulVec_const_apply, hdeg]
  have hc1 := key _ h1
  have hne : Nonempty V := by
    rw [← Fintype.card_pos_iff, card_eq G hspec]; norm_num
  obtain ⟨v₀⟩ := hne
  -- the indicator of the component of `v₀`
  let x : V → ℝ := fun w => if G.Reachable v₀ w then 1 else 0
  have hx : (G.adjMatrix ℝ) *ᵥ x = (3 : ℝ) • x := by
    funext w
    rw [SimpleGraph.adjMatrix_mulVec_apply]
    by_cases hw : G.Reachable v₀ w
    · have : ∀ u ∈ G.neighborFinset w, x u = 1 := by
        intro u hu
        rw [SimpleGraph.mem_neighborFinset] at hu
        simp [x, hw.trans hu.reachable]
      rw [Finset.sum_congr rfl this]
      simp [x, hw, hdeg]
    · have : ∀ u ∈ G.neighborFinset w, x u = 0 := by
        intro u hu
        rw [SimpleGraph.mem_neighborFinset] at hu
        have : ¬ G.Reachable v₀ u := fun h => hw (h.trans hu.symm.reachable)
        simp [x, this]
      rw [Finset.sum_congr rfl this]
      simp [x, hw]
  have hcx := key x hx
  haveI : Nonempty V := ⟨v₀⟩
  refine ⟨fun a b => ?_⟩
  suffices hall : ∀ w, G.Reachable v₀ w from (hall a).symm.trans (hall b)
  intro w
  by_contra hw
  have e0 : x w = 0 := by simp [x, hw]
  have e1 : x v₀ = 1 := by simp [x]
  have f0 := hcx w
  have f1 := hcx v₀
  have g0 := hc1 w
  have g1 := hc1 v₀
  -- `U · i₀` is constant and nonzero
  have hUw : U G w i₀ ≠ 0 := by intro h; rw [h, zero_mul] at g0; norm_num at g0
  have hUv : U G v₀ i₀ ≠ 0 := by intro h; rw [h, zero_mul] at g1; norm_num at g1
  rw [e0] at f0
  rw [e1] at f1
  have hy : (star (U G) *ᵥ x) i₀ = 0 := (mul_eq_zero.1 f0.symm).resolve_left hUw
  rw [hy, mul_zero] at f1
  norm_num at f1

end CFSGOutside.VanDamHaemers
