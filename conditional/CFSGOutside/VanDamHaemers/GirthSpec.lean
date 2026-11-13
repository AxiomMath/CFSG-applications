import CFSGOutside.VanDamHaemers.Girth

/-!
# Girth `≥ 12` from the spectrum
-/

namespace CFSGOutside.VanDamHaemers

open Matrix Finset SimpleGraph

/-- The polynomials with `F r = p_r(A)` for a cubic graph. -/
noncomputable def pp : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, t => t
  | r + 2, t => t * pp (r + 1) t - (if r = 0 then 3 else 2) * pp r t

/-- Coefficients of `p_r(t) = a + b t` when `t² = c`. -/
def ab (c : ℤ) : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | 1 => (0, 1)
  | r + 2 => (c * (ab c (r + 1)).2 - (if r = 0 then 3 else 2) * (ab c r).1,
      (ab c (r + 1)).1 - (if r = 0 then 3 else 2) * (ab c r).2)

lemma pp_eq {t : ℝ} {c : ℤ} (ht : t ^ 2 = c) :
    ∀ r, pp r t = (ab c r).1 + (ab c r).2 * t
  | 0 => by simp [pp, ab]
  | 1 => by simp [pp, ab]
  | r + 2 => by
    rw [pp, pp_eq ht (r + 1), pp_eq ht r]
    simp only [ab]
    split_ifs <;> push_cast <;> linear_combination ((ab c (r + 1)).2 : ℝ) * ht

lemma trace_values : ∀ r < 12, 1 ≤ r →
    2 * (ab 9 r).1 + 28 * (ab 0 r).1 + 42 * (ab 6 r).1 + 54 * (ab 2 r).1 = 0 := by
  decide

lemma sum_pp (r : ℕ) : (tutteSpectrum.map (pp r)).sum =
    2 * (ab 9 r).1 + 28 * (ab 0 r).1 + 42 * (ab 6 r).1 + 54 * (ab 2 r).1 := by
  rw [sum_tutteSpectrum]
  rw [pp_eq (c := 9) (by norm_num) r, pp_eq (c := 9) (by norm_num) r, pp_eq (c := 0) (by norm_num) r,
    pp_eq (c := 6) (by push_cast; exact sq_sqrt6) r, pp_eq (c := 6) (by push_cast; rw [neg_sq]; exact sq_sqrt6) r,
    pp_eq (c := 2) (by push_cast; exact sq_sqrt2) r, pp_eq (c := 2) (by push_cast; rw [neg_sq]; exact sq_sqrt2) r]
  push_cast
  ring

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The matrix of non-backtracking walk counts. -/
noncomputable def F (r : ℕ) : Matrix V V ℝ := fun u v => ((nbWalks G r u v).card : ℝ)

lemma nbWalks_eq_of_le {r : ℕ} (hr : r ≤ 1) (u v : V) :
    nbWalks G r u v = G.finsetWalkLength r u v := by
  classical
  ext p
  rw [mem_nbWalks, SimpleGraph.mem_finsetWalkLength_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, isNB_of_length_le G p (by omega)⟩⟩

lemma F_le (r : ℕ) (hr : r ≤ 1) : F G r = G.adjMatrix ℝ ^ r := by
  ext u v
  rw [F, nbWalks_eq_of_le G hr, SimpleGraph.adjMatrix_pow_apply_eq_card_walk,
    ← SimpleGraph.card_set_walk_length_eq]

lemma F_succ_succ (hdeg : ∀ v, G.degree v = 3) (r : ℕ) :
    F G (r + 2) = G.adjMatrix ℝ * F G (r + 1) - ((if r = 0 then 3 else 2 : ℕ) : ℝ) • F G r := by
  ext u v
  rw [Matrix.sub_apply, Matrix.smul_apply, SimpleGraph.adjMatrix_mul_apply]
  have h := nb_recursion G hdeg r u v
  have h' : (∑ w ∈ G.neighborFinset u, ((nbWalks G (r + 1) w v).card : ℝ)) =
      ((nbWalks G (r + 2) u v).card : ℝ) +
        ((if r = 0 then 3 else 2 : ℕ) : ℝ) * ((nbWalks G r u v).card : ℝ) := by
    exact_mod_cast h
  simp only [F, smul_eq_mul]
  rw [h']
  ring

variable (hspec : (G.adjMatrix ℝ).charpoly = spectrumPoly)
include hspec

lemma F_eq (hdeg : ∀ v, G.degree v = 3) :
    ∀ r, F G r = U G * diagonal (fun i => pp r (eig G i)) * star (U G)
  | 0 => by
    rw [F_le G 0 (by norm_num), pow_zero]
    simp only [pp]
    exact (conj_one G).symm
  | 1 => by
    rw [F_le G 1 (by norm_num), pow_one, adj_eq]
    rfl
  | r + 2 => by
    rw [F_succ_succ G hdeg, F_eq hdeg (r + 1), F_eq hdeg r, adj_eq, conj_mul, conj_smul, conj_sub]
    refine congrArg (fun d => U G * diagonal d * star (U G)) (funext fun i => ?_)
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    rw [pp]
    split_ifs <;> push_cast <;> ring

lemma trace_F (hdeg : ∀ v, G.degree v = 3) (r : ℕ) :
    (F G r).trace = 2 * (ab 9 r).1 + 28 * (ab 0 r).1 + 42 * (ab 6 r).1 + 54 * (ab 2 r).1 := by
  rw [F_eq G hspec hdeg, trace_conj, sum_eig G hspec (pp r), sum_pp]

omit hspec in
lemma isNB_of_isCycle {v : V} {c : G.Walk v v} (hc : c.IsCycle) : IsNB G c := by
  intro i hi heq
  have h3 := hc.three_le_length
  have hnd := hc.support_nodup
  -- `support.tail[j] = getVert (j + 1)`
  have hlen : c.support.tail.length = c.length := by simp [Walk.length_support]
  have hget : ∀ j (hj : j < c.support.tail.length), c.support.tail[j] = c.getVert (j + 1) := by
    intro j hj
    rw [List.getElem_tail, Walk.support_getElem_eq_getVert]
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · -- `getVert 0 = getVert c.length`
    have e : c.getVert 0 = c.getVert c.length := by rw [Walk.getVert_zero, Walk.getVert_length]
    rw [e] at heq
    have := (hnd.getElem_inj_iff (i := 1) (j := c.length - 1) (hi := by omega)
      (hj := by omega)).1
      (by rw [hget, hget, show c.length - 1 + 1 = c.length by omega]; exact heq.symm)
    omega
  · have := (hnd.getElem_inj_iff (i := i - 1) (j := i + 1) (hi := by omega)
      (hj := by omega)).1
      (by rw [hget, hget, show i - 1 + 1 = i by omega]; exact heq)
    omega

/-- A graph with the spectrum of the Tutte 12-cage has girth at least `12`. -/
theorem cycle_length_ge (hdeg : ∀ v, G.degree v = 3) (v : V) (c : G.Walk v v)
    (hc : c.IsCycle) : 12 ≤ c.length := by
  by_contra hlt
  push Not at hlt
  set g := c.length with hg
  have h3 := hc.three_le_length
  have htr := trace_F G hspec hdeg g
  have h0 := trace_values g hlt (by omega)
  have h0' : (F G g).trace = 0 := by rw [htr]; exact_mod_cast h0
  rw [Matrix.trace] at h0'
  have hnn : ∀ w ∈ univ, 0 ≤ (F G g).diag w := fun w _ => Nat.cast_nonneg _
  have hv := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0' v (mem_univ v)
  simp only [Matrix.diag, F, Nat.cast_eq_zero, card_eq_zero] at hv
  have hmem : c ∈ nbWalks G g v v := (mem_nbWalks G).2 ⟨rfl, isNB_of_isCycle G hc⟩
  rw [hv] at hmem
  exact absurd hmem (Finset.notMem_empty _)

end CFSGOutside.VanDamHaemers
