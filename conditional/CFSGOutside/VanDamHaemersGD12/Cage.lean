import CFSGOutside.VanDamHaemersGD12.Traces
import CFSGOutside.VanDamHaemers.Facts

/-!
# The Tutte 12-cage as a graph, and its adjacency matrix

`cage` is the LCF graph of `Defs.lean` on `Fin 126`. The entries of the powers of its adjacency matrix are
the walk counts `walks`, so the kernel computations of `Compute.lean` and `Traces.lean` give
`A^7 + 84 A^3 = 17 A^5 + 108 A` and the traces of `A^0, …, A^6`.
-/

namespace CFSGOutside.VanDamHaemersGD12

open Matrix Finset

/-- The neighbours as elements of `Fin 126`. -/
def nxtF (i : Fin 126) : Fin 126 := ⟨nxt i, lt_nxt _⟩
/-- The previous vertex as an element of `Fin 126`. -/
def prvF (i : Fin 126) : Fin 126 := ⟨prv i, lt_prv _⟩
/-- The chord as an element of `Fin 126`. -/
def chordF (i : Fin 126) : Fin 126 := ⟨chord i, lt_chord _⟩

lemma neighborFinset_eq (i : Fin 126) : cage.neighborFinset i = {nxtF i, prvF i, chordF i} := by
  ext j
  simp only [SimpleGraph.mem_neighborFinset, mem_insert, mem_singleton, Fin.ext_iff, nxtF, prvF, chordF,
    cage_adj, cageRel]

lemma adjMatrix_pow_apply (k : ℕ) (i v : Fin 126) :
    (cage.adjMatrix ℝ ^ k) i v = (walks k v i : ℝ) := by
  induction k generalizing i with
  | zero =>
    simp only [pow_zero, one_apply, walks, Fin.ext_iff]
    split_ifs <;> simp
  | succ k ih =>
    obtain ⟨-, -, -, h1, h2, h3⟩ := distinct i
    rw [pow_succ', SimpleGraph.adjMatrix_mul_apply, neighborFinset_eq,
      sum_insert (by simp [Fin.ext_iff, nxtF, prvF, chordF, h1, h2]),
      sum_insert (by simp [Fin.ext_iff, prvF, chordF, h3]), sum_singleton, ih, ih, ih, walks]
    simp only [nxtF, prvF, chordF]
    push_cast
    ring

/-- `A^7 + 84 A^3 = 17 A^5 + 108 A`: the minimal polynomial `x (x² - 9) (x² - 6) (x² - 2)` kills `A`. -/
theorem minpoly_eq : cage.adjMatrix ℝ ^ 7 + (84 : ℝ) • cage.adjMatrix ℝ ^ 3 =
    (17 : ℝ) • cage.adjMatrix ℝ ^ 5 + (108 : ℝ) • cage.adjMatrix ℝ ^ 1 := by
  ext i v
  have h := List.all_eq_true.1 colOK_all v (List.mem_range.2 v.2)
  rw [colOK_eq, List.all_eq_true] at h
  have h' := h i (List.mem_range.2 i.2)
  rw [beq_iff_eq, col_get _ _ _ i.2, col_get _ _ _ i.2, col_get _ _ _ i.2, col_get _ _ _ i.2] at h'
  simp only [Matrix.add_apply, Matrix.smul_apply, adjMatrix_pow_apply, smul_eq_mul]
  exact_mod_cast h'

lemma trace_eq_traceW (k : ℕ) : (cage.adjMatrix ℝ ^ k).trace = (traceW k : ℝ) := by
  have hl : (List.range 126).map (fun v => (col v k).get v) = (List.range 126).map (fun v => walks k v v) :=
    List.map_congr_left fun v hv => col_get v k v (List.mem_range.1 hv)
  rw [Matrix.trace, traceW, hl, Nat.cast_list_sum, List.map_map]
  simp only [Matrix.diag, adjMatrix_pow_apply]
  rw [Fin.sum_univ_eq_sum_range (fun v => (walks k v v : ℝ)) 126]
  simp only [Finset.sum, Finset.range_val, Multiset.range, Multiset.map_coe, Multiset.sum_coe]
  rfl

end CFSGOutside.VanDamHaemersGD12
