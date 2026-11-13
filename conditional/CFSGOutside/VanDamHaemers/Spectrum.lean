import CFSGOutside.VanDamHaemers.Defs

/-!
# The spectrum of the Tutte 12-cage and the spectral decomposition of an adjacency matrix
-/

namespace CFSGOutside.VanDamHaemers

open Matrix Polynomial Finset

lemma card_tutteSpectrum : Multiset.card tutteSpectrum = 126 := by
  simp [tutteSpectrum]

lemma sum_tutteSpectrum (f : ℝ → ℝ) :
    (tutteSpectrum.map f).sum = f 3 + f (-3) + 28 * f 0 + 21 * f (Real.sqrt 6) +
      21 * f (-Real.sqrt 6) + 27 * f (Real.sqrt 2) + 27 * f (-Real.sqrt 2) := by
  simp [tutteSpectrum, Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
    Multiset.sum_replicate]
  ring

lemma mem_tutteSpectrum {m : ℝ} (hm : m ∈ tutteSpectrum) :
    m = 3 ∨ m = -3 ∨ m = 0 ∨ m ^ 2 = 6 ∨ m ^ 2 = 2 := by
  simp only [tutteSpectrum, Multiset.mem_add, Multiset.insert_eq_cons, Multiset.mem_cons,
    Multiset.mem_singleton, Multiset.mem_replicate] at hm
  rcases hm with ((((((h | h) | ⟨-, h⟩) | ⟨-, h⟩) | ⟨-, h⟩) | ⟨-, h⟩) | ⟨-, h⟩) <;> subst h <;>
    simp

section Graph

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma adj_isHermitian : (G.adjMatrix ℝ).IsHermitian :=
  isHermitian_iff_isSelfAdjoint.mpr (G.isSymm_adjMatrix)

/-- The orthogonal matrix of eigenvectors. -/
noncomputable abbrev U : Matrix V V ℝ := ((adj_isHermitian G).eigenvectorUnitary : Matrix V V ℝ)

/-- The eigenvalues. -/
noncomputable abbrev eig : V → ℝ := (adj_isHermitian G).eigenvalues

lemma U_star_mul : star (U G) * U G = 1 :=
  Matrix.mem_unitaryGroup_iff'.1 (adj_isHermitian G).eigenvectorUnitary.2

lemma U_mul_star : U G * star (U G) = 1 :=
  Matrix.mem_unitaryGroup_iff.1 (adj_isHermitian G).eigenvectorUnitary.2

lemma adj_eq : G.adjMatrix ℝ = U G * diagonal (eig G) * star (U G) := by
  have := (adj_isHermitian G).spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at this
  simpa using this

lemma conj_mul (d e : V → ℝ) :
    (U G * diagonal d * star (U G)) * (U G * diagonal e * star (U G)) =
      U G * diagonal (d * e) * star (U G) := by
  calc (U G * diagonal d * star (U G)) * (U G * diagonal e * star (U G))
      = U G * diagonal d * (star (U G) * U G) * diagonal e * star (U G) := by
        simp only [Matrix.mul_assoc]
    _ = U G * diagonal (d * e) * star (U G) := by
        rw [U_star_mul, Matrix.mul_one, Matrix.mul_assoc (U G), diagonal_mul_diagonal]; rfl

lemma conj_add (d e : V → ℝ) :
    U G * diagonal d * star (U G) + U G * diagonal e * star (U G) =
      U G * diagonal (d + e) * star (U G) := by
  rw [← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]; rfl

lemma conj_smul (c : ℝ) (d : V → ℝ) :
    c • (U G * diagonal d * star (U G)) = U G * diagonal (c • d) * star (U G) := by
  rw [diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]

lemma conj_one : U G * diagonal (1 : V → ℝ) * star (U G) = 1 := by
  show U G * diagonal (fun _ => (1 : ℝ)) * star (U G) = 1
  rw [diagonal_one, Matrix.mul_one, U_mul_star]

lemma trace_conj (d : V → ℝ) : (U G * diagonal d * star (U G)).trace = ∑ i, d i := by
  rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, U_star_mul, Matrix.mul_one, trace_diagonal]

lemma adj_pow_eq (k : ℕ) : G.adjMatrix ℝ ^ k = U G * diagonal (eig G ^ k) * star (U G) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, conj_one]
  | succ k ih => rw [pow_succ, ih, adj_eq, conj_mul, pow_succ]

/-- The quadratic form of a conjugated diagonal matrix. -/
lemma dot_conj (d x : V → ℝ) :
    x ⬝ᵥ ((U G * diagonal d * star (U G)) *ᵥ x) = ∑ i, d i * (star (U G) *ᵥ x) i ^ 2 := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have : x ᵥ* U G = star (U G) *ᵥ x := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, mulVec_transpose]
  rw [this, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_diagonal]
  ring

variable (hspec : (G.adjMatrix ℝ).charpoly = spectrumPoly)
include hspec

lemma eig_multiset : Finset.univ.val.map (eig G) = tutteSpectrum := by
  have := (adj_isHermitian G).roots_charpoly_eq_eigenvalues
  rw [hspec, spectrumPoly, roots_multiset_prod_X_sub_C] at this
  rw [this]
  simp

lemma sum_eig (f : ℝ → ℝ) : ∑ i, f (eig G i) = (tutteSpectrum.map f).sum := by
  rw [← eig_multiset G hspec, Multiset.map_map]
  rfl

lemma card_eq : Fintype.card V = 126 := by
  have := congrArg Multiset.card (eig_multiset G hspec)
  rw [Multiset.card_map, card_tutteSpectrum] at this
  exact this

lemma eig_mem (i : V) : eig G i ∈ tutteSpectrum := by
  rw [← eig_multiset G hspec]
  exact Multiset.mem_map_of_mem _ (Finset.mem_univ i)

end Graph

end CFSGOutside.VanDamHaemers
