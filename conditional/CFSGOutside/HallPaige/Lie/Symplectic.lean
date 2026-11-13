import CFSGOutside.HallPaige.Lie.Polar
import CFSGOutside.HallPaige.Lie.Good
import CFSGOutside.Corpus.HallPaige.LieSymplectic
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Data.Matrix.Block

/-!
# The symplectic groups: linear algebra

The alternating form `B(u, v) = uᵀ J v`, `J = [[0, 1], [-1, 0]]`, on `K^{n ⊕ n}`, the symplectic
transvections `w ↦ w + c B(w, v) v`, and the transitivity properties of `Sp_{2n}(K)` on vectors
and on the points of `ℙ(K^{2n})` that feed the polar-space criterion.
-/

namespace CFSGOutside.HallPaige.Symplectic

open Matrix Corpus.Lie

variable {n : ℕ} {K : Type} [Field K]

/-- The standard alternating Gram matrix `[[0, 1], [-1, 0]]`. -/
abbrev J (n : ℕ) (K : Type) [Field K] : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  fromBlocks 0 1 (-1) 0

/-- The standard alternating form. -/
def form (u v : Fin n ⊕ Fin n → K) : K := u ⬝ᵥ (J n K *ᵥ v)

theorem J_mulVec (v : Fin n ⊕ Fin n → K) :
    J n K *ᵥ v = Sum.elim (v ∘ Sum.inr) (-(v ∘ Sum.inl)) := by
  rw [J, fromBlocks_mulVec]
  simp only [zero_mulVec, one_mulVec, zero_add, add_zero, neg_mulVec]

theorem form_eq (u v : Fin n ⊕ Fin n → K) :
    form u v = ∑ i, (u (.inl i) * v (.inr i) - u (.inr i) * v (.inl i)) := by
  rw [form, J_mulVec, dotProduct, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Sum.elim_inl, Sum.elim_inr, Function.comp_apply, Pi.neg_apply]
  ring

theorem form_self (v : Fin n ⊕ Fin n → K) : form v v = 0 := by
  rw [form_eq]
  exact Finset.sum_eq_zero fun i _ => by ring

theorem form_swap (u v : Fin n ⊕ Fin n → K) : form v u = - form u v := by
  rw [form_eq, form_eq, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem form_add_left (u w v : Fin n ⊕ Fin n → K) : form (u + w) v = form u v + form w v := by
  simp only [form, add_dotProduct]

theorem form_add_right (u v w : Fin n ⊕ Fin n → K) : form u (v + w) = form u v + form u w := by
  simp only [form, mulVec_add, dotProduct_add]

theorem form_sub_right (u v w : Fin n ⊕ Fin n → K) : form u (v - w) = form u v - form u w := by
  simp only [form, mulVec_sub, dotProduct_sub]

theorem form_smul_left (c : K) (u v : Fin n ⊕ Fin n → K) : form (c • u) v = c * form u v := by
  simp only [form, smul_dotProduct, smul_eq_mul]

theorem form_smul_right (c : K) (u v : Fin n ⊕ Fin n → K) : form u (c • v) = c * form u v := by
  simp only [form, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_mulVec (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (u w : Fin n ⊕ Fin n → K) :
    form (A *ᵥ u) (A *ᵥ w) = u ⬝ᵥ ((Aᵀ * J n K * A) *ᵥ w) := by
  rw [form, dotProduct_comm, dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose,
    mulVec_mulVec, mulVec_mulVec]

/-- A matrix preserves the form iff `Aᵀ J A = J`. -/
theorem transpose_mul_J_mul_eq_iff (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :
    Aᵀ * J n K * A = J n K ↔ ∀ u w, form (A *ᵥ u) (A *ᵥ w) = form u w := by
  constructor
  · intro h u w
    rw [form_mulVec, h, form]
  · intro h
    ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    rw [form_mulVec, form] at this
    simpa [mulVec_single_one, single_one_dotProduct] using this

/-- Membership in the symplectic group. -/
theorem mem_statedSp_iff (A : GL (Fin n ⊕ Fin n) K) :
    A ∈ StatedSp n K ↔ ∀ u w,
      form ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ u)
        ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ w) = form u w := by
  constructor
  · intro hA
    induction hA using Subgroup.closure_induction with
    | mem A hA => exact (transpose_mul_J_mul_eq_iff (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)).1 hA
    | one => intro u w; simp
    | mul A B _ _ hA hB =>
      intro u w
      rw [Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, hA, hB]
    | inv A _ hA =>
      intro u w
      have hinv : ∀ v : Fin n ⊕ Fin n → K, (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ
          (((A⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) = v := by
        intro v
        rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
      rw [← hA, hinv, hinv]
  · intro h
    exact Subgroup.subset_closure ((transpose_mul_J_mul_eq_iff (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)).2 h)

/-! ### Symplectic transvections -/

/-- The transvection matrix `w ↦ w + c B(w, v) v`. -/
def trMat (v : Fin n ⊕ Fin n → K) (c : K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  1 + c • vecMulVec v (J n K *ᵥ v)

theorem trMat_mulVec (v : Fin n ⊕ Fin n → K) (c : K) (w : Fin n ⊕ Fin n → K) :
    trMat v c *ᵥ w = w + (c * form w v) • v := by
  rw [trMat, add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
    smul_smul, dotProduct_comm]
  rfl

theorem form_trMat (v : Fin n ⊕ Fin n → K) (c : K) (u w : Fin n ⊕ Fin n → K) :
    form (trMat v c *ᵥ u) (trMat v c *ᵥ w) = form u w := by
  rw [trMat_mulVec, trMat_mulVec, form_add_left, form_add_right, form_add_right,
    form_smul_left, form_smul_right, form_smul_right, form_smul_left, form_self, form_swap v w]
  ring

theorem trMat_mul_neg (v : Fin n ⊕ Fin n → K) (c : K) : trMat v c * trMat v (-c) = 1 := by
  refine ext_of_mulVec_single fun i => ?_
  rw [← mulVec_mulVec, trMat_mulVec, trMat_mulVec, one_mulVec, form_add_left, form_smul_left,
    form_self]
  module

/-- The transvection as an element of `GL`. -/
def trGL (v : Fin n ⊕ Fin n → K) (c : K) : GL (Fin n ⊕ Fin n) K :=
  ⟨trMat v c, trMat v (-c), trMat_mul_neg v c, by simpa using trMat_mul_neg v (-c)⟩

/-- The transvection as an element of `Sp`. -/
def trSp (v : Fin n ⊕ Fin n → K) (c : K) : StatedSp n K :=
  ⟨trGL v c, (mem_statedSp_iff _).2 (form_trMat v c)⟩

theorem trSp_smul (v : Fin n ⊕ Fin n → K) (c : K) (w : Fin n ⊕ Fin n → K) :
    trSp v c • w = w + (c * form w v) • v :=
  trMat_mulVec v c w

/-- The symplectic group preserves the form. -/
theorem form_smul (g : StatedSp n K) (u w : Fin n ⊕ Fin n → K) :
    form (g • u) (g • w) = form u w :=
  (mem_statedSp_iff (g : GL (Fin n ⊕ Fin n) K)).1 g.2 u w

/-- **Moving a vector along a transvection.** If `B(y, z) ≠ 0`, a transvection maps `y` to `z`
and fixes every vector perpendicular to `z - y`. -/
theorem exists_move {y z : Fin n ⊕ Fin n → K} (h : form y z ≠ 0) :
    ∃ g : StatedSp n K, g • y = z ∧ ∀ x, form x (z - y) = 0 → g • x = x := by
  refine ⟨trSp (z - y) (form y z)⁻¹, ?_, fun x hx => ?_⟩
  · rw [trSp_smul, form_sub_right, form_self, sub_zero, inv_mul_cancel₀ h, one_smul]
    abel
  · rw [trSp_smul, hx, mul_zero, zero_smul, add_zero]

/-- The partner of a coordinate: `inl i ↔ inr i`. -/
def partner : Fin n ⊕ Fin n → Fin n ⊕ Fin n
  | .inl i => .inr i
  | .inr i => .inl i

theorem form_single_partner (y : Fin n ⊕ Fin n → K) (j : Fin n ⊕ Fin n) :
    form y (Pi.single (partner j) 1) = match j with
      | .inl i => y (.inl i)
      | .inr i => -y (.inr i) := by
  rw [form_eq]
  rcases j with i | i <;>
    simp [partner, Pi.single_apply, Finset.sum_sub_distrib, Finset.sum_ite_eq']

/-- A vector with a nonzero coordinate at `j` pairs nontrivially with the partner basis vector. -/
theorem form_single_partner_ne_zero (y : Fin n ⊕ Fin n → K) {j : Fin n ⊕ Fin n} (hj : y j ≠ 0) :
    form y (Pi.single (partner j) 1) ≠ 0 := by
  rw [form_single_partner]
  rcases j with i | i
  · exact hj
  · exact neg_ne_zero.2 hj

/-- A common partner: given a subspace condition `P` and two vectors each pairing nontrivially
with some vector satisfying `P`, some vector satisfying `P` pairs nontrivially with both. -/
theorem exists_common {P : (Fin n ⊕ Fin n → K) → Prop} (hP : ∀ a b, P a → P b → P (a + b))
    {y y' : Fin n ⊕ Fin n → K} (h : ∃ z, P z ∧ form y z ≠ 0) (h' : ∃ z, P z ∧ form y' z ≠ 0) :
    ∃ z, P z ∧ form y z ≠ 0 ∧ form y' z ≠ 0 := by
  obtain ⟨z, hz, hyz⟩ := h
  obtain ⟨z', hz', hyz'⟩ := h'
  by_cases h1 : form y' z ≠ 0
  · exact ⟨z, hz, hyz, h1⟩
  by_cases h2 : form y z' ≠ 0
  · exact ⟨z', hz', h2, hyz'⟩
  push Not at h1 h2
  refine ⟨z + z', hP _ _ hz hz', ?_, ?_⟩
  · rw [form_add_right, h2, add_zero]; exact hyz
  · rw [form_add_right, h1, zero_add]; exact hyz'

/-- Every nonzero vector pairs nontrivially with some vector. -/
theorem exists_form_ne_zero {y : Fin n ⊕ Fin n → K} (hy : y ≠ 0) : ∃ z, True ∧ form y z ≠ 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
  exact ⟨_, trivial, form_single_partner_ne_zero y hj⟩

/-- **`Sp` is transitive on nonzero vectors.** -/
theorem exists_smul_eq {u w : Fin n ⊕ Fin n → K} (hu : u ≠ 0) (hw : w ≠ 0) :
    ∃ g : StatedSp n K, g • u = w := by
  by_cases huw : form u w ≠ 0
  · obtain ⟨g, hg, -⟩ := exists_move huw
    exact ⟨g, hg⟩
  obtain ⟨z, -, hz, hz'⟩ := exists_common (P := fun _ => True) (fun _ _ _ _ => trivial)
    (exists_form_ne_zero hu) (exists_form_ne_zero hw)
  obtain ⟨g, hg, -⟩ := exists_move hz
  obtain ⟨g', hg', -⟩ := exists_move (y := z) (z := w) (by rw [form_swap]; exact neg_ne_zero.2 hz')
  exact ⟨g' * g, by rw [mul_smul, hg, hg']⟩

/-! ### The stabilizer of a basis vector -/

/-- `B(e_{i₀}, y) = y_{f_{i₀}}`. -/
theorem form_single_inl (i₀ : Fin n) (y : Fin n ⊕ Fin n → K) :
    form (Pi.single (.inl i₀) 1) y = y (.inr i₀) := by
  rw [form_eq]
  simp [Pi.single_apply]

theorem partner_eq_inr_iff (j : Fin n ⊕ Fin n) (i₀ : Fin n) :
    partner j = .inr i₀ ↔ j = .inl i₀ := by
  rcases j with i | i <;> simp [partner]

/-- A vector perpendicular to `e = e_{i₀}` and not a multiple of it pairs nontrivially with some
vector perpendicular to `e`. -/
theorem exists_perp_form_ne_zero (i₀ : Fin n) {y : Fin n ⊕ Fin n → K}
    (hy : ∀ c : K, y ≠ c • Pi.single (.inl i₀) 1) :
    ∃ z, form (Pi.single (.inl i₀) 1) z = 0 ∧ form y z ≠ 0 := by
  obtain ⟨j, hj, hyj⟩ : ∃ j, j ≠ .inl i₀ ∧ y j ≠ 0 := by
    by_contra h
    push Not at h
    apply hy (y (.inl i₀))
    funext k
    by_cases hk : k = .inl i₀
    · subst hk; simp
    · rw [h k hk]; simp [Pi.single_apply, hk]
  refine ⟨Pi.single (partner j) 1, ?_, form_single_partner_ne_zero y hyj⟩
  rw [form_single_inl, Pi.single_apply, if_neg]
  intro h
  exact hj ((partner_eq_inr_iff _ _).1 h.symm)

/-- **The stabilizer of `e` is transitive on the vectors `y` with `B(e, y) = 1`.** -/
theorem exists_smul_eq_of_form_eq_one (i₀ : Fin n) {y y' : Fin n ⊕ Fin n → K}
    (hy : form (Pi.single (.inl i₀) 1) y = 1) (hy' : form (Pi.single (.inl i₀) 1) y' = 1) :
    ∃ g : StatedSp n K, g • (Pi.single (.inl i₀) 1 : Fin n ⊕ Fin n → K) = Pi.single (.inl i₀) 1 ∧
      g • y = y' := by
  set e : Fin n ⊕ Fin n → K := Pi.single (.inl i₀) 1
  by_cases hyy : form y y' ≠ 0
  · obtain ⟨g, hg, hfix⟩ := exists_move hyy
    exact ⟨g, hfix e (by rw [form_sub_right, hy, hy', sub_self]), hg⟩
  push Not at hyy
  have h1 : form y (y + e) ≠ 0 := by
    rw [form_add_right, form_self, zero_add, form_swap, hy]; exact neg_ne_zero.2 one_ne_zero
  obtain ⟨g, hg, hfix⟩ := exists_move h1
  have h2 : form (y + e) y' ≠ 0 := by
    rw [form_add_left, hyy, zero_add, hy']; exact one_ne_zero
  obtain ⟨g', hg', hfix'⟩ := exists_move h2
  refine ⟨g' * g, ?_, by rw [mul_smul, hg, hg']⟩
  rw [mul_smul, hfix e (by rw [add_sub_cancel_left, form_self]),
    hfix' e (by rw [form_sub_right, form_add_right, hy', hy, form_self, add_zero, sub_self])]

/-- **The stabilizer of `e` is transitive on the vectors perpendicular to `e` outside `K e`.** -/
theorem exists_smul_eq_of_form_eq_zero (i₀ : Fin n) {y y' : Fin n ⊕ Fin n → K}
    (hy : form (Pi.single (.inl i₀) 1) y = 0) (hy' : form (Pi.single (.inl i₀) 1) y' = 0)
    (hny : ∀ c : K, y ≠ c • Pi.single (.inl i₀) 1)
    (hny' : ∀ c : K, y' ≠ c • Pi.single (.inl i₀) 1) :
    ∃ g : StatedSp n K, g • (Pi.single (.inl i₀) 1 : Fin n ⊕ Fin n → K) = Pi.single (.inl i₀) 1 ∧
      g • y = y' := by
  set e : Fin n ⊕ Fin n → K := Pi.single (.inl i₀) 1
  by_cases hyy : form y y' ≠ 0
  · obtain ⟨g, hg, hfix⟩ := exists_move hyy
    exact ⟨g, hfix e (by rw [form_sub_right, hy, hy', sub_self]), hg⟩
  obtain ⟨z, hz, hyz, hyz'⟩ := exists_common (P := fun z => form e z = 0)
    (fun a b ha hb => by rw [form_add_right, ha, hb, add_zero])
    (exists_perp_form_ne_zero i₀ hny) (exists_perp_form_ne_zero i₀ hny')
  obtain ⟨g, hg, hfix⟩ := exists_move hyz
  obtain ⟨g', hg', hfix'⟩ := exists_move (y := z) (z := y')
    (by rw [form_swap]; exact neg_ne_zero.2 hyz')
  refine ⟨g' * g, ?_, by rw [mul_smul, hg, hg']⟩
  rw [mul_smul, hfix e (by rw [form_sub_right, hz, hy, sub_self]),
    hfix' e (by rw [form_sub_right, hy', hz, sub_self])]

end CFSGOutside.HallPaige.Symplectic
