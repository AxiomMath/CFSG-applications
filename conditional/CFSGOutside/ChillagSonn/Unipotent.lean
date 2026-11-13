import CFSGOutside.Corpus.Defs.ClassicalModel

/-!
# `p`-elements of the corpus models of `PSL(n,q)` and `PSU(n,q)`

In characteristic `p`, a `p`-element `u` of `GL(n, K)` is unipotent, `(u - 1) ^ n = 0`, so its order
divides `p ^ b` once `n ≤ p ^ b`; the same bound passes to `StatedProj H`. We also identify Mathlib's
`PSL(n, K)` with the corpus model `StatedProj (StatedSL n K)`.
-/

namespace CFSGOutside.ChillagSonn

open CFSGOutside.Corpus.Open Matrix

/-- A `p`-element of `GL(n, K)` in characteristic `p` is unipotent, so its order divides `p^b` once `n ≤ p^b`. -/
theorem pow_eq_one_of_charP {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}
    (A : GL (Fin n) K) {a : ℕ} (hA : A ^ (p ^ a) = 1) {b : ℕ} (hb : n ≤ p ^ b) : A ^ (p ^ b) = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Units.ext (Subsingleton.elim _ _)
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set M : Matrix (Fin n) (Fin n) K := (A : Matrix (Fin n) (Fin n) K) - 1 with hM
  have h1 : M ^ (p ^ a) = 0 := by
    rw [hM, sub_pow_char_pow_of_commute p a (Commute.one_right _), one_pow, ← Units.val_pow_eq_pow_val,
      hA, Units.val_one, sub_self]
  have hchar : M.charpoly = Polynomial.X ^ n := by
    simpa [sub_eq_zero] using
      (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent (M := M) ⟨_, h1⟩).eq_zero
  have h2 : M ^ (p ^ b) = 0 := pow_eq_zero_of_le hb (by simpa [hchar] using M.aeval_self_charpoly)
  have hA' : (A : Matrix (Fin n) (Fin n) K) = M + 1 := by simp [hM]
  ext1
  rw [Units.val_pow_eq_pow_val, hA', add_pow_char_pow_of_commute p b (Commute.one_right _), h2, one_pow,
    zero_add, Units.val_one]

/-- In `StatedProj H` (`K` finite of characteristic `p`), an element of `p`-power order has order dividing `p^b` once
`n ≤ p^b`. -/
theorem statedProj_pow_eq_one {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}
    (H : Subgroup (GL (Fin n) K)) (x : StatedProj H) {a : ℕ} (hx : x ^ (p ^ a) = 1) {b : ℕ} (hb : n ≤ p ^ b) :
    x ^ (p ^ b) = 1 := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨c, r, hr, hcr⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' p hp.ne_one
  have hz : ((y ^ r : H) : GL (Fin n) K) ^ (p ^ b) = 1 := by
    refine pow_eq_one_of_charP _ (a := c) ?_ hb
    rw [← Subgroup.coe_pow, ← pow_mul, mul_comm, ← hcr, pow_orderOf_eq_one, Subgroup.coe_one]
  have hzH : (y ^ r) ^ (p ^ b) = 1 := Subtype.ext (by simpa using hz)
  have hz' : ((QuotientGroup.mk y : StatedProj H) ^ r) ^ (p ^ b) = 1 := by
    rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, hzH, QuotientGroup.mk_one]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hx)
  have hcop : (orderOf (QuotientGroup.mk y : StatedProj H)).Coprime r := by
    rw [hk]; exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hr)
  rw [← orderOf_dvd_iff_pow_eq_one, ← hcop.orderOf_pow]
  exact orderOf_dvd_of_pow_eq_one hz'

/-- Every element of a `p`-subgroup of `StatedProj H` satisfies `x ^ (p ^ b) = 1` once `n ≤ p ^ b`. -/
theorem statedProj_pow_eq_one_of_isPGroup {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    {n : ℕ} (H : Subgroup (GL (Fin n) K)) (Q : Subgroup (StatedProj H)) (hQ : IsPGroup p Q) {b : ℕ}
    (hb : n ≤ p ^ b) : ∀ x ∈ Q, x ^ (p ^ b) = 1 := fun x hx => by
  obtain ⟨k, hk⟩ := hQ ⟨x, hx⟩
  exact statedProj_pow_eq_one H x (a := k) (by simpa using congrArg Subtype.val hk) hb

/-- A finite field of order `p ^ f` (`f ≥ 1`) has characteristic `p`. -/
theorem charP_of_card_eq_pow {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) : CharP K p := by
  have := Fintype.ofFinite K
  obtain ⟨q, hq, m, hqp, hcard⟩ := FiniteField.card' K
  rw [Nat.card_eq_fintype_card, hcard] at hK
  have hdvd : q ∣ p ^ f := hK ▸ dvd_pow_self q m.ne_zero
  rwa [← (Nat.prime_dvd_prime_iff_eq hqp Fact.out).mp (hqp.dvd_of_dvd_pow hdvd)]

/-- `StatedSL n K` is the image of `SL(n, K)` in `GL(n, K)`, i.e. the kernel of the determinant. -/
theorem statedSL_eq_ker_det (n : ℕ) (K : Type) [Field K] :
    StatedSL n K = (GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker := by
  rw [StatedSL]
  convert Subgroup.closure_eq (GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker using 2
  ext A
  simp [MonoidHom.mem_ker, Units.ext_iff]

/-- `PSL(n, K)` is the corpus model `StatedProj (StatedSL n K)`. -/
noncomputable def projectiveSpecialLinearEquivStatedProj (n : ℕ) (K : Type) [Field K] :
    Matrix.ProjectiveSpecialLinearGroup (Fin n) K ≃* StatedProj (StatedSL n K) :=
  let e : SpecialLinearGroup (Fin n) K ≃* StatedSL n K :=
    SpecialLinearGroup.toGLKerEquiv.trans (MulEquiv.subgroupCongr (statedSL_eq_ker_det n K).symm)
  QuotientGroup.congr _ _ e <| by
    ext y
    change y ∈ Subgroup.map e.toMonoidHom _ ↔ _
    rw [Subgroup.mem_map_equiv, ← SpecialLinearGroup.toGL_mem_center_iff, Subgroup.mem_subgroupOf,
      StatedScalars, ← GeneralLinearGroup.center_eq_range_scalar,
      show SpecialLinearGroup.toGL (e.symm y) = y from Units.ext rfl]

end CFSGOutside.ChillagSonn
