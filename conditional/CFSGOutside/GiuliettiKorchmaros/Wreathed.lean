import CFSGOutside.Corpus.Defs.LowTwoRankCatalog

/-! # Exponent and order of the wreathed 2-group `C_{2^n} ≀ C_2` -/

namespace CFSGOutside.GiuliettiKorchmaros

open CFSGOutside.Corpus

open scoped MatrixGroups

section B

/-- (B1) Every element `x` of the wreathed group `C_{2^n} ≀ C_2` satisfies `x ^ 2^(n+1) = 1`. -/
theorem wreathed_pow_eq_one (n : ℕ) (x : Open.WreathedTwoGroup n) : x ^ (2 ^ (n + 1)) = 1 := by
  have hz : ∀ g : Multiplicative (ZMod (2 ^ n)), g ^ (2 ^ n) = 1 := by
    intro g
    have : g = Multiplicative.ofAdd (Multiplicative.toAdd g) := rfl
    rw [this, ← ofAdd_nsmul]
    have h0 : (2 ^ n : ℕ) • Multiplicative.toAdd g = 0 := by
      rw [nsmul_eq_mul]
      have : ((2 ^ n : ℕ) : ZMod (2 ^ n)) = 0 := ZMod.natCast_self _
      rw [this, zero_mul]
    rw [h0]; rfl
  have hq : ∀ g : Multiplicative (ZMod 2), g ^ 2 = 1 := by decide
  have key : ∀ y : Open.WreathedTwoGroup n, y.right = 1 → ∀ k : ℕ,
      (y ^ k).right = 1 ∧ (y ^ k).left = y.left ^ k := by
    intro y hy k
    induction k with
    | zero => exact ⟨by simp [RegularWreathProduct.one_right], by simp [RegularWreathProduct.one_left]⟩
    | succ k ih =>
      refine ⟨?_, ?_⟩
      · rw [pow_succ, RegularWreathProduct.mul_right, ih.1, hy, one_mul]
      · rw [pow_succ, RegularWreathProduct.mul_left, ih.2, ih.1]; simp [pow_succ]; funext q; show y.left (1⁻¹ * q) = y.left q; congr 1; revert q; decide
  have hy : (x ^ 2).right = 1 := by
    rw [pow_two, RegularWreathProduct.mul_right, ← pow_two]; exact hq _
  rw [pow_succ, mul_comm, pow_mul]
  obtain ⟨h1, h2⟩ := key (x ^ 2) hy (2 ^ n)
  refine RegularWreathProduct.ext ?_ h1
  rw [h2, RegularWreathProduct.one_left]
  funext q
  exact hz _

/-- (B2) `|C_{2^n} ≀ C_2| = 2^(2n+1)`. -/
theorem card_wreathed (n : ℕ) : Nat.card (Open.WreathedTwoGroup n) = 2 ^ (2 * n + 1) := by
  rw [Nat.card_congr (RegularWreathProduct.equivProd _ _), Nat.card_prod, Nat.card_fun]
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  ring

end B

end CFSGOutside.GiuliettiKorchmaros
