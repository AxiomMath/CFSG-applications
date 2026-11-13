import Mathlib

/-!
# Corpus input: Zsigmondy's theorem for base and exponent at least 3

Statement of `CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one`
(`CFSG/LinearAlgebra/SL2MinimalFaithfulZsigmondy.lean`, line 150, at
AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962), copied verbatim (the implicit
arguments `{a n : ℕ}` become universally quantified fields).
-/

namespace CFSGOutside.Corpus

/-- Zsigmondy: `a ^ n - 1` has a primitive prime divisor for `a ≥ 3`, `n ≥ 3`. -/
class SL2MinimalFaithfulZsigmondy : Prop where
  exists_primitive_prime_dvd_pow_sub_one : ∀ {a n : ℕ} (_ha : 3 ≤ a) (_hn : 3 ≤ n),
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ a ^ n - 1 ∧ ∀ k : ℕ, 0 < k → k < n → ¬ ℓ ∣ a ^ k - 1

end CFSGOutside.Corpus
