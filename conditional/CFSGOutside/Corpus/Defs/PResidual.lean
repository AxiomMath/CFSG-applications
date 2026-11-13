import Mathlib

/-!
# Copied corpus definition: the `p`-residual

Copy of `CFSG.Quasithin.pResidual`, `CFSG/Quasithin/Background/A1cTransfer.lean` line 169, at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962.
-/

namespace CFSGOutside.Corpus.Quasithin

/-- The intersection of the normal subgroups with `p`-group quotient. -/
def pResidual (p : ℕ) (X : Type*) [Group X] : Subgroup X :=
  ⨅ (N : Subgroup X) (_ : N.Normal) (_ : ∀ x : X, ∃ k : ℕ, x ^ p ^ k ∈ N), N

end CFSGOutside.Corpus.Quasithin
