import Mathlib

/-!
# Copied corpus definition: elementary abelian groups

Copied verbatim from AxiomMath/CFSG at commit 69cb972f587a3ecc035e092253167ff2e303c962, under
`CFSGOutside.Corpus`. The clean build relates it to the corpus class in
`clean/CFSGOutsideClean/Corpus/Defs/ElementaryAbelian.lean`.
-/

universe u

namespace CFSGOutside.Corpus

open scoped IsMulCommutative

/-- An *elementary abelian* `p`-group: a commutative group whose exponent divides `p`. Copy of
`CFSG.IsElementaryAbelian`, `CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/ElementaryAbelian.lean` line 28. -/
class IsElementaryAbelian (p : ℕ) (G : Type u) [Group G] : Prop
    extends IsMulCommutative G where
  exponent_dvd_p (p) (G) : Monoid.exponent G ∣ p

end CFSGOutside.Corpus
