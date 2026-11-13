import CFSGOutside.Corpus.Defs.Components
import CFSGOutside.Corpus.Defs.Fitting

/-!
# Copied corpus definition: the generalized Fitting subgroup

Copy, under `CFSGOutside.Corpus`, of `CFSG.generalizedFitting` from AxiomMath/CFSG at commit
69cb972f587a3ecc035e092253167ff2e303c962. `clean/CFSGOutsideClean/Corpus/Defs/GeneralizedFitting.lean` shows
that the copy equals the original.
-/

namespace CFSGOutside.Corpus

variable (G : Type*) [Group G]

/-- The generalized Fitting subgroup `F*(G) = F(G) E(G)`. Copy of `CFSG.generalizedFitting`,
`CFSG/Foundations/Basic.lean` line 53, with `CFSG.WholeGroup.fstarOf` unfolded to
`CFSG.generalizedFitting.eq_sup`, line 57. -/
def generalizedFitting : Subgroup G :=
  fittingSubgroup G ⊔ layer G

theorem generalizedFitting.eq_sup : generalizedFitting G = fittingSubgroup G ⊔ layer G :=
  rfl

instance generalizedFitting_normal : (generalizedFitting G).Normal :=
  Subgroup.sup_normal _ _

end CFSGOutside.Corpus
