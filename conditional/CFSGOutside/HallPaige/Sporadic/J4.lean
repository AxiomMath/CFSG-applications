import CFSGOutside.HallPaige.Sporadic.J4.Cover
import CFSGOutside.Corpus.HallPaige.Fi23
import CFSGOutside.HallPaige.CatalogueDefs
import CFSGOutside.HallPaige.Cosets
import CFSGOutside.HallPaige.Transport

/-!
# The catalogue case of the Janko group `J₄`

The matrix model `J ≤ GL₁₁₂(𝔽₂)` satisfies the Wilcox criterion
(`CFSGOutside.HallPaige.J4.wilcoxCriterion_J`, with `H` the stabilizer of a `10`-dimensional
subspace fixed by the centralizer of a `2A`-involution), and it is isomorphic to the TauCeti
presented group `J₄` (corpus `CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv`, through the seed
isomorphism of `CFSG/Sporadic/J4/Group.lean`, here rebuilt from `matrixSeedEquiv`).

Corpus input: `Corpus.J4.Bridge`, `Corpus.J4.Cover`, `Corpus.J4.Stab`
(`CFSGOutside/Corpus/HallPaige/J4.lean`).
-/

namespace CFSGOutside.HallPaige

open CFSGOutside.Corpus.J4

set_option maxRecDepth 100000

namespace J4

attribute [local irreducible] decode J4Seed1 J4Seed2

/-- The native model is isomorphic to `J` (corpus `CFSG.Sporadic.J4.seedEquiv`,
CFSG/Sporadic/J4/Group.lean:80, rebuilt with the determinant conditions proved here). -/
noncomputable def seedEquiv : Corpus.J4.J4 ≃* Corpus.J4.J :=
  (CFSGOutside.Corpus.Fi23.matrixSeedEquiv 2 112 (by norm_num) matA matB det_matA det_matB).trans
    (MulEquiv.subgroupCongr (by
      show _ = Subgroup.closure {gA, gB}
      rw [gA_eq, gB_eq]))

end J4

section
variable [h0 : Corpus.J4.Bridge] [h1 : Corpus.J4.Cover] [h2 : Corpus.J4.Stab]
include h0 h1 h2

attribute [local irreducible] decode J4Seed1 J4Seed2

theorem J4.hasCompleteMapping_J (hP : ProperSubgroupsAdmissible Corpus.J4.J) :
    HasCompleteMapping Corpus.J4.J :=
  hasCompleteMapping_of_wilcoxCriterion (G := Corpus.J4.J) cosetStatement J4.wilcoxCriterion_J hP

/-- **Hall–Paige for `J₄`**: the minimal-counterexample step for the Janko group `J₄`. -/
theorem catalogueCase_J4 : CatalogueCase (.sporadic .J4) := by
  intro _ hP
  obtain ⟨e₀⟩ := Corpus.J4.Bridge.nonempty_mulEquiv
  have e : TauCeti.SporadicName.J4.Group ≃* Corpus.J4.J :=
    e₀.symm.trans CFSGOutside.HallPaige.J4.seedEquiv
  exact @HasCompleteMapping.of_mulEquiv Corpus.J4.J _ TauCeti.SporadicName.J4.Group _ e.symm
    (CFSGOutside.HallPaige.J4.hasCompleteMapping_J
      (@ProperSubgroupsAdmissible.of_mulEquiv TauCeti.SporadicName.J4.Group Corpus.J4.J _ _ e hP))

end

end CFSGOutside.HallPaige
