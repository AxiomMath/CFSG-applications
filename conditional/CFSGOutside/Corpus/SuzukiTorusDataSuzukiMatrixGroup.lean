import CFSGOutside.Corpus.Defs.SuzukiMatrixGroup
import CFSGOutside.Corpus.Defs.SuzukiTorusData

/-!
# Corpus input: the Suzuki matrix group satisfies the point/torus axioms

Statement of `CFSG.LocalAnalysis.UniquenessCase.UC22.suzukiTorusData_suzukiMatrixGroup`, copied verbatim from
`CFSG/LocalAnalysis/UniquenessCase/PartTwo/Section23/ProofsSzPointActionTorus.lean` (line 216) at
AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962, with `SuzukiTorusData` and `SuzukiMatrixGroup` the copies in
`CFSGOutside.Corpus`.
-/

namespace CFSGOutside.Corpus

/-- `Sz(2 ^ (2m+1))`, in its matrix model, satisfies the Suzuki point/torus axioms. -/
class SuzukiTorusDataSuzukiMatrixGroup : Prop where
  suzukiTorusData_suzukiMatrixGroup : ∀ (m : ℕ) (_hm : 0 < m),
    SuzukiTorusData (SuzukiMatrixGroup m) (2 ^ (2 * m + 1))

end CFSGOutside.Corpus
