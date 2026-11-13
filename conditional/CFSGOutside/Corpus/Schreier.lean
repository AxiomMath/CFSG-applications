import CFSGOutside.Corpus.Defs.InCatalog
import CFSGOutside.Corpus.Defs.OuterAutomorphisms

/-!
# Corpus input: the Schreier conjecture for the catalogue

Statement of `CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds`
(`CFSG/RankThree/PartOne/TCB/SchreierFinal.lean`, line 12, at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962), which is `SchreierFor InCatalog`. Here
`CFSG.LocalAnalysis.ComponentInitial.SchreierFor` (`CFSG/LocalAnalysis/ComponentInitial/KProperPumpUpStatement.lean`,
line 12) is unfolded, and `InCatalog` and `Outer` are the copies in `CFSGOutside.Corpus.Defs`.

Every nonabelian finite simple group in the catalogue has a solvable outer automorphism group. Results that
assume the classification statement use it with `TauCeti.classificationStatement_iff`.
-/

namespace CFSGOutside.Corpus

/-- Schreier's conjecture for every group in the catalogue, as `schreierFor_inCatalog_holds` states it. -/
class Schreier : Prop where
  schreierFor_inCatalog_holds : ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X],
    (∃ a b : X, a * b ≠ b * a) → Assembly.InCatalog X →
      Group.IsSolvable (ComponentClassification.OuterAutomorphisms.Outer X)

end CFSGOutside.Corpus
