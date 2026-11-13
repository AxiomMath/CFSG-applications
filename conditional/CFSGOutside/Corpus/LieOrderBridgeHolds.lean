import CFSGOutside.Corpus.Defs.LieOrder

/-!
# Corpus input: orders of the groups of Lie type in the catalogue

Statement of `CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds`
(`CFSG/HardMathSupport/Solomon/Coordinator/LieOrderBridgeHolds.lean`, line 293, at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962), which is `LieOrderBridge`
(`CFSG/HardMathSupport/Solomon/Coordinator/I14_20LieEnd.lean`, line 17) unfolded. `lieOrderFormula` is the
copy in `CFSGOutside.Corpus.Defs.LieOrder`.

A finite group isomorphic to the catalogue group of a valid Lie type index has the order given by the
formula `lieOrderFormula`.
-/

namespace CFSGOutside.Corpus

/-- The catalogue groups of Lie type have the orders given by `lieOrderFormula`, as `lieOrderBridge_holds`
states it. -/
class LieOrderBridgeHolds : Prop where
  lieOrderBridge_holds : ∀ (idx : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G],
    Nonempty (G ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      Nat.card G = HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula idx.1

end CFSGOutside.Corpus
