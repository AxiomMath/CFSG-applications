import CFSGOutside.Corpus.Defs.ClassicalModel

/-!
# Corpus input: the Sylow 2-subgroup of `U₃(4)`

Statement of `CFSG.LyonsUnitaryFour.unitary_four_sylow_structure`, copied verbatim from
`CFSG/LocalAnalysis/LyonsUnitaryFour/Local.lean` (line 56, with the section variables of line 33, `[Finite G]`
omitted as the corpus omits it) at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962.
`CFSG.Assembly.LowTwoRank.StatedClassicalModel` is an `export` of `CFSG.Open.StatedClassicalModel`, copied in
`CFSGOutside.Corpus.Defs`.
-/

namespace CFSGOutside.Corpus

/-- A Sylow 2-subgroup of `U₃(4)` has order 64, its squares are central, and its involutions are central,
as `CFSG.LyonsUnitaryFour.unitary_four_sylow_structure` states it. -/
class UnitaryFourSylowStructure : Prop where
  unitary_four_sylow_structure : ∀ {G : Type} [Group G] {T : Type} [Group T]
    (_hT : Open.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (_hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T))),
    Nat.card (S : Subgroup G) = 64 ∧
      Subgroup.center (S : Subgroup G) = commutator (S : Subgroup G) ∧
      (∀ y : (S : Subgroup G), y ^ 2 = 1 ↔ y ∈ Subgroup.center (S : Subgroup G)) ∧
      (∀ y : (S : Subgroup G), y ^ 2 ∈ Subgroup.center (S : Subgroup G)) ∧
      Nat.card (Subgroup.center (S : Subgroup G)) = 4

end CFSGOutside.Corpus
