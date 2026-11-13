import CFSGOutside.Corpus.Defs.Suzuki

/-!
# Corpus input: involution centralizers in `Sz(q)` are `2`-groups

Statement of `CFSG.LieType.SuzukiSubgroups.isPGroup_centralizer_of_isSz`, copied verbatim from
`CFSG/LieType/SuzukiSubgroups/Facts.lean` (line 84) at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962, with `IsSz` the copy
in `CFSGOutside.Corpus`.
-/

namespace CFSGOutside.Corpus

/-- In a group `H ≅ Sz(2 ^ n)` the centralizer of an involution is a `2`-group. -/
class IsPGroupCentralizerOfIsSz : Prop where
  isPGroup_centralizer_of_isSz : ∀ {n : ℕ} {H : Type} [Group H] (_hH : IsSz n H) {x : H}
    (_hx : orderOf x = 2), IsPGroup 2 (Subgroup.centralizer ({x} : Set H))

end CFSGOutside.Corpus
