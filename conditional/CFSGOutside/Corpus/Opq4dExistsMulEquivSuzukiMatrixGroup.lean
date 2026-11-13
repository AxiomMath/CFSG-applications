import CFSGOutside.Corpus.Defs.Suzuki
import CFSGOutside.Corpus.Defs.SuzukiMatrixGroup

/-!
# Corpus input: a group `X` with `IsSz n X` is isomorphic to the Suzuki matrix group

Statement of `CFSG.Quasithin.opq4d_exists_mulEquiv_suzukiMatrixGroup`, copied verbatim from
`CFSG/Quasithin/Background/F918Z8Op4d.lean` (line 20) at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962, with `IsSz` and
`SuzukiMatrixGroup` the copies in `CFSGOutside.Corpus`.
-/

namespace CFSGOutside.Corpus

/-- If `X ≅ Sz(2 ^ n)` then `n = 2m + 1` with `m ≥ 1` and `X` is isomorphic to the matrix model
`SuzukiMatrixGroup m`. -/
class Opq4dExistsMulEquivSuzukiMatrixGroup : Prop where
  opq4d_exists_mulEquiv_suzukiMatrixGroup : ∀ {X : Type} [Group X] {n : ℕ} (_hX : IsSz n X),
    ∃ m : ℕ, 1 ≤ m ∧ n = 2 * m + 1 ∧ Nonempty (X ≃* SuzukiMatrixGroup m)

end CFSGOutside.Corpus
