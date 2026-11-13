import CFSGOutside.Corpus.Defs.Suzuki

/-!
# Corpus input: `Sz(q)` is finite, simple and nonabelian

Statement of `CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suzukiGroup_simple_nonab`, copied verbatim from
`CFSG/HardMathSupport/Solomon/Coordinator/LieComp/FactorSRT.lean` (line 148) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962, with `suzukiGroup` the copy in `CFSGOutside.Corpus`.
-/

namespace CFSGOutside.Corpus

/-- `Sz(q)`, `q ≥ 8`, is finite, simple and nonabelian. -/
class SuzukiGroupSimpleNonab : Prop where
  suzukiGroup_simple_nonab : ∀ {b : ℕ} (_hb : 1 ≤ b) {k : Type} [Field k] [Finite k]
    (_hk : Nat.card k = 2 ^ (2 * b + 1)),
    Finite (suzukiGroup b k) ∧ IsSimpleGroup (suzukiGroup b k) ∧
      ∃ x y : suzukiGroup b k, x * y ≠ y * x

end CFSGOutside.Corpus
