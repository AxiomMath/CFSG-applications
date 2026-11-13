import CFSGOutside.Corpus.Defs.J1Models
import CFSGOutside.Corpus.Defs.ReeModel

/-!
# Corpus input: the order of the small Ree group model

Statement of `CFSG.ClassicalInvolution.card_of_reeTitsModel_twistedG2`
(`CFSG/ClassicalInvolution/Orders/Ree.lean`, line 12, at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962). `ReeTitsModel` and `ordRee` are the copies in
`CFSGOutside.Corpus.Defs`.
-/

namespace CFSGOutside.Corpus

/-- A group modelled as `²G₂(p^f)` has `p = 3`, `f = 2a + 1` with `a ≥ 1`, and order `|²G₂(3^f)|`. -/
class CardOfReeTitsModelTwistedG2 : Prop where
  card_of_reeTitsModel_twistedG2 : ∀ {G : Type} [Group G] {p f : ℕ},
    Blueprint.ReeTitsModel G .twistedG2 p f →
    p = 3 ∧ ∃ a : ℕ, 1 ≤ a ∧ f = 2 * a + 1 ∧ Nat.card G = Open.ordRee (3 ^ f)

end CFSGOutside.Corpus
