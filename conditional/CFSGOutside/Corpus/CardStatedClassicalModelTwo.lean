import CFSGOutside.Corpus.Defs.ClassicalModel
import CFSGOutside.Corpus.Defs.OrdFormulas

/-!
# Corpus input: orders of classical groups in characteristic two

Statement of `CFSG.Timmesfeld.card_statedClassicalModel_two`
(`CFSG/Timmesfeld/Orders/Classical.lean`, line 44, at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962). The order formulas are the copies in
`CFSGOutside.Corpus.Defs.OrdFormulas`.
-/

namespace CFSGOutside.Corpus

/-- The order of a classical model over a field of characteristic two. -/
class CardStatedClassicalModelTwo : Prop where
  card_statedClassicalModel_two : ∀ {G : Type} [Group G] {t : Open.StatedLieTag} {n f : ℕ}
    (_h : Open.StatedClassicalModel G t n 2 f),
    (t = .PSL → Nat.card G = Open.ordA (n - 1) (2 ^ f)) ∧
    (t = .PSU → Nat.card G = Open.ordTwistedA (n - 1) (2 ^ f)) ∧
    (t = .PSp → Nat.card G = Open.ordBC n (2 ^ f)) ∧
    (t = .POmegaPlus → Nat.card G = Open.ordD n (2 ^ f)) ∧
    (t = .POmegaMinus → Nat.card G = Open.ordTwistedD n (2 ^ f))

end CFSGOutside.Corpus
