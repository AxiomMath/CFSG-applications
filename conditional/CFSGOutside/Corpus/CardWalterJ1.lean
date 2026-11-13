import CFSGOutside.Corpus.Defs.J1Models

/-!
# Corpus input: the order of the matrix model of `J₁`

Statement of `CFSG.Walter.J1Props.card_walterJ1` (`CFSG/Walter/J1Props/Elt.lean`, line 88, at
AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962). `walterJ1` is the copy in
`CFSGOutside.Corpus.Defs`.
-/

namespace CFSGOutside.Corpus

/-- `|J₁| = 175560`, as `card_walterJ1` states it. -/
class CardWalterJ1 : Prop where
  card_walterJ1 : Nat.card Open.walterJ1 = 175560

end CFSGOutside.Corpus
