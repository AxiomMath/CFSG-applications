import CFSGOutside.Corpus.Defs.J1Models
import CFSGOutside.Corpus.Defs.ReeModel

/-!
# Corpus input: Walter's theorem with the Ree case as a model

Statement of `CFSG.Quasithin.H13.S3320.walter_split`
(`CFSG/Quasithin/Vol2/Ch3Sec3InspWalterHolds.lean`, line 20, at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962). `ReeTitsModel` and `walterJ1` are the copies in
`CFSGOutside.Corpus.Defs`.

A finite nonabelian simple group with an abelian Sylow 2-subgroup is `PSL(2, 2^f)` (`f ≥ 2`), `PSL(2, q)`
(`q ≡ ±3 mod 8`, `q ≥ 5`), the small Ree group `²G₂(3^f)` (`f` odd, `f ≥ 3`), or `J₁`.
-/

open scoped MatrixGroups

namespace CFSGOutside.Corpus

/-- Walter's theorem, as `walter_split` states it. -/
class WalterSplit : Prop where
  walter_split : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (_hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G) (_hP : IsMulCommutative (P : Subgroup G)),
    (∃ f : ℕ, 2 ≤ f ∧ Nonempty (G ≃* PSL(2, GaloisField 2 f))) ∨
    (∃ p f : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
        (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nonempty (G ≃* PSL(2, GaloisField p f))) ∨
    (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ Blueprint.ReeTitsModel G .twistedG2 3 f) ∨
    Nonempty (G ≃* Open.walterJ1)

end CFSGOutside.Corpus
