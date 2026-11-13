import CFSGOutside.Corpus.Defs.ClassicalModel
import CFSGOutside.Corpus.Defs.TwoRank
import CFSGOutside.Corpus.Defs.StatedM11

/-!
# Corpus input: the finite simple groups of 2-rank two (Alperin–Brauer–Gorenstein, second main theorem)

Statement of `CFSG.Milestones.lr_rank_two_isomorphism_types`, copied verbatim from
`CFSG/Milestones/LR_rank_two_isomorphism_types.lean` (line 13) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962. `twoRank`, `StatedClassicalModel` and `StatedM11` are the copies in
`CFSGOutside.Corpus.Defs`.

A nonabelian finite simple group of 2-rank two is `PSL(2,q)`, `PSL(3,q)` or `PSU(3,q)` with `q` odd, `PSU(3,4)`, `A₇`
or `M₁₁`.
-/

namespace CFSGOutside.Corpus

open Open

/-- The finite simple groups of 2-rank two, as `CFSG.Milestones.lr_rank_two_isomorphism_types` states it. -/
class LrRankTwoIsomorphismTypes : Prop where
  lr_rank_two_isomorphism_types : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (_hnonab : ∃ a b : G, a * b ≠ b * a) (_hrank : twoRank G = 2),
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSL 2 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSL 3 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSU 3 p f) ∨
    StatedClassicalModel G .PSU 3 2 2 ∨
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (G ≃* StatedM11)

end CFSGOutside.Corpus
