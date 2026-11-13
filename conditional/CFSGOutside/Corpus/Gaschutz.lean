import Mathlib

/-!
# Corpus input: Gaschütz's theorem

Statement of `CFSG.Quasithin.gaschutz`, copied verbatim from `CFSG/Quasithin/Background/A1cTransfer.lean`
(line 349, with the section variables of line 14) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962.

An abelian normal `p`-subgroup `V` of a finite group `G` has a complement in `G` if and only if it has a
complement in a Sylow `p`-subgroup. The corpus theorem is universe polymorphic, so the class takes the
universe of `G` as a parameter. The clean build provides every instance, in
`clean/CFSGOutsideClean/Corpus/Gaschutz.lean`.
-/

namespace CFSGOutside.Corpus

/-- Gaschütz's theorem, as `CFSG.Quasithin.gaschutz` states it. -/
class Gaschutz.{u} : Prop where
  gaschutz : ∀ {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {V : Subgroup G} [V.Normal]
    [IsMulCommutative V] (_hVp : IsPGroup p V) (P : Sylow p G),
    (∃ K : Subgroup G, V ⊓ K = ⊥ ∧ V ⊔ K = ⊤) ↔
      ∃ K : Subgroup G, K ≤ P ∧ V ⊓ K = ⊥ ∧ V ⊔ K = P

end CFSGOutside.Corpus
