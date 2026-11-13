import CFSGOutside.Corpus.Defs.Frobenius

/-!
# Corpus input: generation by centralizers of subgroups with cyclic quotient

Statement of `CFSG.proposition_1_16_b`, copied verbatim from
`CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/BGsection1/proposition_1_16.lean` (line 28) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962. `fixedPointSubgroup` is the copy in `CFSGOutside.Corpus.Defs`.

Gorenstein, Proposition 1.16(b): a noncyclic abelian `p`-group `A` acting on a finite group `G` of order prime
to `p` has `G = ⟨C_G(Y) | A/Y cyclic⟩`. The corpus theorem is universe polymorphic, so the class takes the
universes of `G` and of `A` as parameters. The clean build provides every instance, in
`clean/CFSGOutsideClean/Corpus/Proposition116B.lean`.
-/

namespace CFSGOutside.Corpus

/-- Generation of `G` by the centralizers of the subgroups `Y ≤ A` with `A/Y` cyclic, as
`CFSG.proposition_1_16_b` states it. -/
class Proposition116B.{u, v} : Prop where
  proposition_1_16_b : ∀ {G : Type u} {A : Type v} [Group G] [Finite G] [CommGroup A] [Finite A] (p : ℕ)
    [Fact p.Prime] (_hG : Nat.Coprime p (Nat.card G)) [Fact (IsPGroup p A)] [MulDistribMulAction A G]
    (_hncyc : ¬ IsCyclic A),
    (⨆ (Y : Subgroup A) (_ : IsCyclic (A ⧸ Y)), fixedPointSubgroup (↥Y) G) = ⊤

end CFSGOutside.Corpus
