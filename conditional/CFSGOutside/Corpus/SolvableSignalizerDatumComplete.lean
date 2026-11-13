import CFSGOutside.Corpus.Defs.SolvableSignalizerDatum

/-!
# Corpus input: Glauberman's solvable signalizer functor theorem

Statement of `CFSG.RankThree.Theta.solvable_signalizer_datum_complete`, copied verbatim from
`CFSG/RankThree/Theta/SignalizerCompleteness.lean` (line 116) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962. `IsSolvableSignalizerDatum` is the copy in
`CFSGOutside.Corpus.Defs.SolvableSignalizerDatum`.

For an elementary abelian `p`-group `A` of order at least `p ^ 3` and a solvable `A`-signalizer functor `θ`
on a finite group, the join of the `θ a`, `a ∈ A#`, is an `A`-invariant solvable `p'`-subgroup whose
`a`-fixed points lie in `θ a`. The corpus theorem is universe polymorphic, so the class takes the universes
of `A` and of the group as parameters. The clean build provides every instance, in
`clean/CFSGOutsideClean/Corpus/SolvableSignalizerDatumComplete.lean`.
-/

universe u v

namespace CFSGOutside.Corpus

/-- Glauberman's solvable signalizer functor theorem, as
`CFSG.RankThree.Theta.solvable_signalizer_datum_complete` states it. -/
class SolvableSignalizerDatumComplete.{u₁, v₁} : Prop where
  solvable_signalizer_datum_complete : ∀ {p : ℕ} {A : Type u₁} [Group A] {X : Type v₁} [Group X]
    {α : A →* MulAut X} {θ : A → Subgroup X}
    (_hd : GroupTheory.SteinbergBS.IsSolvableSignalizerDatum p A X α θ)
    (_h3 : p ^ 3 ≤ Nat.card A),
    let Θ : Subgroup X := ⨆ (a : A) (_ : a ≠ 1), θ a
    (∀ b : A, Θ.map (α b).toMonoidHom = Θ) ∧ Group.IsSolvable Θ ∧ Nat.Coprime p (Nat.card Θ) ∧
      ∀ a : A, a ≠ 1 → ∀ g ∈ Θ, α a g = g → g ∈ θ a

end CFSGOutside.Corpus
