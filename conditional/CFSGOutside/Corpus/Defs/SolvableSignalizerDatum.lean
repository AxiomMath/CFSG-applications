import CFSGOutside.Corpus.Defs.ElementaryAbelian

/-!
# Copied corpus definition: solvable signalizer data

Copied verbatim from AxiomMath/CFSG at commit 69cb972f587a3ecc035e092253167ff2e303c962, under
`CFSGOutside.Corpus`, with `IsElementaryAbelian` the copy in `CFSGOutside.Corpus.Defs.ElementaryAbelian`.
The clean build proves it equivalent to the corpus original in
`clean/CFSGOutsideClean/Corpus/Defs/SolvableSignalizerDatum.lean`.
-/

namespace CFSGOutside.Corpus.GroupTheory.SteinbergBS

/-- A solvable `A`-signalizer functor datum. Copy of
`CFSG.GroupTheory.SteinbergBS.IsSolvableSignalizerDatum`,
`CFSG/GroupTheory/SteinbergBSSolvableSignalizer.lean` line 10. -/
structure IsSolvableSignalizerDatum (p : ℕ) (A : Type*) [Group A] (G : Type*) [Group G]
    (α : A →* MulAut G) (θ : A → Subgroup G) : Prop where
  prime : p.Prime
  finite_actor : Finite A
  elementary : IsElementaryAbelian p A
  card_actor : p ^ 2 ≤ Nat.card A
  finite : Finite G
  invariant : ∀ a : A, a ≠ 1 → ∀ b : A, (θ a).map (α b).toMonoidHom = θ a
  solvable : ∀ a : A, a ≠ 1 → Group.IsSolvable (θ a)
  coprime : ∀ a : A, a ≠ 1 → Nat.Coprime p (Nat.card (θ a))
  le_fixed : ∀ a : A, a ≠ 1 → ∀ g ∈ θ a, α a g = g
  balance : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∀ g ∈ θ a, α b g = g → g ∈ θ b

end CFSGOutside.Corpus.GroupTheory.SteinbergBS
