import Mathlib
import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

/-!
# Copied corpus definitions: elementary abelian subgroups, `p`-rank and the catalogue

Definitions copied verbatim from AxiomMath/CFSG at commit 69cb972f587a3ecc035e092253167ff2e303c962, under
`CFSGOutside.Corpus` so that `clean/`, which imports the corpus too, sees no clash. The clean build proves
each copy equal to its corpus original in `clean/CFSGOutsideClean/Corpus/Defs/OpenVocabulary.lean`.

These are the `CFSG.Open` versions (`IsElemAbelian`, `pRank` for a subgroup), distinct from `CFSG.pRank` and
`CFSG.IsElementaryAbelian`, which `ElemThompson` and `ElementaryAbelian` copy.
-/

namespace CFSGOutside.Corpus

namespace Open

/-- `E` is an elementary abelian `p`-subgroup: commutative of exponent dividing `p`. Copy of
`CFSG.Open.IsElemAbelian`, `CFSG/Open/LocalVocabulary.lean` line 12. -/
def IsElemAbelian (p : ℕ) {G : Type*} [Group G] (E : Subgroup G) : Prop :=
  IsMulCommutative E ∧ ∀ x ∈ E, x ^ p = 1

/-- The `p`-rank of a subgroup `H`: the largest `k` such that `H` has an elementary abelian `p`-subgroup of
order `p ^ k`. Copy of `CFSG.Open.pRank`, `CFSG/Open/LocalVocabulary.lean` line 15. -/
noncomputable def pRank (p : ℕ) {G : Type*} [Group G] [Finite G] (H : Subgroup G) : ℕ :=
  sSup {k | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k}

/-- `H` is isomorphic to a group of TauCeti's catalogue of finite simple groups. Copy of
`CFSG.Open.IsCatalogGroup`, `CFSG/Open/Defs.lean` line 96. -/
def IsCatalogGroup (H : Type*) [Group H] : Prop :=
  ∃ i : TauCeti.CFSGIndex, Nonempty (H ≃* i.Group)

end Open

/-- For an odd prime `p` not dividing the order of a nonabelian simple catalogue group `K`, the `p`-rank of
`Aut K` is at most one. Copy of `CFSG.HardMathSupport.Solomon.Coordinator.I_7_13_1_pPrime`,
`CFSG/HardMathSupport/Solomon/Coordinator/Generation228.lean` line 16. -/
def I_7_13_1_pPrime : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → Open.IsCatalogGroup K → ¬ p ∣ Nat.card K →
      Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 1

end CFSGOutside.Corpus
