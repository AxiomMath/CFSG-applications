import Mathlib
import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

/-!
# Serre (2013), Théorème 5: the sets `Σ_ℓ`

J.-P. Serre, *Un critère d'indépendance pour une famille de représentations ℓ-adiques*,
Comment. Math. Helv. 88 (2013), 541-554 (arXiv 1006.2442), §6.1 and §6.4.

For a prime `ℓ ≥ 5`, `Σ_ℓ` is the set of (isomorphism classes of) finite simple groups of Lie type in
characteristic `ℓ`, together with the cyclic group `ℤ/ℓℤ` (§6.1). The simple groups of Lie type are taken
from the TauCeti catalogue (`TauCeti.CFSGIndex.lie`), with characteristic
`TauCeti.LieTypeIndex.characteristic`. The catalogue lists each simple group once, so a group that has two
names in Lie type appears under one of them only; `DuplicateLie` adds back the names the catalogue omits.
-/

namespace CFSGOutside.Serre

/-- The six Lie-type indices that the TauCeti catalogue omits as duplicate representatives
(`TauCeti.LieTypeIndex.IsDuplicateRepresentative`) are `A₁(4)`, `A₁(5)`, `A₁(9)`, `A₂(2)`, `A₃(2)` and
`B₂(3)`. The first five are the groups `PSL_{n+1}(𝔽_q)`, for which Mathlib has the group itself; `B₂(3)` is
`PSp₄(3) ≅ PSU₄(2)`, modelled by the catalogue group of `²A₃(2)`.

`DuplicateLie ℓ G`: `G` is isomorphic to the group attached to an omitted index of characteristic `ℓ`.
These groups are among the groups of Lie type of Serre (2013), §6.1. -/
def DuplicateLie (ℓ : ℕ) (G : Type) [Group G] : Prop :=
  (∃ (n : ℕ) (q : TauCeti.PrimePower) (k : Type) (_ : Field k) (_ : Finite k),
      (TauCeti.LieTypeIndex.A n q).InStandardRange ∧
      (TauCeti.LieTypeIndex.A n q).IsDuplicateRepresentative ∧ q.p = ℓ ∧
      Nat.card k = q.card ∧
      Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin (n + 1)) k)) ∨
  (ℓ = 3 ∧ ∃ h : (TauCeti.LieTypeIndex.twistedA 3
      ⟨2, 1, Nat.prime_two, Nat.one_pos⟩).Valid,
    Nonempty (G ≃* (TauCeti.CFSGIndex.lie
      ⟨TauCeti.LieTypeIndex.twistedA 3 ⟨2, 1, Nat.prime_two, Nat.one_pos⟩, h⟩).Group))

/-- `G ∈ Σ_ℓ` (Serre (2013), §6.1): `G` is isomorphic to a finite simple group of Lie type in
characteristic `ℓ` (every group `H_F`, duplicates included), or to the cyclic group `ℤ/ℓℤ`.
The groups of Lie type are those of the TauCeti catalogue (`TauCeti.CFSGIndex.lie idx` with
`idx.characteristic = ℓ`), together with the groups the catalogue lists under another name
(`DuplicateLie`). -/
def InSigma (ℓ : ℕ) (G : Type) [Group G] : Prop :=
  (∃ idx : TauCeti.ValidLieTypeIndex, idx.1.characteristic = ℓ ∧
    Nonempty (G ≃* (TauCeti.CFSGIndex.lie idx).Group)) ∨
  DuplicateLie ℓ G ∨
  Nonempty (G ≃* Multiplicative (ZMod ℓ))

end CFSGOutside.Serre
