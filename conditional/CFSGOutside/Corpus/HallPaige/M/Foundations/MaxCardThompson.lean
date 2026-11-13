import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Copied corpus declarations from `CFSG/Foundations/MaxCardThompson.lean`

Declarations copied verbatim from AxiomMath/CFSG @ 69cb972 by a script, with
`CFSG.*` renamed to `CFSGOutside.Corpus.M.*` (the definitional closure of the statements of the
classes in `Corpus/HallPaige/M.lean`, with the corpus proofs of the theorems these definitions
use). The imports are the module's own transitive non-corpus imports and the copies of its
corpus imports, so every proof elaborates in the corpus's environment.
-/

/-! ### `CFSG/Foundations/MaxCardThompson.lean` -/

section

namespace CFSGOutside.Corpus.M

open Subgroup

universe u v

section General

variable {G : Type u} [Group G]

/-- Corpus: `CFSG.IsMaxCardAbelian`, CFSG/Foundations/MaxCardThompson.lean:30. -/
def IsMaxCardAbelian (A : Subgroup G) : Prop :=
  IsMulCommutative A ∧ ∀ B : Subgroup G, IsMulCommutative B → Nat.card B ≤ Nat.card A

/-- Corpus: `CFSG.IsMaxCardAbelian.subgroupOf`, CFSG/Foundations/MaxCardThompson.lean:55. -/
theorem IsMaxCardAbelian.subgroupOf {A H : Subgroup G} (hA : IsMaxCardAbelian A) (hAH : A ≤ H) :
    IsMaxCardAbelian (A.subgroupOf H) := by
  have : IsMulCommutative A := hA.1
  refine ⟨inferInstance, fun B hB => ?_⟩
  have : IsMulCommutative B := hB
  have bound := hA.2 (B.map H.subtype) inferInstance
  rw [card_map_of_injective H.subtype_injective] at bound
  rwa [Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv]

section MulEquiv

variable {H : Type v} [Group H]

end MulEquiv

section Injective

variable {H : Type v} [Group H]

end Injective

end General

end CFSGOutside.Corpus.M
