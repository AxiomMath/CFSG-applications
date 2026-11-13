import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Set.Lattice
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.QuotientGroup.Basic
import CFSGOutside.Corpus.HallPaige.M.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs

/-!
# Copied corpus declarations from `CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/PCore/PCore.lean`

Declarations copied verbatim from AxiomMath/CFSG @ 69cb972 by a script, with
`CFSG.*` renamed to `CFSGOutside.Corpus.M.*` (the definitional closure of the statements of the
classes in `Corpus/HallPaige/M.lean`, with the corpus proofs of the theorems these definitions
use). The imports are the module's own transitive non-corpus imports and the copies of its
corpus imports, so every proof elaborates in the corpus's environment.
-/

/-! ### `CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/PCore/PCore.lean` -/

namespace CFSGOutside.Corpus.M
end CFSGOutside.Corpus.M
open CFSGOutside.Corpus.M

open scoped commutatorElement

variable (p : ℕ) (G : Type*) [Group G]

section pCore_properties

-- Lemmas from pCore.lean

/-- Corpus: `CFSG.normalPSubgroups_nonempty`, CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/PCore/PCore.lean:17. -/
lemma CFSGOutside.Corpus.M.normalPSubgroups_nonempty : (normalPSubgroups p G).Nonempty :=
    ⟨⊥, ⟨inferInstance, IsPGroup.of_bot⟩⟩

/-- Corpus: `CFSG.directedOn_normal_pGroups`, CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/PCore/PCore.lean:20. -/
lemma CFSGOutside.Corpus.M.directedOn_normal_pGroups :
    DirectedOn (· ≤ ·) (normalPSubgroups p G) := by
  intro A hA B hB
  have hA_normal := hA.1
  have hB_normal := hB.1
  have hA_p := hA.2
  have hB_p := hB.2
  refine ⟨A ⊔ B, ⟨?_, ?_⟩, le_sup_left, le_sup_right⟩
  · exact Subgroup.sup_normal A B
  · exact IsPGroup.to_sup_of_normal_right hA.2 hB.2

variable {G} {p}

/-- `p`-core of `G` is normal. -/
@[instance]
theorem CFSGOutside.Corpus.M.pCore_normal : (pCore p G).Normal := by
  refine ⟨?_⟩
  intro n hn g
  have hdir := directedOn_normal_pGroups p G
  have hne := normalPSubgroups_nonempty p G
  rcases ((Subgroup.mem_sSup_of_directedOn hne hdir).mp hn) with ⟨K, hK, hnK⟩
  exact Subgroup.mem_sSup_of_mem hK (hK.1.conj_mem n hnK g)

variable [Fact p.Prime]

variable [Finite G]

end pCore_properties
