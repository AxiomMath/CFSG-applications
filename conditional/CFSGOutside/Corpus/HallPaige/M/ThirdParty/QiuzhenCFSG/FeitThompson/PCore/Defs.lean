import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Set.Lattice
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Copied corpus declarations from `CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/PCore/Defs.lean`

Declarations copied verbatim from AxiomMath/CFSG @ 69cb972 by a script, with
`CFSG.*` renamed to `CFSGOutside.Corpus.M.*` (the definitional closure of the statements of the
classes in `Corpus/HallPaige/M.lean`, with the corpus proofs of the theorems these definitions
use). The imports are the module's own transitive non-corpus imports and the copies of its
corpus imports, so every proof elaborates in the corpus's environment.
-/

/-! ### `CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/PCore/Defs.lean` -/

namespace CFSGOutside.Corpus.M
end CFSGOutside.Corpus.M
open CFSGOutside.Corpus.M

open scoped Pointwise

variable (p : ℕ) (G : Type*) [Group G]

/-- The set of normal `p`-subgroups of `G`. -/

def CFSGOutside.Corpus.M.normalPSubgroups : Set (Subgroup G) :=
  {K : Subgroup G | K.Normal ∧ IsPGroup p K}

/-- The `p`-core of `G`: the supremum of all normal `p`-subgroups. -/

def CFSGOutside.Corpus.M.pCore : Subgroup G :=
  sSup {K : Subgroup G | K.Normal ∧ IsPGroup p K}
