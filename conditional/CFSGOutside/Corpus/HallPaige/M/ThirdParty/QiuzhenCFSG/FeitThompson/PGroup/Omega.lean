import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Module.ZMod
import Mathlib.Basic.Logic.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Sylow
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.Basic
import CFSGOutside.Corpus.HallPaige.M.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

/-!
# Copied corpus declarations from `CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/PGroup/Omega.lean`

Declarations copied verbatim from AxiomMath/CFSG @ 69cb972 by a script, with
`CFSG.*` renamed to `CFSGOutside.Corpus.M.*` (the definitional closure of the statements of the
classes in `Corpus/HallPaige/M.lean`, with the corpus proofs of the theorems these definitions
use). The imports are the module's own transitive non-corpus imports and the copies of its
corpus imports, so every proof elaborates in the corpus's environment.
-/

/-! ### `CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/PGroup/Omega.lean` -/

namespace CFSGOutside.Corpus.M
end CFSGOutside.Corpus.M
open CFSGOutside.Corpus.M

open scoped IsMulCommutative

/-- The Omega subgroup. -/

def CFSGOutside.Corpus.M.omega (G : Type*) [Group G] {p : ℕ} (k : ℕ) : Subgroup G :=
  Subgroup.closure {x : G | x ^ (p ^ k) = 1}
