import Mathlib
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Set.Lattice
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.Subgroup.Simple
import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
import CFSGOutside.Corpus.HallPaige.M.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs
import CFSGOutside.Corpus.HallPaige.M.Foundations.MaxCardThompson

/-!
# Copied corpus declarations from `CFSG/Open/MonsterDefs.lean`

Declarations copied verbatim from AxiomMath/CFSG @ 69cb972 by a script, with
`CFSG.*` renamed to `CFSGOutside.Corpus.M.*` (the definitional closure of the statements of the
classes in `Corpus/HallPaige/M.lean`, with the corpus proofs of the theorems these definitions
use). The imports are the module's own transitive non-corpus imports and the copies of its
corpus imports, so every proof elaborates in the corpus's environment.
-/

/-! ### `CFSG/Open/MonsterDefs.lean` -/

section

namespace CFSGOutside.Corpus.M.Open
open Matrix

/-- Corpus: `CFSG.Open.monsterOrder`, CFSG/Open/MonsterDefs.lean:10. -/
def monsterOrder : ℕ :=
  2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71

/-- Corpus: `CFSG.Open.monsterBabyOrder`, CFSG/Open/MonsterDefs.lean:13. -/
def monsterBabyOrder : ℕ := 2 ^ 41 * 3 ^ 13 * 5 ^ 6 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 31 * 47

end CFSGOutside.Corpus.M.Open
