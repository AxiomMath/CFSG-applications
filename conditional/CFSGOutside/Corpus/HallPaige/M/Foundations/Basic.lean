import Lean.Elab.Term
import Lean.Meta.Tactic.Delta
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Action.Faithful
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Notation.Defs
import Mathlib.Basic.Logic.Basic
import Mathlib.Data.Bracket
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Set.Lattice
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.IsSubnormal
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Transfer
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Order.Atoms.Finite
import Mathlib.Order.RelSeries
import Mathlib.Order.SetNotation
import Mathlib.RepresentationTheory.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Eqns
import Mathlib.Tactic.TypeStar
import CFSGOutside.Corpus.HallPaige.M.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs
import CFSGOutside.Corpus.HallPaige.M.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSGOutside.Corpus.HallPaige.M.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Core
import CFSGOutside.Corpus.HallPaige.M.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSGOutside.Corpus.HallPaige.M.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.Omega

/-!
# Copied corpus declarations from `CFSG/Foundations/Basic.lean`

Declarations copied verbatim from AxiomMath/CFSG @ 69cb972 by a script, with
`CFSG.*` renamed to `CFSGOutside.Corpus.M.*` (the definitional closure of the statements of the
classes in `Corpus/HallPaige/M.lean`, with the corpus proofs of the theorems these definitions
use). The imports are the module's own transitive non-corpus imports and the copies of its
corpus imports, so every proof elaborates in the corpus's environment.
-/

/-! ### `CFSG/Foundations/Basic.lean` -/

section

namespace CFSGOutside.Corpus.M

open Subgroup

universe u

variable {G : Type*} [Group G]

/-- Corpus: `CFSG.inSubgroup`, CFSG/Foundations/Basic.lean:27. -/
def inSubgroup {G : Type u} [Group G] (F : ∀ (K : Type u) [Group K], Subgroup K)
    (H : Subgroup G) : Subgroup G :=
  (F H).map H.subtype

/-- Corpus: `CFSG.IsExtraspecialPGroup`, CFSG/Foundations/Basic.lean:132. -/
def IsExtraspecialPGroup (p : ℕ) (P : Type*) [Group P] : Prop :=
  IsPGroup p P ∧ commutator P = center P ∧ frattini P = center P ∧ Nat.card (center P) = p

section Cores

variable (G)

end Cores

end CFSGOutside.Corpus.M
