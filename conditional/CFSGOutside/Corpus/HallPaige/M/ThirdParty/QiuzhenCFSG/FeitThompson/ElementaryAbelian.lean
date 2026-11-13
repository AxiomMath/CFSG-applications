import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Module.ZMod
import Mathlib.Basic.Logic.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.Basic

/-!
# Copied corpus declarations from `CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/ElementaryAbelian.lean`

Declarations copied verbatim from AxiomMath/CFSG @ 69cb972 by a script, with
`CFSG.*` renamed to `CFSGOutside.Corpus.M.*` (the definitional closure of the statements of the
classes in `Corpus/HallPaige/M.lean`, with the corpus proofs of the theorems these definitions
use). The imports are the module's own transitive non-corpus imports and the copies of its
corpus imports, so every proof elaborates in the corpus's environment.
-/

/-! ### `CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/ElementaryAbelian.lean` -/

namespace CFSGOutside.Corpus.M
end CFSGOutside.Corpus.M
open CFSGOutside.Corpus.M

open scoped IsMulCommutative

universe u

/-- An *elementary abelian* `p`-group: a commutative group whose exponent divides `p`. -/
class CFSGOutside.Corpus.M.IsElementaryAbelian (p : ℕ) (G : Type u) [Group G] : Prop
    extends IsMulCommutative G where
  exponent_dvd_p (p) (G) : Monoid.exponent G ∣ p

/-- Corpus: `CFSG.IsElementaryAbelian.isVectorSpace`, CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/ElementaryAbelian.lean:52. -/
instance CFSGOutside.Corpus.M.IsElementaryAbelian.isVectorSpace (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [inst : IsElementaryAbelian p G] :
    Module (ZMod p) (Additive G) :=
  have hpow : ∀ g : G, g ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp inst.exponent_dvd_p
  have hsmul : ∀ x : Additive G, p • x = 0 := fun x =>
    toMul_eq_one.mp (hpow x)
  AddCommMonoid.zmodModule (M := Additive G) (n := p) hsmul

/-- A subgroup of an elementary abelian group, restricted to a larger subgroup, is still elementary
abelian. -/
theorem CFSGOutside.Corpus.M.IsElementaryAbelian.subgroupOf {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    {H K : Subgroup G} [IsElementaryAbelian p H] (_hHK : H ≤ K) :
    IsElementaryAbelian p (H.subgroupOf K) := by
  refine
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  apply Subtype.ext
  let xH : H := ⟨((x : H.subgroupOf K) : K), Subgroup.mem_subgroupOf.mp x.2⟩
  have hxpow : xH ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p H) xH
  simpa [xH] using congrArg (fun y : H => ((y : H) : G)) hxpow

/-- The image of an elementary abelian subgroup under a homomorphism is elementary abelian. -/
theorem CFSGOutside.Corpus.M.IsElementaryAbelian.map
    {p : ℕ} [Fact p.Prime] {R S : Type*} [Group R] [Group S]
    {A : Subgroup R} [IsElementaryAbelian p A] (f : R →* S) :
    IsElementaryAbelian p (A.map f) := by
  refine
    { toIsMulCommutative := by
        simpa using (Subgroup.map_isMulCommutative (f := f) (H := A))
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  rcases Subgroup.mem_map.mp x.2 with ⟨y, hyA, hyx⟩
  let yA : A := ⟨y, hyA⟩
  have hypow : yA ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p A) yA
  have hx_eq : (x : S) = f y := by simpa using hyx.symm
  calc
    (x : S) ^ p = (f y) ^ p := by simp [hx_eq]
    _ = f (y ^ p) := by simp
    _ = 1 := by simpa using congrArg f (congrArg Subtype.val hypow)
