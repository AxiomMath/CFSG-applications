import Mathlib
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

/-!
# Corpus input: a product of two reflections of equal norm in the group of norm-`c` reflections

Statement of `CFSG.ClassicalGroups.Orthogonal.reflect_mul_reflect_mem_closure_reflect`
(`CFSG/ClassicalGroups/Orthogonal/NormClass/Generation.lean`, line 141, at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962), with the section variables
`{K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}` (line 15) bound. `reflect` is the
copy of `CFSG.ClassicalGroups.Orthogonal.reflect` (`CFSG/ClassicalGroups/Orthogonal/Derived.lean`, line 18).
-/

namespace CFSGOutside.Corpus.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable (Q : QuadraticForm K V) in
/-- Copy of `CFSG.ClassicalGroups.Orthogonal.reflect`: the reflection in `v`, or `1` if `Q v = 0`. -/
noncomputable def reflect (v : V) : V ≃ₗ[K] V :=
  open scoped Classical in
  if h : Q v ≠ 0 then
    @TauCeti.QuadraticMap.reflection K V _ _ _ Q v (invertibleOfNonzero h)
  else 1

end CFSGOutside.Corpus.ClassicalGroups.Orthogonal

namespace CFSGOutside.Corpus

open QuadraticMap ClassicalGroups.Orthogonal in
/-- `reflect_mul_reflect_mem_closure_reflect`, as the corpus states it. -/
class ReflectMulReflectClosure : Prop where
  reflect_mul_reflect_mem_closure_reflect : ∀ {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} [Finite K] [FiniteDimensional K V]
    (_h2 : (2 : K) ≠ 0) (_h3 : (3 : K) ≠ 0) (_hQ : (polarBilin Q).Nondegenerate) {a b : V}
    (_hab : Q a = Q b) {c : K} (_hc : c ≠ 0),
    reflect Q a * reflect Q b ∈ Subgroup.closure (reflect Q '' {x | Q x = c})

end CFSGOutside.Corpus
