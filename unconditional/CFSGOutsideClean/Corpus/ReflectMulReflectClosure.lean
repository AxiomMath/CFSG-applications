import CFSG.ClassicalGroups.Orthogonal.NormClass.Generation
import CFSGOutside.Corpus.ReflectMulReflectClosure

/-! The corpus proves the statement that `CFSGOutside.Corpus.ReflectMulReflectClosure` assumes. -/

/-- The copy `CFSGOutside.Corpus.ClassicalGroups.Orthogonal.reflect` is the corpus `reflect`. -/
theorem CFSGOutsideClean.Corpus.ClassicalGroups.Orthogonal.reflect_eq {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) (v : V) :
    CFSGOutside.Corpus.ClassicalGroups.Orthogonal.reflect Q v =
      CFSG.ClassicalGroups.Orthogonal.reflect Q v :=
  rfl

instance CFSGOutsideClean.Corpus.reflectMulReflectClosure :
    CFSGOutside.Corpus.ReflectMulReflectClosure :=
  ⟨by
    intro _ _ _ _ _ _ _ _ h2 h3 hQ _ _ hab _ hc
    exact CFSG.ClassicalGroups.Orthogonal.reflect_mul_reflect_mem_closure_reflect h2 h3 hQ hab hc⟩
