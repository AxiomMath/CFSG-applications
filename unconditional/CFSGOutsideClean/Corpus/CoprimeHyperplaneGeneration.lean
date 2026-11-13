import CFSG.GroupTheory.HyperplaneGeneration
import CFSGOutside.Corpus.CoprimeHyperplaneGeneration
import CFSGOutsideClean.Corpus.Defs.ElementaryAbelian
import CFSGOutsideClean.Corpus.Defs.Frobenius

/-! The corpus proves the statement that `CFSGOutside.Corpus.CoprimeHyperplaneGeneration` assumes. The copied
`fixedPointSubgroup` is the corpus definition by `rfl` (`CFSGOutsideClean.Corpus.fixedPointSubgroup_eq`). -/

universe u v

instance CFSGOutsideClean.Corpus.coprimeHyperplaneGeneration :
    CFSGOutside.Corpus.CoprimeHyperplaneGeneration.{u, v} :=
  ⟨fun {p} _ {A} _ _ inst _ {_} _ _ _ hp =>
    haveI := (CFSGOutsideClean.Corpus.isElementaryAbelian_iff p A).1 inst
    CFSG.SolvableHall.coprime_hyperplane_generation (A := A) hp⟩
