import CFSG.ClassicalGroups.McLaughlin.Basic
import CFSGOutside.Corpus.Defs.McLaughlin

/-! The definitions copied into `CFSGOutside.Corpus.Defs.McLaughlin` are the corpus definitions. -/

namespace CFSGOutsideClean.Corpus.ClassicalGroups.McLaughlin

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem isRootElt_iff (X : Subgroup (LinearMap.GeneralLinearGroup K V)) (v : V)
    (φ : Module.Dual K V) :
    CFSGOutside.Corpus.ClassicalGroups.McLaughlin.IsRootElt X v φ ↔
      CFSG.ClassicalGroups.McLaughlin.IsRootElt X v φ :=
  Iff.rfl

theorem genByRoots_iff (X : Subgroup (LinearMap.GeneralLinearGroup K V)) :
    CFSGOutside.Corpus.ClassicalGroups.McLaughlin.GenByRoots X ↔
      CFSG.ClassicalGroups.McLaughlin.GenByRoots X :=
  Iff.rfl

theorem irred_iff (X : Subgroup (LinearMap.GeneralLinearGroup K V)) :
    CFSGOutside.Corpus.ClassicalGroups.McLaughlin.Irred X ↔
      CFSG.ClassicalGroups.McLaughlin.Irred X :=
  Iff.rfl

theorem isCentre_iff (X : Subgroup (LinearMap.GeneralLinearGroup K V)) (v : V) :
    CFSGOutside.Corpus.ClassicalGroups.McLaughlin.IsCentre X v ↔
      CFSG.ClassicalGroups.McLaughlin.IsCentre X v :=
  Iff.rfl

end CFSGOutsideClean.Corpus.ClassicalGroups.McLaughlin
