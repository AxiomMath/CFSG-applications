import CFSG.Foundations.Basic
import CFSGOutside.Corpus.Defs.Conjugate

/-! The definition copied into `CFSGOutside.Corpus.Defs.Conjugate` is the corpus definition. -/

theorem CFSGOutsideClean.Corpus.conjugate_eq {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    CFSGOutside.Corpus.conjugate H g = CFSG.conjugate H g :=
  rfl
