import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
import CFSG.LocalAnalysis.StandardType.GGSecFiveCoxProd
import CFSGOutside.Corpus.Defs.GGWeylInputs
import CFSGOutsideClean.Corpus.Defs.ZSReflectionGroups

/-! The definitions copied into `CFSGOutside.Corpus.Defs.GGWeylInputs` are the corpus definitions. -/

namespace CFSGOutsideClean.Corpus.StandardType

theorem ggInduced_eq {G : Type} [Group G] [Finite G] (H Bs : Subgroup G) :
    CFSGOutside.Corpus.StandardType.ggInduced H Bs = CFSG.StandardType.ggInduced H Bs :=
  rfl

theorem ggIsReflection_iff {G : Type} [Group G] [Finite G] (p : ℕ) {Bs : Subgroup G}
    (φ : MulAut ↥Bs) :
    CFSGOutside.Corpus.StandardType.GGIsReflection p φ ↔ CFSG.StandardType.GGIsReflection p φ :=
  Iff.rfl

theorem ggIsTransvection_iff {G : Type} [Group G] [Finite G] (p : ℕ) {Bs : Subgroup G}
    (φ : MulAut ↥Bs) :
    CFSGOutside.Corpus.StandardType.GGIsTransvection p φ ↔
      CFSG.StandardType.GGIsTransvection p φ :=
  Iff.rfl

theorem ggNoTransvection_iff {G : Type} [Group G] [Finite G] (p : ℕ) (Bs : Subgroup G) :
    CFSGOutside.Corpus.StandardType.GGNoTransvection p Bs ↔
      CFSG.StandardType.GGNoTransvection p Bs :=
  Iff.rfl

theorem ggSecFiveRootReflInput_iff :
    CFSGOutside.Corpus.StandardType.GGSecFiveRootReflInput ↔
      CFSG.StandardType.GGSecFiveRootReflInput :=
  Iff.rfl

theorem ggSecFiveCoxProdInput_iff :
    CFSGOutside.Corpus.StandardType.GGSecFiveCoxProdInput ↔
      CFSG.StandardType.GGSecFiveCoxProdInput :=
  Iff.rfl

end CFSGOutsideClean.Corpus.StandardType
