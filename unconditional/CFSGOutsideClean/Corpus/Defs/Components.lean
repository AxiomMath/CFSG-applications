import CFSG.Foundations.Basic
import CFSG.GroupTheory.LocalCores.Layer
import CFSGOutside.Corpus.Defs.Components

/-! The definitions copied into `CFSGOutside.Corpus.Defs.Components` are the corpus definitions. -/

universe u

namespace CFSGOutsideClean.Corpus

theorem isQuasisimple_iff (Q : Type*) [Group Q] :
    CFSGOutside.Corpus.IsQuasisimple Q ↔ CFSG.IsQuasisimple Q :=
  Iff.rfl

theorem isComponent_iff {G : Type*} [Group G] (K : Subgroup G) :
    CFSGOutside.Corpus.IsComponent K ↔ CFSG.IsComponent K :=
  Iff.rfl

theorem layer_eq (G : Type*) [Group G] : CFSGOutside.Corpus.layer G = CFSG.layer G :=
  rfl

theorem solvableRadical_eq (G : Type*) [Group G] :
    CFSGOutside.Corpus.solvableRadical G = CFSG.solvableRadical G :=
  rfl

theorem componentIndex_eq (G : Type*) [Group G] :
    CFSGOutside.Corpus.LocalCores.ComponentIndex G = CFSG.LocalCores.ComponentIndex G :=
  rfl

theorem layerMul_eq (G : Type u) [Group G] [Finite G] :
    CFSGOutside.Corpus.LocalCores.layerMul G = CFSG.LocalCores.layerMul G :=
  rfl

end CFSGOutsideClean.Corpus
