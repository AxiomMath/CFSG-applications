import CFSG.LocalAnalysis.ComponentClassification.WittDesignWittAut
import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Transitive
import CFSG.Sporadic.Mathieu.M22
import CFSGOutside.Corpus.Defs.WittDesign

/-!
# The copied `S(3,6,22)`, hexad and `M22` definitions are the corpus ones

`CFSGOutside.Corpus.Defs.WittDesign` copies `M22`, `IsSteinerTriple`, `hexadList`, `hexads`, `blockAut` and `hexadAut`.
Each copy is the corpus definition by `rfl`.
-/

namespace CFSGOutsideClean.Corpus.WittDesign

theorem nativeM22_eq :
    CFSGOutside.Corpus.NativeSporadic.M22 = CFSG.Blueprint.NativeSporadic.M22 :=
  rfl

theorem m22_eq :
    CFSGOutside.Corpus.WittDesign.M22 = CFSG.ComponentClassification.WittDesign.M22 :=
  rfl

theorem isSteinerTriple_iff {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (𝓑 : Finset (Finset Ω)) :
    CFSGOutside.Corpus.WittDesign.IsSteinerTriple 𝓑 ↔
      CFSG.ComponentClassification.WittDesign.IsSteinerTriple 𝓑 :=
  Iff.rfl

theorem hexadList_eq :
    CFSGOutside.Corpus.WittDesign.hexadList = CFSG.ComponentClassification.WittDesign.hexadList :=
  rfl

theorem hexads_eq :
    CFSGOutside.Corpus.WittDesign.hexads = CFSG.ComponentClassification.WittDesign.hexads :=
  rfl

theorem blockAut_eq {P : Type*} (𝓛 : Finset (Finset P)) :
    CFSGOutside.Corpus.WittDesign.blockAut 𝓛 = CFSG.ComponentClassification.WittDesign.blockAut 𝓛 :=
  Subgroup.ext fun _ => Iff.rfl

theorem hexadAut_eq :
    CFSGOutside.Corpus.WittDesign.hexadAut = CFSG.ComponentClassification.WittDesign.hexadAut :=
  Subgroup.ext fun _ => Iff.rfl

end CFSGOutsideClean.Corpus.WittDesign
