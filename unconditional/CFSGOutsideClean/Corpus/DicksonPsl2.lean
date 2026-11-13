import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
import CFSGOutside.Corpus.DicksonPsl2
import CFSGOutsideClean.Corpus.Defs.ElementaryAbelian

/-! The corpus proves the statement that `CFSGOutside.Corpus.DicksonPsl2SubgroupClassification` assumes. The copied
`IsElementaryAbelian` is matched to the corpus class by `CFSGOutsideClean.Corpus.isElementaryAbelian_iff`. -/

universe u

instance CFSGOutsideClean.Corpus.dicksonPsl2SubgroupClassification :
    CFSGOutside.Corpus.DicksonPsl2SubgroupClassification.{u} :=
  ⟨fun hFcard H => by
    simp_rw [CFSGOutsideClean.Corpus.isElementaryAbelian_iff]
    exact CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hFcard H⟩
