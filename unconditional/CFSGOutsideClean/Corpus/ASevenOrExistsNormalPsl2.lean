import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
import CFSGOutside.Corpus.ASevenOrExistsNormalPsl2
import CFSGOutsideClean.Corpus.Defs.OddCoreDihedral

/-! The corpus proves the statement that `CFSGOutside.Corpus.ASevenOrExistsNormalPsl2` assumes. -/

instance CFSGOutsideClean.Corpus.aSevenOrExistsNormalPsl2 : CFSGOutside.Corpus.ASevenOrExistsNormalPsl2 :=
  ⟨@CFSG.ABGDGroups.aSeven_or_exists_normal_psl2⟩
