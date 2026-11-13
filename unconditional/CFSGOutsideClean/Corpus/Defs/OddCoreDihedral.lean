import CFSG.GroupTheory.PCore.Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog
import CFSGOutside.Corpus.Defs.OddCoreDihedral

/-! The definitions copied into `CFSGOutside.Corpus.Defs.OddCoreDihedral` are the corpus definitions. -/

universe u

namespace CFSGOutsideClean.Corpus

theorem oddCore_eq (G : Type*) [Group G] : CFSGOutside.Corpus.oddCore G = CFSG.oddCore G :=
  rfl

theorem hasDihedralSylowTwo_iff (G : Type u) [Group G] :
    CFSGOutside.Corpus.GorensteinWalter.HasDihedralSylowTwo G ↔
      CFSG.GorensteinWalter.HasDihedralSylowTwo G :=
  Iff.rfl

theorem isOddPrimePower_iff (q : ℕ) :
    CFSGOutside.Corpus.GorensteinWalter.IsOddPrimePower q ↔ CFSG.GorensteinWalter.IsOddPrimePower q :=
  Iff.rfl

theorem psl2_eq (K : Type u) [CommRing K] :
    CFSGOutside.Corpus.GorensteinWalter.PSL2 K = CFSG.GorensteinWalter.PSL2 K :=
  rfl

theorem psl2GF_eq (p n : ℕ) [Fact p.Prime] :
    CFSGOutside.Corpus.AGLEmbedding.PSL2GF p n = CFSG.AGLEmbedding.PSL2GF p n :=
  rfl

end CFSGOutsideClean.Corpus
