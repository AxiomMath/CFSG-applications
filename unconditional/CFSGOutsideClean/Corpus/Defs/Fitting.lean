import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
import CFSGOutside.Corpus.Defs.Fitting

/-! The definitions copied into `CFSGOutside.Corpus.Defs.Fitting` are the corpus definitions. -/

namespace CFSGOutsideClean.Corpus

theorem fittingSubgroup_eq (G : Type*) [Group G] :
    CFSGOutside.Corpus.fittingSubgroup G = CFSG.fittingSubgroup G :=
  rfl

theorem pCore_eq (p : ℕ) (G : Type*) [Group G] :
    CFSGOutside.Corpus.pCore p G = CFSG.pCore p G :=
  rfl

end CFSGOutsideClean.Corpus
