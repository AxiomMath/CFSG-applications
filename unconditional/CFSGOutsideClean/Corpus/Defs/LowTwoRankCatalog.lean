import CFSG.Open.Catalog
import CFSGOutside.Corpus.Defs.LowTwoRankCatalog

/-! The definitions copied into `CFSGOutside.Corpus.Defs.LowTwoRankCatalog` are the corpus definitions. -/

namespace CFSGOutsideClean.Corpus

theorem open_psu3_eq (p k : ℕ) [Fact p.Prime] :
    CFSGOutside.Corpus.Open.PSU3 p k = CFSG.Open.PSU3 p k :=
  rfl

theorem open_m11_eq : CFSGOutside.Corpus.Open.M11 = CFSG.Open.M11 :=
  rfl

end CFSGOutsideClean.Corpus
