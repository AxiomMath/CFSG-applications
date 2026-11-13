import CFSG.Open.Defs
import CFSG.Open.WalterAbelianSylowTwoMilestoneDefs
import CFSG.Open.GoldschmidtStronglyClosedAbelianMilestoneDefs
import CFSGOutside.Corpus.Defs.J1Models

/-! The definitions copied into `CFSGOutside.Corpus.Defs.J1Models` are the corpus definitions. -/

namespace CFSGOutsideClean.Corpus

theorem ordRee_eq (q : ℕ) : CFSGOutside.Corpus.Open.ordRee q = CFSG.Open.ordRee q :=
  rfl

theorem walterJ1_eq : CFSGOutside.Corpus.Open.walterJ1 = CFSG.Open.walterJ1 :=
  rfl

theorem goldschmidtJ1_eq : CFSGOutside.Corpus.Open.goldschmidtJ1 = CFSG.Open.goldschmidtJ1 :=
  rfl

end CFSGOutsideClean.Corpus
