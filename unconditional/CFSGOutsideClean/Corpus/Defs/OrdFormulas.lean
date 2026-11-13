import CFSG.Open.Defs
import CFSGOutside.Corpus.Defs.OrdFormulas

/-! The order formulas copied into `CFSGOutside.Corpus.Defs.OrdFormulas` are the corpus definitions. -/

namespace CFSGOutsideClean.Corpus.Open

theorem ordA_eq (n q : ℕ) : CFSGOutside.Corpus.Open.ordA n q = CFSG.Open.ordA n q :=
  rfl

theorem ordTwistedA_eq (n q : ℕ) :
    CFSGOutside.Corpus.Open.ordTwistedA n q = CFSG.Open.ordTwistedA n q :=
  rfl

theorem ordBC_eq (n q : ℕ) : CFSGOutside.Corpus.Open.ordBC n q = CFSG.Open.ordBC n q :=
  rfl

theorem ordD_eq (n q : ℕ) : CFSGOutside.Corpus.Open.ordD n q = CFSG.Open.ordD n q :=
  rfl

theorem ordTwistedD_eq (n q : ℕ) :
    CFSGOutside.Corpus.Open.ordTwistedD n q = CFSG.Open.ordTwistedD n q :=
  rfl

theorem ordG2_eq (q : ℕ) : CFSGOutside.Corpus.Open.ordG2 q = CFSG.Open.ordG2 q :=
  rfl

theorem ordTrialityD4_eq (q : ℕ) :
    CFSGOutside.Corpus.Open.ordTrialityD4 q = CFSG.Open.ordTrialityD4 q :=
  rfl

theorem ordSuzuki_eq (q : ℕ) : CFSGOutside.Corpus.Open.ordSuzuki q = CFSG.Open.ordSuzuki q :=
  rfl

end CFSGOutsideClean.Corpus.Open
