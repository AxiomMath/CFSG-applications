import CFSG.Open.GriessSchurMultipliersMilestoneDefs
import CFSGOutside.Corpus.Defs.GriessHopf

/-! The definitions copied into `CFSGOutside.Corpus.Defs.GriessHopf` are the corpus definitions. -/

namespace CFSGOutsideClean.Corpus.Open

theorem griessHopfRelations_eq (X : Type) [Group X] :
    CFSGOutside.Corpus.Open.griessHopfRelations X = CFSG.Open.griessHopfRelations X :=
  rfl

theorem griessHopfMultiplier_eq (X : Type) [Group X] :
    CFSGOutside.Corpus.Open.griessHopfMultiplier X = CFSG.Open.griessHopfMultiplier X :=
  rfl

theorem griessPSLExceptional_eq (n q : ℕ) :
    CFSGOutside.Corpus.Open.griessPSLExceptional n q = CFSG.Open.griessPSLExceptional n q :=
  rfl

end CFSGOutsideClean.Corpus.Open
