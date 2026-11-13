import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms
import CFSG.GroupTheory.FrobeniusNormalComplement
import CFSGOutside.Corpus.Defs.FrobeniusFrattini

/-! The definitions copied into `CFSGOutside.Corpus.Defs.FrobeniusFrattini` are the corpus definitions. -/

namespace CFSGOutsideClean.Corpus

theorem isNormalPComplement_iff {G : Type*} [Group G] (p : ℕ) (N : Subgroup G) :
    CFSGOutside.Corpus.GroupTheory.IsNormalPComplement p N ↔ CFSG.GroupTheory.IsNormalPComplement p N :=
  Iff.rfl

theorem quotientEquivalence_eq {P : Type*} [Group P] (N : Subgroup P) [N.Characteristic] :
    CFSGOutside.Corpus.OrderReductions.FrattiniAutomorphisms.quotientEquivalence N =
      CFSG.OrderReductions.FrattiniAutomorphisms.quotientEquivalence N :=
  rfl

theorem quotientAutomorphism_eq {P : Type*} [Group P] (N : Subgroup P) [N.Characteristic] :
    CFSGOutside.Corpus.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism N =
      CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism N :=
  rfl

end CFSGOutsideClean.Corpus
