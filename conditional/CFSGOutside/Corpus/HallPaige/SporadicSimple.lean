import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Corpus input: the sporadic presented groups are finite and simple

The corpus theorem used by the sporadic-group certificates (`results_conditional/CFSGOutside/HallPaige/Sporadic/*.lean`),
stated as a class whose field is the corpus statement from AxiomMath/CFSG @ 69cb972. It is only used to
see that a permutation representation of a sporadic group with a nontrivial generator is
faithful.
-/

namespace CFSGOutside.Corpus

/-- The sporadic groups of the TauCeti catalogue are finite and simple. -/
class Simple : Prop where
  /-- **The sporadic groups of the TauCeti catalogue are finite and simple.**
  Corpus: `CFSG.Milestones.fam_sporadic_converse_tauCeti`,
  CFSG/Milestones/FAM_sporadic_converse.lean:14 (AxiomMath/CFSG @ 69cb972). -/
  fam_sporadic_converse_tauCeti (s : TauCeti.SporadicName) :
    Finite s.Group ∧ IsSimpleGroup s.Group

end CFSGOutside.Corpus
