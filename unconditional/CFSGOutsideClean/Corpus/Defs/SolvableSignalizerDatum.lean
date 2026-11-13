import CFSG.GroupTheory.SteinbergBSSolvableSignalizer
import CFSGOutside.Corpus.Defs.SolvableSignalizerDatum
import CFSGOutsideClean.Corpus.Defs.ElementaryAbelian

/-! The structure copied into `CFSGOutside.Corpus.Defs.SolvableSignalizerDatum` is the corpus structure. -/

namespace CFSGOutsideClean.Corpus

theorem isSolvableSignalizerDatum_iff (p : ℕ) (A : Type*) [Group A] (G : Type*) [Group G]
    (α : A →* MulAut G) (θ : A → Subgroup G) :
    CFSGOutside.Corpus.GroupTheory.SteinbergBS.IsSolvableSignalizerDatum p A G α θ ↔
      CFSG.GroupTheory.SteinbergBS.IsSolvableSignalizerDatum p A G α θ :=
  ⟨fun h => ⟨h.prime, h.finite_actor, (isElementaryAbelian_iff p A).1 h.elementary, h.card_actor,
      h.finite, h.invariant, h.solvable, h.coprime, h.le_fixed, h.balance⟩,
    fun h => ⟨h.prime, h.finite_actor, (isElementaryAbelian_iff p A).2 h.elementary, h.card_actor,
      h.finite, h.invariant, h.solvable, h.coprime, h.le_fixed, h.balance⟩⟩

end CFSGOutsideClean.Corpus
