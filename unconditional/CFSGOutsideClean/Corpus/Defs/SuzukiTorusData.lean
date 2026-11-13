import CFSG.GroupTheory.SuzukiPointTorus.Basic
import CFSGOutside.Corpus.Defs.SuzukiTorusData

/-! The structure copied into `CFSGOutside.Corpus.Defs.SuzukiTorusData` is the corpus structure. -/

namespace CFSGOutsideClean.Corpus

theorem suzukiTorusData_iff {X : Type*} [Group X] [Finite X] (q : ℕ) :
    CFSGOutside.Corpus.SuzukiTorusData X q ↔ CFSG.GroupTheory.SuzukiTorusData X q :=
  ⟨fun h => { faithful := h.faithful, card_points := h.card_points, fixes_le_two := h.fixes_le_two,
              card_sylow := h.card_sylow, regular := h.regular,
              inf_normalizer_isCyclic := h.inf_normalizer_isCyclic,
              inf_normalizer_card := h.inf_normalizer_card,
              inf_normalizer_free := h.inf_normalizer_free, card_frattini := h.card_frattini },
    fun h => { faithful := h.faithful, card_points := h.card_points, fixes_le_two := h.fixes_le_two,
               card_sylow := h.card_sylow, regular := h.regular,
               inf_normalizer_isCyclic := h.inf_normalizer_isCyclic,
               inf_normalizer_card := h.inf_normalizer_card,
               inf_normalizer_free := h.inf_normalizer_free, card_frattini := h.card_frattini }⟩

end CFSGOutsideClean.Corpus
