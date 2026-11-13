import CFSG.Timmesfeld.Orders.Classical
import CFSGOutside.Corpus.CardStatedClassicalModelTwo
import CFSGOutsideClean.Corpus.Defs.ClassicalModel
import CFSGOutsideClean.Corpus.Defs.OrdFormulas

/-! The corpus proves the statement that `CFSGOutside.Corpus.CardStatedClassicalModelTwo` assumes. The copied
`StatedClassicalModel` is matched to the corpus one by `CFSGOutsideClean.Corpus.Open.statedClassicalModel_iff`. -/

instance CFSGOutsideClean.Corpus.cardStatedClassicalModelTwo :
    CFSGOutside.Corpus.CardStatedClassicalModelTwo :=
  ⟨fun {G _ t n f} h => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := CFSG.Timmesfeld.card_statedClassicalModel_two
      ((CFSGOutsideClean.Corpus.Open.statedClassicalModel_iff G t n 2 f).1 h)
    refine ⟨fun ht => ?_, fun ht => ?_, fun ht => ?_, fun ht => ?_, fun ht => ?_⟩ <;> subst ht
    exacts [h1 rfl, h2 rfl, h3 rfl, h4 rfl, h5 rfl]⟩
