import CFSG.Walter.ReeOrder.Ward.Order
import CFSG.Walter.ReeOrder.WardLocal
import CFSGOutside.Corpus.WardLocal
import CFSGOutsideClean.Corpus.Defs.Walter

/-! The corpus proves the statements that `CFSGOutside.Corpus.WardOrder`, `WardTwoThree` and `WardFour` assume,
through `CFSGOutsideClean.Corpus.Walter.reeTypeHypToCorpus`. -/

namespace CFSGOutsideClean.Corpus

open CFSGOutsideClean.Corpus.Walter

instance wardOrder : CFSGOutside.Corpus.WardOrder :=
  ⟨fun h => CFSG.Walter.Ward.ward_order (reeTypeHypToCorpus h)⟩

instance wardFour : CFSGOutside.Corpus.WardFour :=
  ⟨fun h _ hq => CFSG.Walter.WardLocal.ward_four (reeTypeHypToCorpus h) hq⟩

instance wardTwoThree : CFSGOutside.Corpus.WardTwoThree := ⟨fun {G} _ _ h P => by
  obtain ⟨h1, h2, h3, h4, P₁, W, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ :=
    CFSG.Walter.WardLocal.ward_two_three (reeTypeHypToCorpus h) P
  refine ⟨h1, h2, (isElementaryAbelian_iff _ _).mpr h3, h4, P₁, W, h5, h6,
    (isElementaryAbelian_iff _ _).mpr h7, h8, h9, h10, h11, h12, h13, h14, fun t ht ht2 => ?_, h16⟩
  obtain ⟨a, b, c, d⟩ := h15 t ht ht2
  exact ⟨a, (isElementaryAbelian_iff _ _).mpr b, c, d⟩⟩

end CFSGOutsideClean.Corpus
