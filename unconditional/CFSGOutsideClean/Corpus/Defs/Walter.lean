import CFSG.Open.WalterAbelianSylowTwoMilestoneDefs
import CFSG.Walter.Defs
import CFSG.Walter.ReeOrder.Ward.Defs
import CFSGOutside.Corpus.Defs.Walter
import CFSGOutsideClean.Corpus.Defs.ElementaryAbelian

/-! The definitions copied into `CFSGOutside.Corpus.Defs.Walter` are the corpus definitions. The copied
`ReeTypeHyp` differs from the corpus structure only in its copied `IsElementaryAbelian`, so the two carry the same
data, with the same `q`. -/

namespace CFSGOutsideClean.Corpus.Walter

theorem walterJ1GenA_eq : CFSGOutside.Corpus.Open.walterJ1GenA = CFSG.Open.walterJ1GenA := rfl

theorem walterJ1GenB_eq : CFSGOutside.Corpus.Open.walterJ1GenB = CFSG.Open.walterJ1GenB := rfl

theorem walterJ1_eq : CFSGOutside.Corpus.Open.walterJ1 = CFSG.Open.walterJ1 := rfl

theorem isTypeL2_eq (L : Type) [Group L] :
    CFSGOutside.Corpus.Walter.IsTypeL2 L = CFSG.Walter.IsTypeL2 L := rfl

theorem wardSign_eq : CFSGOutside.Corpus.Walter.Ward.wardSign = CFSG.Walter.Ward.wardSign := rfl

variable {G : Type} [Group G] [Finite G]

/-- The corpus `ReeTypeHyp` built from the copied one. -/
def reeTypeHypToCorpus (h : CFSGOutside.Corpus.Walter.Ward.ReeTypeHyp G) : CFSG.Walter.Ward.ReeTypeHyp G :=
  { p := h.p, f := h.f, fact_prime := h.fact_prime, p_ne_two := h.p_ne_two, f_pos := h.f_pos,
    card_sylow := h.card_sylow,
    elementary_sylow := fun P => (isElementaryAbelian_iff 2 P).mp (h.elementary_sylow P),
    index_ne_two := h.index_ne_two, J := h.J, orderOf_J := h.orderOf_J, L := h.L,
    le_centralizer := h.le_centralizer, J_not_mem := h.J_not_mem, centralizer_eq := h.centralizer_eq,
    iso := h.iso, normalizer_le := h.normalizer_le, not_commute := h.not_commute }

/-- The copied `ReeTypeHyp` built from the corpus one. -/
def reeTypeHypOfCorpus (h : CFSG.Walter.Ward.ReeTypeHyp G) : CFSGOutside.Corpus.Walter.Ward.ReeTypeHyp G :=
  { p := h.p, f := h.f, fact_prime := h.fact_prime, p_ne_two := h.p_ne_two, f_pos := h.f_pos,
    card_sylow := h.card_sylow,
    elementary_sylow := fun P => (isElementaryAbelian_iff 2 P).mpr (h.elementary_sylow P),
    index_ne_two := h.index_ne_two, J := h.J, orderOf_J := h.orderOf_J, L := h.L,
    le_centralizer := h.le_centralizer, J_not_mem := h.J_not_mem, centralizer_eq := h.centralizer_eq,
    iso := h.iso, normalizer_le := h.normalizer_le, not_commute := h.not_commute }

theorem reeTypeHypToCorpus_q (h : CFSGOutside.Corpus.Walter.Ward.ReeTypeHyp G) :
    (reeTypeHypToCorpus h).q = h.q := rfl

end CFSGOutsideClean.Corpus.Walter
