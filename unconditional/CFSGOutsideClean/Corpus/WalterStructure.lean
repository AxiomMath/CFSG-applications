import CFSG.Milestones.CL_LIT_Walter_abelian_Sylow_two_simple
import CFSG.Walter.Final
import CFSGOutside.Corpus.WalterStructure
import CFSGOutsideClean.Corpus.Defs.Walter

/-! The corpus proves the statement that `CFSGOutside.Corpus.WalterStructure` assumes: `CFSG.Walter.walter_structure`
with `JRStrongHyp` discharged by the corpus's own proof, the one used for
`CFSG.Milestones.cl_lit_walter_abelian_sylow_two_simple`. -/

instance CFSGOutsideClean.Corpus.walterStructure : CFSGOutside.Corpus.WalterStructure :=
  ⟨fun G _ _ _ hnonab P hP => by
    rcases CFSG.Walter.walter_structure
      (CFSG.Walter.jrStrongHyp_of_open
        (CFSG.Walter.W67.theorem_of_reeIdentNative
          (CFSG.Walter.W67.prop_6_6_of CFSG.Walter.W67.prop_4_1 CFSG.Walter.W67.prop_5_6
            (CFSG.Walter.W67.lemma_6_2_of CFSG.Walter.W67.prop_4_1 CFSG.Walter.W67.prop_5_6)
            CFSG.Walter.W67.lemma_6_5)
          (CFSG.Walter.Ree.reeIdentNative CFSG.Walter.Ree.T2.baseExists))
        CFSG.Walter.j1RecogHyp CFSG.Walter.jtThreeHyp) G hnonab P hP with h | h | h
    · exact Or.inl h
    · obtain ⟨h⟩ := h
      exact Or.inr (Or.inl ⟨CFSGOutsideClean.Corpus.Walter.reeTypeHypOfCorpus h⟩)
    · exact Or.inr (Or.inr h)⟩
