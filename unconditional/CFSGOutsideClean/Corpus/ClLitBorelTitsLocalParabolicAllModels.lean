import CFSG.Milestones.CL_LIT_Borel_Tits_local_parabolic
import CFSGOutside.Corpus.ClLitBorelTitsLocalParabolicAllModels
import CFSGOutsideClean.Corpus.Defs.LieModel

/-! The corpus proves the Borel–Tits statement that
`CFSGOutside.Corpus.ClLitBorelTitsLocalParabolicAllModels` assumes, through the equivalence of the copied and the
corpus models of the simple groups of Lie type. -/

open CFSGOutsideClean.Corpus.Open (statedLieTagToCorpus statedLieTagToCorpus_eq_tits_iff)

instance CFSGOutsideClean.Corpus.clLitBorelTitsLocalParabolicAllModels :
    CFSGOutside.Corpus.ClLitBorelTitsLocalParabolicAllModels :=
  ⟨fun X _ t n r f hmodel U hU hUr => by
    obtain ⟨S, P, hP, hNU, hcore, hU', hS, hS'⟩ :=
      CFSG.Milestones.cl_lit_borel_tits_local_parabolic_all_models X (statedLieTagToCorpus t) n r f
        ((CFSGOutsideClean.Corpus.lieModel_iff X t n r f).1 hmodel) U hU hUr
    exact ⟨S, P, hP, hNU, hcore, hU',
      fun ht => hS (fun h => ht ((statedLieTagToCorpus_eq_tits_iff t).1 h)),
      fun ht => hS' ((statedLieTagToCorpus_eq_tits_iff t).2 ht)⟩⟩
