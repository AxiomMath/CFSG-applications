import CFSG.Blueprint.Chevalley
import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.ReeTransport
import CFSG.LieType.Ree.BorelOvergroupClassification
import CFSG.LieType.Ree.FixedBruhatDecomposition
import CFSG.LieType.Ree.FixedMonomialQuotient
import CFSG.LieType.Ree.FixedTwoCellParabolics
import CFSG.LieType.Ree.FixedWeylStructure
import CFSG.LieType.Ree.LargeReeSylowOpposition
import CFSGOutside.Corpus.HallPaige.LieExcTwRee
import CFSGOutsideClean.Corpus.HallPaige.LieExcChevalley
import CFSGOutsideClean.Corpus.HallPaige.LieRankOneRee

/-! The corpus proves the statements that `CFSGOutside.Corpus.HallPaige.LieExcTwRee` assumes. -/

namespace CFSGOutsideClean.Corpus

open CFSGOutside.Corpus.Exc

-- the copied and the corpus groups are compared by unfolding, which takes many heartbeats
set_option maxHeartbeats 4000000

noncomputable instance hpLieExcTwReeFixedOrbits : CFSGOutside.Corpus.Ree.ReeTag.FixedOrbits where
  fixedOrbitElement_mul_self := fun {t} => by cases t; exacts [CFSG.LieType.Ree.ReeTag.fixedOrbitElement_mul_self (t := .G2), CFSG.LieType.Ree.ReeTag.fixedOrbitElement_mul_self (t := .F4)]
  fixedOrbitElement_mem := fun {t} => by cases t; exacts [CFSG.LieType.Ree.ReeTag.fixedOrbitElement_mem (t := .G2), CFSG.LieType.Ree.ReeTag.fixedOrbitElement_mem (t := .F4)]
  fixedOrbitElement_mem_fixedOrbitWeyl := fun {t} => by cases t; exacts [CFSG.LieType.Ree.ReeTag.fixedOrbitElement_mem_fixedOrbitWeyl (t := .G2), CFSG.LieType.Ree.ReeTag.fixedOrbitElement_mem_fixedOrbitWeyl (t := .F4)]
  fixedOrbitWeyl_inter_relWeylRee := fun {t} => by cases t; exacts [CFSG.LieType.Ree.ReeTag.fixedOrbitWeyl_inter_relWeylRee (t := .G2), CFSG.LieType.Ree.ReeTag.fixedOrbitWeyl_inter_relWeylRee (t := .F4)]
  fixedOrbitElement_injective := fun {t} => by cases t; exacts [CFSG.LieType.Ree.ReeTag.fixedOrbitElement_injective (t := .G2), CFSG.LieType.Ree.ReeTag.fixedOrbitElement_injective (t := .F4)]
  canonicalRep_mem_reeFixedMonomial := fun t => by cases t; exacts [CFSG.LieType.Ree.ReeTag.canonicalRep_mem_reeFixedMonomial .G2, CFSG.LieType.Ree.ReeTag.canonicalRep_mem_reeFixedMonomial .F4]
  reeFixedMonomial_eq_sup := fun t => by cases t; exacts [CFSG.LieType.Ree.ReeTag.reeFixedMonomial_eq_sup .G2, CFSG.LieType.Ree.ReeTag.reeFixedMonomial_eq_sup .F4]
  reeGamma_eq_iUnion_reeFixedBruhatCell := fun {t} => by cases t; exacts [CFSG.LieType.Ree.ReeTag.reeGamma_eq_iUnion_reeFixedBruhatCell (t := .G2), CFSG.LieType.Ree.ReeTag.reeGamma_eq_iUnion_reeFixedBruhatCell (t := .F4)]
  reeGamma_eq_sup_reeFixedMonomial := fun {t} => by cases t; exacts [CFSG.LieType.Ree.ReeTag.reeGamma_eq_sup_reeFixedMonomial (t := .G2), CFSG.LieType.Ree.ReeTag.reeGamma_eq_sup_reeFixedMonomial (t := .F4)]
  coe_reeGamma_inf_parabolicSubgroup := fun {t} => by cases t; exacts [CFSG.LieType.Ree.ReeTag.coe_reeGamma_inf_parabolicSubgroup (t := .G2), CFSG.LieType.Ree.ReeTag.coe_reeGamma_inf_parabolicSubgroup (t := .F4)]
  not_normal_reeFixedBorel_subgroupOf := fun {t} => by cases t; exacts [CFSG.LieType.Ree.ReeTag.not_normal_reeFixedBorel_subgroupOf (t := .G2), CFSG.LieType.Ree.ReeTag.not_normal_reeFixedBorel_subgroupOf (t := .F4)]
  not_dvd_index_reeFixedPosUnipotent := fun {t} => by cases t; exacts [CFSG.LieType.Ree.ReeTag.not_dvd_index_reeFixedPosUnipotent (t := .G2), CFSG.LieType.Ree.ReeTag.not_dvd_index_reeFixedPosUnipotent (t := .F4)]

noncomputable instance hpLieExcTwReeReeGammaCat : CFSGOutside.Corpus.Ree.ReeGammaCat where
  reeGamma_equiv_cat_of_card := CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.reeGamma_equiv_cat_of_card

end CFSGOutsideClean.Corpus
