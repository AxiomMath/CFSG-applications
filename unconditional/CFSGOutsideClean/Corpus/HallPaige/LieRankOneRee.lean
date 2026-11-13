import CFSG.Blueprint.Chevalley
import CFSG.LieType.Chevalley.WeylRoots
import CFSG.LieType.Ree.G2PrimeFieldWords
import CFSG.LieType.Ree.NormalPositiveGeneration
import CFSG.LieType.Ree.SmallReeBorelCosetAction
import CFSG.LieType.Ree.SmallReeFixedCoordinates
import CFSG.LieType.Ree.SmallReeTorusAction
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeModel
import CFSG.Walter.Ree.Model.Cells
import CFSG.Walter.Ree.Model.Fusion
import CFSGOutside.Corpus.HallPaige.LieRankOneRee
import CFSGOutsideClean.Corpus.HallPaige.LieExcChevalley

/-! The corpus proves the statements that `CFSGOutside.Corpus.HallPaige.LieRankOneRee` assumes. -/

namespace CFSGOutsideClean.Corpus

open CFSGOutside.Corpus.Exc

-- the copied and the corpus groups are compared by unfolding, which takes many heartbeats
set_option maxHeartbeats 4000000

/-- The automorphism of the small Ree groups of the corpus on the copied tags. -/
noncomputable instance hpLieRankOneReeReeAut : CFSGOutside.Corpus.Ree.ReeTag.ReeAut where
  finiteReeAut t K _ _ _ a := match t with
    | .G2 => CFSG.LieType.Ree.ReeTag.finiteReeAut .G2 K a
    | .F4 => CFSG.LieType.Ree.ReeTag.finiteReeAut .F4 K a

noncomputable instance hpLieRankOneReeFiniteWeylGroup : CFSGOutside.Corpus.Ree.FiniteWeylGroup where
  instFiniteWeylGroup := fun {τ} => by cases τ; exacts [CFSG.LieType.Chevalley.instFiniteWeylGroup (τ := .G2), CFSG.LieType.Chevalley.instFiniteWeylGroup (τ := .F4), CFSG.LieType.Chevalley.instFiniteWeylGroup (τ := .D4), CFSG.LieType.Chevalley.instFiniteWeylGroup (τ := .E6), CFSG.LieType.Chevalley.instFiniteWeylGroup (τ := .E7), CFSG.LieType.Chevalley.instFiniteWeylGroup (τ := .E8)]

noncomputable instance hpLieRankOneReeReeModel : CFSGOutside.Corpus.Ree.ReeModel where
  nonempty_reeGamma_equiv := CFSG.AGLEmbedding.ReeModel.nonempty_reeGamma_equiv
  canonicalRep_longest_conj_torus := fun {t} => by cases t; exacts [CFSG.LieType.Ree.ReeTag.canonicalRep_longest_conj_torus (t := .G2), CFSG.LieType.Ree.ReeTag.canonicalRep_longest_conj_torus (t := .F4)]
  canonicalRep_longest_mem_reeGamma := CFSG.LieType.Ree.ReeTag.canonicalRep_longest_mem_reeGamma
  reeGamma_G2_cases := CFSG.Walter.Ree.Model.reeGamma_G2_cases
  eq_of_mul_canonicalRep_mul_eq := CFSG.Walter.Ree.Model.eq_of_mul_canonicalRep_mul_eq
  small_Ree_positive_fixed_coordinates := CFSG.LieType.Ree.small_Ree_positive_fixed_coordinates
  small_Ree_positive_torus_action := CFSG.LieType.Ree.small_Ree_positive_torus_action
  ree_G2_prime_field_words := CFSG.LieType.Ree.ReeTag.ree_G2_prime_field_words
  smallReeE8_relations := CFSG.Walter.Ree.Model.smallReeE8_relations

end CFSGOutsideClean.Corpus
