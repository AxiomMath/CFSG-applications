import CFSG.Adapters.TauCetiExceptional.EvenBridgeTwistedE6
import CFSG.Adapters.TauCetiExceptional.EvenD4
import CFSG.Adapters.TauCetiExceptional.TwistedD4Push
import CFSG.Adapters.TauCetiExceptional.TwistedE6Push
import CFSG.Blueprint.Chevalley
import CFSG.LieType.Chevalley.FoldedWeylIdentification
import CFSG.LieType.Chevalley.GraphFixedOrbitParametrization
import CFSG.LieType.Chevalley.GraphFixedRankOneScalar
import CFSG.LieType.Chevalley.GraphFixedRootBruhat
import CFSG.LieType.Chevalley.GraphFixedRootMonomialQuotient
import CFSG.LieType.Chevalley.GraphFixedSimpleBruhat
import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalDihedralTwisted
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicGenTwisted
import CFSG.Open.SplitBNPair
import CFSGOutside.Corpus.HallPaige.LieExcTw
import CFSGOutsideClean.Corpus.HallPaige.LieExcChevalley

/-! The corpus proves the statements that `CFSGOutside.Corpus.HallPaige.LieExcTw` assumes. -/

namespace CFSGOutsideClean.Corpus

open CFSGOutside.Corpus.Exc

-- the copied and the corpus groups are compared by unfolding, which takes many heartbeats
set_option maxHeartbeats 8000000

/-- The copied split BN-pair structure holds when the corpus one does. -/
theorem isSplitBNPair_ofCorpus {M : Type} [Group M] {p : ℕ} {B N : Subgroup M}
    (h : CFSG.ASVolI.ChIJK.IsSplitBNPair p B N) : CFSGOutside.Corpus.ExcTw.IsSplitBNPair p B N :=
  ⟨h.gen, h.normal_inter, h.coxeter, h.split⟩

/-- The label permutations of the corpus on the copied tags. -/
noncomputable instance hpLieExcTwLabelPerm : CFSGOutside.Corpus.ExcTw.LabelPerm where
  labelPerm {τ} π hπ := match τ with
    | .G2 => CFSG.Blueprint.Chevalley.labelPerm (τ := .G2) π hπ
    | .F4 => CFSG.Blueprint.Chevalley.labelPerm (τ := .F4) π hπ
    | .D4 => CFSG.Blueprint.Chevalley.labelPerm (τ := .D4) π hπ
    | .E6 => CFSG.Blueprint.Chevalley.labelPerm (τ := .E6) π hπ
    | .E7 => CFSG.Blueprint.Chevalley.labelPerm (τ := .E7) π hπ
    | .E8 => CFSG.Blueprint.Chevalley.labelPerm (τ := .E8) π hπ

noncomputable instance hpLieExcTwGraphFixed : CFSGOutside.Corpus.ExcTw.GraphFixed where
  graphFixed_isSplitBNPair := fun t => match t with
    | .E6 => fun K _ _ p hp _ σ =>
      have h := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPGen.graphFixed_isSplitBNPair .E6 K hp σ
      ⟨isSplitBNPair_ofCorpus h.1, h.2⟩
    | .D4 => fun K _ _ p hp _ σ =>
      have h := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPGen.graphFixed_isSplitBNPair .D4 K hp σ
      ⟨isSplitBNPair_ofCorpus h.1, h.2⟩
  disjoint_graphFixedRootBruhatCell := fun {t} => by cases t; exacts [CFSG.LieType.Chevalley.disjoint_graphFixedRootBruhatCell (t := .E6), CFSG.LieType.Chevalley.disjoint_graphFixedRootBruhatCell (t := .D4)]
  fixed_simple_Bruhat_multiplication := fun t => by cases t; exacts [CFSG.LieType.Chevalley.fixed_simple_Bruhat_multiplication .E6, CFSG.LieType.Chevalley.fixed_simple_Bruhat_multiplication .D4]
  canonicalRep_mem_graphFixedRootMonomial := fun t => by cases t; exacts [CFSG.LieType.Chevalley.canonicalRep_mem_graphFixedRootMonomial .E6, CFSG.LieType.Chevalley.canonicalRep_mem_graphFixedRootMonomial .D4]
  graphFixedRootMonomial_eq_sup := fun t => by cases t; exacts [CFSG.LieType.Chevalley.graphFixedRootMonomial_eq_sup .E6, CFSG.LieType.Chevalley.graphFixedRootMonomial_eq_sup .D4]
  fixed_Weyl_folded_identification := fun t => by cases t; exacts [CFSG.LieType.Chevalley.fixed_Weyl_folded_identification .E6, CFSG.LieType.Chevalley.fixed_Weyl_folded_identification .D4]
  orbitH_mem_graphFixedRootGroup := fun t => by cases t; exacts [CFSG.LieType.Chevalley.orbitH_mem_graphFixedRootGroup .E6, CFSG.LieType.Chevalley.orbitH_mem_graphFixedRootGroup .D4]
  coe_orbitH := fun t => by cases t; exacts [CFSG.LieType.Chevalley.coe_orbitH .E6, CFSG.LieType.Chevalley.coe_orbitH .D4]

noncomputable instance hpLieExcTwBridges : CFSGOutside.Corpus.ExcTw.Bridges where
  twistedBridge_twistedE6 := CFSG.TauCetiBridge.Twisted.twistedBridge_twistedE6
  twistedBridge_trialityD4 := CFSG.TauCetiBridge.Twisted.twistedBridge_trialityD4
  twistedBridgeEven_twistedE6 := CFSG.TauCetiBridge.Even.twistedBridgeEven_twistedE6
  twistedBridgeEven_trialityD4 := CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4
  nonempty_mulEquiv_graphFixedRootGroup' := fun {T} _ t => by cases t; exacts [CFSG.ComponentClassification.UnbalancingLocal.DihedralTwisted.nonempty_mulEquiv_graphFixedRootGroup' (t := .E6), CFSG.ComponentClassification.UnbalancingLocal.DihedralTwisted.nonempty_mulEquiv_graphFixedRootGroup' (t := .D4)]

end CFSGOutsideClean.Corpus
