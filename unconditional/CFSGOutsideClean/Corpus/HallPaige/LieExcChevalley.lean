import CFSG.Adapters.TauCetiExceptional.BridgeE8
import CFSG.Adapters.TauCetiExceptional.BridgeF4
import CFSG.Adapters.TauCetiExceptional.BridgeG2
import CFSG.Adapters.TauCetiExceptional.EvenBridgeE6E7
import CFSG.Adapters.TauCetiExceptional.EvenBridgeE8
import CFSG.Adapters.TauCetiExceptional.EvenBridgeF4
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
import CFSG.Adapters.TauCetiExceptional.MinusculeBridgeE
import CFSG.Blueprint.ChevalleyParameterAddition
import CFSG.Blueprint.ChevalleyRootGroupsTorus
import CFSG.Blueprint.ChevalleySimpleRoots
import CFSG.LieType.Chevalley.AdjointCenter
import CFSG.LieType.Chevalley.ChevalleySplitBN
import CFSG.LieType.Chevalley.PosUnipotentSylow
import CFSG.LieType.Chevalley.SylowOpposition
import CFSG.LieType.RootSystem.Basic
import CFSG.LieType.RootSystem.Positivity
import CFSGOutside.Corpus.HallPaige.LieExcChevalley

/-!
# The corpus proves the statements that `CFSGOutside.Corpus.HallPaige.LieExcChevalley` assumes

The copies of `Tag` and of the definitions on it are not the corpus ones, so each statement about all tags is proved
by cases on the tag, where the copied and the corpus definitions reduce to the same term. The root predicate and the
operators `xOp`, `yOp`, `latticeWeight`, which the copy takes as parameters, are instantiated with the corpus ones.
-/

namespace CFSGOutsideClean.Corpus

open CFSGOutside.Corpus.Exc

/-- The root predicate of the corpus, `CFSG.Blueprint.Chevalley.IsRoot`, on the copied tags. -/
def rootPredIsRoot : (τ : Tag) → (Fin τ.rank → ℤ) → Prop
  | .G2, v => CFSG.Blueprint.Chevalley.IsRoot .G2 v
  | .F4, v => CFSG.Blueprint.Chevalley.IsRoot .F4 v
  | .D4, v => CFSG.Blueprint.Chevalley.IsRoot .D4 v
  | .E6, v => CFSG.Blueprint.Chevalley.IsRoot .E6 v
  | .E7, v => CFSG.Blueprint.Chevalley.IsRoot .E7 v
  | .E8, v => CFSG.Blueprint.Chevalley.IsRoot .E8 v

instance hpLieExcChevalleyRootPred : RootPred where
  IsRoot := rootPredIsRoot
  basis τ j := by cases τ <;> exact CFSG.Blueprint.Chevalley.IsRoot.basis _

/-- The root operators of the corpus on the copied tags. -/
noncomputable instance hpLieExcChevalleyOps : Ops where
  xOp τ R _ i c := match τ with
    | .G2 => CFSG.Blueprint.Chevalley.xOp .G2 R i c
    | .F4 => CFSG.Blueprint.Chevalley.xOp .F4 R i c
    | .D4 => CFSG.Blueprint.Chevalley.xOp .D4 R i c
    | .E6 => CFSG.Blueprint.Chevalley.xOp .E6 R i c
    | .E7 => CFSG.Blueprint.Chevalley.xOp .E7 R i c
    | .E8 => CFSG.Blueprint.Chevalley.xOp .E8 R i c
  yOp τ R _ i c := match τ with
    | .G2 => CFSG.Blueprint.Chevalley.yOp .G2 R i c
    | .F4 => CFSG.Blueprint.Chevalley.yOp .F4 R i c
    | .D4 => CFSG.Blueprint.Chevalley.yOp .D4 R i c
    | .E6 => CFSG.Blueprint.Chevalley.yOp .E6 R i c
    | .E7 => CFSG.Blueprint.Chevalley.yOp .E7 R i c
    | .E8 => CFSG.Blueprint.Chevalley.yOp .E8 R i c
  latticeWeight {τ} a := match τ, a with
    | .G2, a => CFSG.Blueprint.Chevalley.Label.latticeWeight (τ := .G2) a
    | .F4, a => CFSG.Blueprint.Chevalley.Label.latticeWeight (τ := .F4) a
    | .D4, a => CFSG.Blueprint.Chevalley.Label.latticeWeight (τ := .D4) a
    | .E6, a => CFSG.Blueprint.Chevalley.Label.latticeWeight (τ := .E6) a
    | .E7, a => CFSG.Blueprint.Chevalley.Label.latticeWeight (τ := .E7) a
    | .E8, a => CFSG.Blueprint.Chevalley.Label.latticeWeight (τ := .E8) a
  latticeWeight_inl {τ} i := by cases τ <;> rfl
  latticeWeight_inr {τ} α := by cases τ <;> rfl

instance hpLieExcChevalleyParameterAddition : ParameterAddition where
  xOp_mul_xOp_neg := fun {τ} => by cases τ <;> first | exact CFSG.Blueprint.Chevalley.xOp_mul_xOp_neg (τ := .G2) | exact CFSG.Blueprint.Chevalley.xOp_mul_xOp_neg (τ := .F4) | exact CFSG.Blueprint.Chevalley.xOp_mul_xOp_neg (τ := .D4) | exact CFSG.Blueprint.Chevalley.xOp_mul_xOp_neg (τ := .E6) | exact CFSG.Blueprint.Chevalley.xOp_mul_xOp_neg (τ := .E7) | exact CFSG.Blueprint.Chevalley.xOp_mul_xOp_neg (τ := .E8)
  xOp_neg_mul_xOp := fun {τ} => by cases τ <;> first | exact CFSG.Blueprint.Chevalley.xOp_neg_mul_xOp (τ := .G2) | exact CFSG.Blueprint.Chevalley.xOp_neg_mul_xOp (τ := .F4) | exact CFSG.Blueprint.Chevalley.xOp_neg_mul_xOp (τ := .D4) | exact CFSG.Blueprint.Chevalley.xOp_neg_mul_xOp (τ := .E6) | exact CFSG.Blueprint.Chevalley.xOp_neg_mul_xOp (τ := .E7) | exact CFSG.Blueprint.Chevalley.xOp_neg_mul_xOp (τ := .E8)
  yOp_mul_yOp_neg := fun {τ} => by cases τ <;> first | exact CFSG.Blueprint.Chevalley.yOp_mul_yOp_neg (τ := .G2) | exact CFSG.Blueprint.Chevalley.yOp_mul_yOp_neg (τ := .F4) | exact CFSG.Blueprint.Chevalley.yOp_mul_yOp_neg (τ := .D4) | exact CFSG.Blueprint.Chevalley.yOp_mul_yOp_neg (τ := .E6) | exact CFSG.Blueprint.Chevalley.yOp_mul_yOp_neg (τ := .E7) | exact CFSG.Blueprint.Chevalley.yOp_mul_yOp_neg (τ := .E8)
  yOp_neg_mul_yOp := fun {τ} => by cases τ <;> first | exact CFSG.Blueprint.Chevalley.yOp_neg_mul_yOp (τ := .G2) | exact CFSG.Blueprint.Chevalley.yOp_neg_mul_yOp (τ := .F4) | exact CFSG.Blueprint.Chevalley.yOp_neg_mul_yOp (τ := .D4) | exact CFSG.Blueprint.Chevalley.yOp_neg_mul_yOp (τ := .E6) | exact CFSG.Blueprint.Chevalley.yOp_neg_mul_yOp (τ := .E7) | exact CFSG.Blueprint.Chevalley.yOp_neg_mul_yOp (τ := .E8)
  upTransport := fun τ => by cases τ <;> first | exact CFSG.Blueprint.Chevalley.upTransport (τ := .G2) | exact CFSG.Blueprint.Chevalley.upTransport (τ := .F4) | exact CFSG.Blueprint.Chevalley.upTransport (τ := .D4) | exact CFSG.Blueprint.Chevalley.upTransport (τ := .E6) | exact CFSG.Blueprint.Chevalley.upTransport (τ := .E7) | exact CFSG.Blueprint.Chevalley.upTransport (τ := .E8)
  downTransport := fun τ => by cases τ <;> first | exact CFSG.Blueprint.Chevalley.downTransport (τ := .G2) | exact CFSG.Blueprint.Chevalley.downTransport (τ := .F4) | exact CFSG.Blueprint.Chevalley.downTransport (τ := .D4) | exact CFSG.Blueprint.Chevalley.downTransport (τ := .E6) | exact CFSG.Blueprint.Chevalley.downTransport (τ := .E7) | exact CFSG.Blueprint.Chevalley.downTransport (τ := .E8)

instance hpLieExcChevalleyLiftable : Liftable :=
  ⟨CFSG.LieType.RootSystem.isLiftable⟩

instance hpLieExcChevalleyDescent : Descent :=
  ⟨CFSG.LieType.RootSystem.nonpos_of_isRightDescent, CFSG.LieType.RootSystem.weylAction_injective⟩

instance hpLieExcChevalleyBorelNormal : BorelNormal where
  normal_borelSub_inf_monomialSub := fun τ K _ => by cases τ <;> first | exact CFSG.LieType.Chevalley.normal_borelSub_inf_monomialSub (τ := .G2) (K := K) | exact CFSG.LieType.Chevalley.normal_borelSub_inf_monomialSub (τ := .F4) (K := K) | exact CFSG.LieType.Chevalley.normal_borelSub_inf_monomialSub (τ := .D4) (K := K) | exact CFSG.LieType.Chevalley.normal_borelSub_inf_monomialSub (τ := .E6) (K := K) | exact CFSG.LieType.Chevalley.normal_borelSub_inf_monomialSub (τ := .E7) (K := K) | exact CFSG.LieType.Chevalley.normal_borelSub_inf_monomialSub (τ := .E8) (K := K)

set_option maxHeartbeats 1000000 in -- the copied and the corpus Chevalley groups are compared by unfolding
instance hpLieExcChevalleyChevalley : Chevalley where
  chevalley_split_bn_pair := fun τ K _ => by cases τ <;> first | exact CFSG.LieType.Chevalley.chevalley_split_bn_pair (τ := .G2) (K := K) | exact CFSG.LieType.Chevalley.chevalley_split_bn_pair (τ := .F4) (K := K) | exact CFSG.LieType.Chevalley.chevalley_split_bn_pair (τ := .D4) (K := K) | exact CFSG.LieType.Chevalley.chevalley_split_bn_pair (τ := .E6) (K := K) | exact CFSG.LieType.Chevalley.chevalley_split_bn_pair (τ := .E7) (K := K) | exact CFSG.LieType.Chevalley.chevalley_split_bn_pair (τ := .E8) (K := K)
  center_adjointGroup_eq_bot := fun {τ} => by cases τ <;> first | exact CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) | exact CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .F4) | exact CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .D4) | exact CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E6) | exact CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E7) | exact CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E8)
  finite_modGL := fun {τ} => by cases τ <;> first | exact CFSG.LieType.Chevalley.finite_modGL (τ := .G2) | exact CFSG.LieType.Chevalley.finite_modGL (τ := .F4) | exact CFSG.LieType.Chevalley.finite_modGL (τ := .D4) | exact CFSG.LieType.Chevalley.finite_modGL (τ := .E6) | exact CFSG.LieType.Chevalley.finite_modGL (τ := .E7) | exact CFSG.LieType.Chevalley.finite_modGL (τ := .E8)

instance hpLieExcChevalleyTorusElt : TorusElt where
  torusElt_apply_eq := fun {τ} => by cases τ <;> first | exact CFSG.Blueprint.Chevalley.torusElt_apply_eq (τ := .G2) | exact CFSG.Blueprint.Chevalley.torusElt_apply_eq (τ := .F4) | exact CFSG.Blueprint.Chevalley.torusElt_apply_eq (τ := .D4) | exact CFSG.Blueprint.Chevalley.torusElt_apply_eq (τ := .E6) | exact CFSG.Blueprint.Chevalley.torusElt_apply_eq (τ := .E7) | exact CFSG.Blueprint.Chevalley.torusElt_apply_eq (τ := .E8)

instance hpLieExcChevalleySylowTwo : SylowTwo where
  isSylowTwoOf_posUnipotent := fun {K} _ _ _ τ => by cases τ <;> first | exact CFSG.LieType.Chevalley.isSylowTwoOf_posUnipotent .G2 | exact CFSG.LieType.Chevalley.isSylowTwoOf_posUnipotent .F4 | exact CFSG.LieType.Chevalley.isSylowTwoOf_posUnipotent .D4 | exact CFSG.LieType.Chevalley.isSylowTwoOf_posUnipotent .E6 | exact CFSG.LieType.Chevalley.isSylowTwoOf_posUnipotent .E7 | exact CFSG.LieType.Chevalley.isSylowTwoOf_posUnipotent .E8

instance hpLieExcChevalleyBridges : Bridges :=
  ⟨CFSG.TauCetiBridge.untwistedBridge_G2, CFSG.TauCetiBridge.untwistedBridge_F4, CFSG.TauCetiBridge.untwistedBridge_E6,
    CFSG.TauCetiBridge.untwistedBridge_E7, CFSG.TauCetiBridge.untwistedBridge_E8,
    CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2, CFSG.TauCetiBridge.Even.untwistedBridgeEven_F4,
    CFSG.TauCetiBridge.Even.untwistedBridgeEven_E6, CFSG.TauCetiBridge.Even.untwistedBridgeEven_E7,
    CFSG.TauCetiBridge.Even.untwistedBridgeEven_E8⟩

end CFSGOutsideClean.Corpus
