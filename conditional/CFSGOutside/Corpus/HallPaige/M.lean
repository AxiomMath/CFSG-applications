import CFSGOutside.Corpus.HallPaige.M.Existence
import CFSGOutside.Corpus.HallPaige.M.Monster.B.Rep4371.Model
import CFSGOutside.Corpus.HallPaige.M.Certificates.Data.CFSGNative.MonsterAxis.Basic

/-!
# Corpus input for the Monster

The corpus facts used for `M` (AxiomMath/CFSG @ 69cb972), stated over an abstract copy of the objects
of the Griess–Conway model they mention. The corpus builds the model (`MGriess = AutO`, the extraspecial
group `Q`, the visible pairs `Pvis` and their action `θ`, `ρ`, the triality `τ`) from the Golay code
`C` over the corpus field `F4`, the Parker loop and the spin coordinates. A copy of those structures is
a different type from the corpus one, so a copy of the model cannot be equated with the corpus model;
`GriessModel` therefore lists the objects as data, and `Theorems` says that some instance of the data
satisfies the facts. The clean version instantiates it with the corpus objects
(`CFSGOutsideClean/Corpus/HallPaige/M.lean`). Everything mathematical, the nine triangles, the
counting and the transport to `TauCeti` `M`, is proved in `HallPaige/Sporadic/M*.lean` from these facts.

Kept as copied corpus definitions (`Corpus/HallPaige/M/**`): the orders, the native models
`NativeSporadic.B`, `Fi22`, … with `M = (Y₄₄₃)′`, the Pauli-triple arithmetic `Model.*` and the
short-vector keys `Native.keyAt`, `Native.thetaTab`. The predicates of the existence milestone are in
`Corpus/HallPaige/M/Existence.lean`, with the corpus `LieModel` and `IsElementaryAbelian` as data.
-/

namespace CFSGOutside.Corpus.M

open Monster.Existence Monster.B Monster.AxisCount Open

/-- The objects of the Griess–Conway model that the corpus facts mention, with the corpus name of
each field. -/
structure GriessModel : Type 1 where
  /-- `CFSG.Blueprint.LieModel`, CFSG/Blueprint/Catalog.lean:137. -/
  LieModel : ∀ (X : Type) [Group X], StatedLieTag → ℕ → ℕ → ℕ → Prop
  /-- `CFSG.IsElementaryAbelian`, CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/ElementaryAbelian.lean:28. -/
  IsElementaryAbelian : ℕ → ∀ (X : Type) [Group X], Prop
  /-- `CFSG.Monster.Griess.SpaceB`, CFSG/Monster/Griess/Space.lean:101. -/
  SpaceB : Type
  [instAddCommGroup : AddCommGroup SpaceB]
  [instModule : Module ℚ SpaceB]
  /-- `CFSG.Monster.Griess.AutO`, CFSG/Monster/Griess/AutFinite.lean:16. -/
  AutO : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)
  /-- `CFSG.Monster.Existence.tGriess`, CFSG/Monster/Existence/TwoA.lean:98. -/
  tGriess : ↥AutO
  /-- `CFSG.Monster.Existence.xGriess`, CFSG/Monster/Existence/TwoB.lean:173. -/
  xGriess : ↥AutO
  /-- `↥CFSG.Monster.Code.C`, CFSG/Monster/Code/Defs.lean:84. -/
  C : Type
  [instZeroC : Zero C]
  /-- `CFSG.Monster.Spin.Cocode`, CFSG/Monster/Spin/Pairing.lean:90. -/
  Cocode : Type
  [instZeroCocode : Zero Cocode]
  /-- `CFSG.Monster.B.Rep4371.toC`, CFSG/Monster/B/Rep4371/Bits.lean:118. -/
  toC : ℕ → C
  /-- `CFSG.Monster.B.Rep4371.toD`, CFSG/Monster/B/Rep4371/Bits.lean:176. -/
  toD : ℕ → Cocode
  /-- `CFSG.Monster.Spin.ΩC`, CFSG/Monster/Spin/Pairing.lean:21. -/
  ΩC : C
  /-- `CFSG.Monster.Spin.thetaD`, CFSG/Monster/Spin/Pairing.lean:213. -/
  thetaD : C → Cocode
  /-- `CFSG.Monster.Spin.SpinCoord`, CFSG/Monster/Spin/SpinCoord.lean:27. -/
  SpinCoord : Type
  [instMulSpinCoord : Mul SpinCoord]
  /-- `CFSG.Monster.Spin.SpinCoord.mk` (fields `s`, `a`, `δ`). -/
  spinCoord : ZMod 2 → C → Cocode → SpinCoord
  /-- `↥CFSG.Monster.Spin.Q`, CFSG/Monster/Spin/Defs.lean:182. -/
  Q : Type
  [instGroupQ : Group Q]
  /-- `CFSG.Monster.Spin.spinEquiv`, CFSG/Monster/Spin/Extraspecial.lean:131. -/
  spinEquiv : SpinCoord ≃* Q
  /-- `CFSG.Monster.Code.Parker`, CFSG/Monster/Code/Loop.lean:27. -/
  Parker : Type
  /-- `CFSG.Monster.Code.Parker.mk` (fields `code`, `sign`). -/
  parker : C → ZMod 2 → Parker
  /-- `CFSG.Monster.SpinLattice.XQ`, CFSG/Monster/SpinLattice/Isometry.lean:16. -/
  XQ : Parker → Q
  /-- `↥CFSG.Monster.Visible.Pvis`, CFSG/Monster/Visible/Pair.lean:136. -/
  Pvis : Type
  /-- `CFSG.Monster.Visible.signLiftPair`, CFSG/Monster/Visible/SignCompat/Labels.lean:18. -/
  signLiftPair : Parker → Pvis
  /-- `CFSG.Monster.Visible.thetaEquiv`, CFSG/Monster/Visible/Pair.lean:375. -/
  thetaEquiv : Pvis → SpaceB ≃ₗ[ℚ] SpaceB
  /-- `CFSG.Monster.Visible.conjQ`, CFSG/Monster/Visible/Pair.lean:164. -/
  conjQ : Pvis → Q ≃* Q
  /-- `CFSG.Monster.Visible.rhoEquiv`, CFSG/Monster/Visible/Action.lean:447. -/
  rhoEquiv : Q → SpaceB ≃ₗ[ℚ] SpaceB
  /-- `CFSG.Monster.Griess.tauB`, CFSG/Monster/Griess/TrialityMatrix.lean:172. -/
  tauB : SpaceB ≃ₗ[ℚ] SpaceB
  /-- `CFSG.Monster.Griess.xB`, CFSG/Monster/Griess/Parity.lean:20. -/
  xB : SpaceB ≃ₗ[ℚ] SpaceB
  /-- `CFSG.Monster.Griess.IsShortCoord`, CFSG/Monster/Griess/Short.lean:15. -/
  IsShortCoord : C × Cocode → Prop
  /-- `CFSG.Monster.Griess.coordOf`, CFSG/Monster/Griess/Short.lean:20. -/
  coordOf : Q → C × Cocode
  /-- `CFSG.Monster.AxisCount.keyOf`, CFSG/Monster/AxisCount/DenseIndex.lean:151. -/
  keyOf : ℕ → ℕ × ℕ

namespace GriessModel

attribute [instance] instAddCommGroup instModule instZeroC instZeroCocode instMulSpinCoord instGroupQ

variable (d : GriessModel)

/-- Corpus: `CFSG.Monster.Existence.MGriess`, CFSG/Monster/Existence/Defs.lean:14. -/
abbrev MGriess : Type := ↥d.AutO

/-- Corpus: `CFSG.Monster.B.Rep4371.boolZ`, CFSG/Monster/B/Rep4371/Bits.lean:16. -/
def boolZ (b : Bool) : ZMod 2 := if b then 1 else 0

/-- Corpus: `CFSG.Monster.B.Rep4371.toSC`, CFSG/Monster/B/Rep4371/Bits.lean:345. -/
def toSC (x : Model.Pauli) : d.SpinCoord := d.spinCoord (boolZ x.s) (d.toC x.a) (d.toD x.d)

/-- Corpus: `CFSG.Monster.B.Rep4371.pauliQ`, CFSG/Monster/B/Rep4371/Bits.lean:359. -/
def pauliQ (x : Model.Pauli) : d.Q := d.spinEquiv (d.toSC x)

/-- Corpus: `CFSG.Monster.Spin.zQ`, CFSG/Monster/Spin/Extraspecial.lean:136 (with `SpinCoord.z`,
CFSG/Monster/Spin/SpinCoord.lean:85). -/
def zQ : d.Q := d.spinEquiv (d.spinCoord 1 0 0)

/-- Corpus: `CFSG.Monster.B.wQ`, CFSG/Monster/B/Cbar/FourGroupSpin.lean:16. -/
def wQ : d.Q := d.XQ (d.parker d.ΩC 0)

/-- Corpus: `CFSG.Monster.Generated.xmat`, CFSG/Monster/Generated/Data.lean:22. -/
def xmat : d.SpaceB ≃ₗ[ℚ] d.SpaceB := d.rhoEquiv d.zQ

/-- Corpus: `CFSG.Monster.Griess.yB`, CFSG/Monster/Griess/FourGroup.lean:122. -/
def yB : d.SpaceB ≃ₗ[ℚ] d.SpaceB := d.tauB * d.xB * d.tauB⁻¹

/-- Corpus: `CFSG.Monster.Griess.zB`, CFSG/Monster/Griess/FourGroup.lean:124. -/
def zB : d.SpaceB ≃ₗ[ℚ] d.SpaceB := d.tauB ^ 2 * d.xB * (d.tauB ^ 2)⁻¹

/-- The corpus facts on the Griess–Conway model. Each field is the corpus statement with the model
objects read in `d`; the fields after `iso_y443Derived_tauCeti` restate corpus definitions and
membership lemmas that the copied model would have provided by unfolding. -/
class Facts : Prop where
  /-- Corpus (literature milestone): `CFSG.Milestones.cl_lit_monster_existence_griess_conway`,
  CFSG/Milestones/CL_LIT_Monster_existence_Griess_Conway.lean:44. -/
  cl_lit_monster_existence_griess_conway :
    MonsterExistenceStatement d.LieModel d.IsElementaryAbelian d.MGriess
  /-- Corpus: `CFSG.YGroups.Y443.monster_clauses_MGriess`, CFSG/YGroups/Y443/Tri/AssemblyLit.lean:20. -/
  monster_clauses_MGriess :
    Nat.card d.MGriess = monsterOrder ∧
      (∀ s : d.MGriess, orderOf s = 2 → IsConj d.tGriess s ∨ IsConj d.xGriess s) ∧
      IsTwoACentralizer d.tGriess
  /-- Corpus: `CFSG.Monster.Existence.card_nativeB`, CFSG/Monster/Existence/BabyOrder.lean:37. -/
  card_nativeB :
    Nat.card CFSGOutside.Corpus.M.Blueprint.NativeSporadic.B = CFSGOutside.Corpus.M.Open.monsterBabyOrder
  /-- Corpus: `CFSG.Sporadic.Fi22.card_Fi22`, CFSG/Sporadic/Fi22/Simple.lean:528. -/
  card_Fi22 :
    Nat.card Blueprint.NativeSporadic.Fi22 = 64561751654400
  /-- Corpus: `CFSG.Monster.Existence.not_isConj_xGriess_tGriess`,
  CFSG/Monster/Existence/InvolutionClasses.lean:32. -/
  not_isConj_xGriess_tGriess : ¬ IsConj d.xGriess d.tGriess
  /-- Corpus: `CFSG.Monster.Existence.orderOf_xGriess`, CFSG/Monster/Existence/Simple.lean:129. -/
  orderOf_xGriess : orderOf d.xGriess = 2
  /-- Corpus: `CFSG.Monster.Existence.shapeSix_isConj_tGriess_of_trace`,
  CFSG/Monster/Existence/TwoPoint/ShapeSixLift.lean:26. -/
  shapeSix_isConj_tGriess_of_trace
    {g : d.MGriess} (hg : orderOf g = 2)
    (htr : LinearMap.trace ℚ d.SpaceB ((g : d.SpaceB ≃ₗ[ℚ] d.SpaceB) : d.SpaceB →ₗ[ℚ] d.SpaceB) = 4372) :
    IsConj d.tGriess g
  /-- Corpus: `CFSG.Monster.B.trace_rho_short`, CFSG/Monster/B/Cbar/Fusion.lean:278. -/
  trace_rho_short {r : d.Q} (hr : d.IsShortCoord (d.coordOf r)) :
    LinearMap.trace ℚ d.SpaceB (d.rhoEquiv r : d.SpaceB →ₗ[ℚ] d.SpaceB) = 4372
  /-- Corpus: `CFSG.Monster.Visible.thetaEquiv_signLiftPair`,
  CFSG/Monster/Visible/SignCompat/Triality.lean:362. -/
  thetaEquiv_signLiftPair (e : d.Parker) :
    d.thetaEquiv (d.signLiftPair e) = d.tauB * d.rhoEquiv (d.XQ e) * d.tauB⁻¹
  /-- Corpus: `CFSG.Monster.Visible.thetaEquiv_conj_rhoEquiv`, CFSG/Monster/Visible/Faithful.lean:119. -/
  thetaEquiv_conj_rhoEquiv (p : d.Pvis) (t : d.Q) :
    d.thetaEquiv p * d.rhoEquiv t * (d.thetaEquiv p)⁻¹ = d.rhoEquiv (d.conjQ p t)
  /-- Corpus: `CFSG.Monster.B.Rep4371.conjQ_sign_toQ`, CFSG/Monster/B/Rep4371/Conj.lean:129. Its pair
  `⟨(YU ⟨toC a, 0⟩, gO (toC a)), _⟩` is `signLiftPair ⟨toC a, 0⟩` by definition
  (CFSG/Monster/Visible/SignCompat/Labels.lean:18). -/
  conjQ_sign_toQ (a : ℕ) (y : Model.Pauli) :
    d.conjQ (d.signLiftPair (d.parker (d.toC a) 0)) (d.pauliQ y) = d.pauliQ (Model.conjYN a y)
  /-- Corpus: `CFSG.Monster.Visible.rhoEquiv_mul`, CFSG/Monster/Visible/Action.lean:453. -/
  rhoEquiv_mul (r r' : d.Q) : d.rhoEquiv (r * r') = d.rhoEquiv r' * d.rhoEquiv r
  /-- Corpus: `CFSG.Monster.Visible.rhoEquiv_injective`, CFSG/Monster/Visible/Action.lean:469. -/
  rhoEquiv_injective : Function.Injective d.rhoEquiv
  /-- Corpus: `CFSG.Monster.B.Rep4371.pauliQ_mul`, CFSG/Monster/B/Rep4371/Bits.lean:361. -/
  pauliQ_mul (x y : Model.Pauli) : d.pauliQ (x.mul y) = d.pauliQ x * d.pauliQ y
  /-- Corpus: `CFSG.Monster.B.Rep4371.thetaD_toC`, CFSG/Monster/B/Rep4371/Bits.lean:330. -/
  thetaD_toC (a : ℕ) : d.thetaD (d.toC a) = d.toD (Model.thetaN a)
  /-- Corpus: `CFSG.Monster.B.Rep4371.ΩC_eq_toC`, CFSG/Monster/B/Rep4371/Bits.lean:225. -/
  ΩC_eq_toC : d.ΩC = d.toC 63
  /-- Corpus: `CFSG.Monster.B.Rep4371.toC_zero`, CFSG/Monster/B/Rep4371/Bits.lean:134. -/
  toC_zero : d.toC 0 = 0
  /-- Corpus: `CFSG.Monster.B.Rep4371.toD_zero`, CFSG/Monster/B/Rep4371/Bits.lean:207. -/
  toD_zero : d.toD 0 = 0
  /-- Corpus: `CFSG.Monster.AxisCount.key_short`, CFSG/Monster/AxisCount/DenseInterp.lean:17. -/
  key_short
    (p : ℕ) (hp : p < 98280) : d.IsShortCoord (d.toC (d.keyOf p).1, d.toD (d.keyOf p).2)
  /-- Corpus: `CFSG.Monster.AxisCount.keyOf_eq`, CFSG/Monster/AxisCount/DenseIndex.lean:166. -/
  keyOf_eq (p : ℕ) (hp : p < 98280) : d.keyOf p = Native.keyAt (Native.thetaTab ()) p
  /-- Corpus: `CFSG.Monster.AxisCount.coordOf_pauliQ`, CFSG/Monster/AxisCount/DenseShort.lean:17. -/
  coordOf_pauliQ (y : Model.Pauli) : d.coordOf (d.pauliQ y) = (d.toC y.a, d.toD y.d)
  /-- Corpus: `CFSG.Monster.B.Short.ne_one_of_isShortCoord`, CFSG/Monster/B/Short/ParityJ.lean:188. -/
  ne_one_of_isShortCoord {r : d.Q} (hr : d.IsShortCoord (d.coordOf r)) : r ≠ 1
  /-- Corpus: `CFSG.Monster.B.rhoEquiv_wQ`, CFSG/Monster/B/Cbar/FourGroupSpin.lean:160. -/
  rhoEquiv_wQ : d.rhoEquiv d.wQ = d.zB
  /-- Corpus: `CFSG.Monster.B.rhoEquiv_zQ_wQ`, CFSG/Monster/B/Cbar/FourGroupSpin.lean:166. -/
  rhoEquiv_zQ_wQ : d.rhoEquiv (d.zQ * d.wQ) = d.yB
  /-- Corpus: `CFSG.Monster.Generated.xmat_eq_xB`, CFSG/Monster/Generated/Data.lean:30. -/
  xmat_eq_xB : d.xmat = d.xB
  /-- Corpus: `CFSG.Monster.B.pauliQ_zero`, CFSG/Monster/B/Final/Max2Nodes.lean:61. -/
  pauliQ_zero : d.pauliQ (false, 0, 0) = 1
  /-- Corpus: `CFSG.Blueprint.NativeSporadic.MonsterModel.iso_griess_y443Derived`,
  CFSG/Sporadic/Bridge/MonsterModelsGriess.lean:44, with `Iso` and the carriers unfolded
  (CFSG/Sporadic/Bridge/MonsterModels.lean:11, CFSG/Blueprint/MonsterModels.lean:19). -/
  iso_griess_y443Derived :
    Nonempty (d.MGriess ≃* Blueprint.NativeSporadic.M)
  /-- Corpus: `CFSG.Blueprint.NativeSporadic.MonsterModel.iso_y443Derived_tauCeti`,
  CFSG/Sporadic/Bridge/MonsterModels.lean:31, unfolded likewise. -/
  iso_y443Derived_tauCeti :
    Nonempty (Blueprint.NativeSporadic.M ≃* TauCeti.SporadicName.M.Group)
  /-- Corpus: `CFSG.Monster.SpinLattice.XQ_eq`, CFSG/Monster/SpinLattice/Isometry.lean:20, at
  `e = ⟨c, s⟩`. -/
  XQ_eq (c : d.C) (s : ZMod 2) : d.XQ (d.parker c s) = d.spinEquiv (d.spinCoord s c (d.thetaD c))
  /-- Corpus definitions `CFSG.Monster.Existence.xGriess` (CFSG/Monster/Existence/TwoB.lean:173,
  `⟨xmat, xmat_mem_AutO⟩`) and `xmat` (CFSG/Monster/Generated/Data.lean:22). -/
  coe_xGriess : (d.xGriess : d.SpaceB ≃ₗ[ℚ] d.SpaceB) = d.xmat
  /-- Corpus: `CFSG.Monster.Griess.tauB_mem_AutO`, CFSG/Monster/Griess/AutFinite.lean:30. -/
  tauB_mem_AutO : d.tauB ∈ d.AutO
  /-- Corpus: `CFSG.Monster.Generated.Gmat_le_AutO` (CFSG/Monster/Generated/Centralizer.lean:21),
  `Hmat_le_Gmat` (CFSG/Monster/Generated/Data.lean:41) and `CFSG.Monster.Visible.thetaEquiv_mem_Gvis`
  (CFSG/Monster/Visible/Action.lean:365). -/
  thetaEquiv_mem_AutO (p : d.Pvis) : d.thetaEquiv p ∈ d.AutO
  /-- The same three lemmas, with `rhoEquiv r = thetaEquiv (rhoPair r)` by definition
  (CFSG/Monster/Visible/Action.lean:447). -/
  rhoEquiv_mem_AutO (r : d.Q) : d.rhoEquiv r ∈ d.AutO

end GriessModel

/-- The corpus theorems for `M`: the Griess–Conway model satisfies `GriessModel.Facts`. -/
class Theorems : Prop where
  exists_griessModel : ∃ d : GriessModel, d.Facts

end CFSGOutside.Corpus.M
