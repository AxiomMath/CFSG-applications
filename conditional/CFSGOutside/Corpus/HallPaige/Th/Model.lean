import Mathlib
import CFSGOutside.Corpus.HallPaige.Th.Kernel

/-!
# Copied corpus definitions: the action of `GL₂₄₈(𝔽₂)` on subspaces and the Dempwolff structures

Definitions copied verbatim from AxiomMath/CFSG @ 69cb972 by
a generator script (each docstring names the corpus declaration and
file:line; the `MulAction` instance comes with its corpus proof). The corpus namespaces `CFSG.X` are
mapped to `CFSGOutside.Corpus.Th.X`; `open` lists only the copied namespaces.
-/

set_option autoImplicit false


namespace CFSGOutside.Corpus.Th.Certificates.ThDemp

/-- Corpus: `CFSG.Certificates.ThDemp.Coords`, CFSG/Certificates/Kernel/ThDemp/ChainExBase.lean:17. -/
abbrev Coords := Fin 31 × Fin 30 × Fin 28 × Fin 24 × Fin 16 × Fin 32

/-- Corpus: `CFSG.Certificates.ThDemp.chainProd`, CFSG/Certificates/Kernel/ThDemp/ChainExBase.lean:19. -/
def chainProd {G : Type*} [Group G] (t : ℕ → ℕ → G) (y : Coords) : G :=
  t 5 y.2.2.2.2.2 * t 4 y.2.2.2.2.1 * t 3 y.2.2.2.1 * t 2 y.2.2.1 * t 1 y.2.1 * t 0 y.1

end CFSGOutside.Corpus.Th.Certificates.ThDemp

namespace CFSGOutside.Corpus.Th.Certificates.ThDemp.Key

open CFSGOutside.Corpus.Th.KC.Th CFSGOutside.Corpus.Th.KC.Th.BigS CFSGOutside.Corpus.Th.KC.Th.Spec CFSGOutside.Corpus.Th.KC.ThDemp

/-- Corpus: `CFSG.Certificates.ThDemp.Key.spanL`, CFSG/Certificates/Kernel/ThDemp/Key.lean:40. -/
def spanL (l : List ℕ) : Submodule (ZMod 2) (Fin 248 → ZMod 2) :=
  Submodule.span (ZMod 2) {v | ∃ b ∈ l, v = pkVec b}

/-- Corpus: `CFSG.Certificates.ThDemp.Key.LIL`, CFSG/Certificates/Kernel/ThDemp/Key.lean:71. -/
def LIL : List ℕ → Prop
  | [] => True
  | b :: l => pkVec b ∉ spanL l ∧ LIL l

end CFSGOutside.Corpus.Th.Certificates.ThDemp.Key

namespace CFSGOutside.Corpus.Th.Certificates.ThDemp.Act

open CFSGOutside.Corpus.Th.KC.Th CFSGOutside.Corpus.Th.KC.Th.BigS CFSGOutside.Corpus.Th.KC.Th.Spec CFSGOutside.Corpus.Th.KC.ThDemp Key

/-- Corpus: `CFSG.Certificates.ThDemp.Act.V`, CFSG/Certificates/Kernel/ThDemp/Action.lean:13. -/
abbrev V := Fin 248 → ZMod 2

/-- Corpus: `CFSG.Certificates.ThDemp.Act.Pts`, CFSG/Certificates/Kernel/ThDemp/Action.lean:15. -/
abbrev Pts : Type := Submodule (ZMod 2) V

/-- Corpus: `CFSG.Certificates.ThDemp.Act.mapM`, CFSG/Certificates/Kernel/ThDemp/Action.lean:17. -/
def mapM (M : Matrix (Fin 248) (Fin 248) (ZMod 2)) (W : Pts) : Pts :=
  Submodule.map (Matrix.vecMulLinear M) W

/-- Corpus: `CFSG.Certificates.ThDemp.Act.mapM_one`, CFSG/Certificates/Kernel/ThDemp/Action.lean:20. -/
theorem mapM_one (W : Pts) : mapM 1 W = W := by
  change Submodule.map (Matrix.vecMulLinear 1) W = W
  have : Matrix.vecMulLinear (1 : Matrix (Fin 248) (Fin 248) (ZMod 2)) = LinearMap.id := by
    ext v
    simp [Matrix.vecMulLinear]
  rw [this, Submodule.map_id]

/-- Corpus: `CFSG.Certificates.ThDemp.Act.mapM_mul`, CFSG/Certificates/Kernel/ThDemp/Action.lean:27. -/
theorem mapM_mul (M N : Matrix (Fin 248) (Fin 248) (ZMod 2)) (W : Pts) :
    mapM (M * N) W = mapM N (mapM M W) := by
  change Submodule.map (Matrix.vecMulLinear (M * N)) W =
    Submodule.map (Matrix.vecMulLinear N) (Submodule.map (Matrix.vecMulLinear M) W)
  have e : Matrix.vecMulLinear (M * N) = (Matrix.vecMulLinear N).comp (Matrix.vecMulLinear M) :=
    LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, Matrix.vecMulLinear_apply, Matrix.vecMulLinear_apply,
        Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul]
  rw [e, Submodule.map_comp]

instance : MulAction (GL (Fin 248) (ZMod 2)) Pts where
  smul g W := mapM ((g⁻¹ : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2)) W
  one_smul W := by
    change mapM _ W = W
    rw [inv_one, Units.val_one, mapM_one]
  mul_smul g h W := by
    change mapM _ W = mapM _ (mapM _ W)
    rw [mul_inv_rev, Units.val_mul, mapM_mul]

/-- Corpus: `CFSG.Certificates.ThDemp.Act.smul_def`, CFSG/Certificates/Kernel/ThDemp/Action.lean:46. -/
theorem smul_def (g : GL (Fin 248) (ZMod 2)) (W : Pts) :
    g • W = mapM ((g⁻¹ : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2)) W := rfl

/-- Corpus: `CFSG.Certificates.ThDemp.Act.smul_eq_self_iff`, CFSG/Certificates/Kernel/ThDemp/Action.lean:49. -/
theorem smul_eq_self_iff (g : GL (Fin 248) (ZMod 2)) (W : Pts) :
    g • W = W ↔ mapM (g : Matrix (Fin 248) (Fin 248) (ZMod 2)) W = W := by
  rw [smul_def]
  constructor
  · intro h
    conv_lhs => rw [← h]
    rw [← mapM_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, mapM_one]
  · intro h
    conv_lhs => rw [← h]
    rw [← mapM_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, mapM_one]

/-- Corpus: `CFSG.Certificates.ThDemp.Act.smul_eq_iff`, CFSG/Certificates/Kernel/ThDemp/Action.lean:60. -/
theorem smul_eq_iff (g : GL (Fin 248) (ZMod 2)) (W W' : Pts) :
    g • W = W' ↔ W = mapM (g : Matrix (Fin 248) (Fin 248) (ZMod 2)) W' := by
  rw [smul_def]
  constructor
  · rintro rfl
    rw [← mapM_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, mapM_one]
  · rintro rfl
    rw [← mapM_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, mapM_one]

/-- Corpus: `CFSG.Certificates.ThDemp.Act.sp`, CFSG/Certificates/Kernel/ThDemp/Action.lean:69. -/
noncomputable def sp (P : ℕ) : Pts := spanL (rowsOf (2 ^ 248 - 1) P)

end CFSGOutside.Corpus.Th.Certificates.ThDemp.Act

namespace CFSGOutside.Corpus.Th.Certificates.ThDemp.Stab

open MulAction CFSGOutside.Corpus.Th.KC.Th CFSGOutside.Corpus.Th.KC.Th.BigS CFSGOutside.Corpus.Th.KC.Th.Spec CFSGOutside.Corpus.Th.KC.ThDemp CFSGOutside.Corpus.Th.Certificates.ThDemp.Act CFSGOutside.Corpus.Th.Certificates.ThDemp.Key

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

variable {J : Subgroup (GL (Fin 248) (ZMod 2))}

/-- Corpus: `CFSG.Certificates.ThDemp.Stab.inv_smul_eq`, CFSG/Certificates/Kernel/ThDemp/OrbStab.lean:23. -/
theorem inv_smul_eq (g : J) (W : Pts) : g⁻¹ • W = mapM (𝕄 g) W := by
  rw [Subgroup.smul_def, Subgroup.coe_inv, Act.smul_def, inv_inv]

/-- Corpus: `CFSG.Certificates.ThDemp.Stab.smul_eq_mapM`, CFSG/Certificates/Kernel/ThDemp/OrbStab.lean:26. -/
theorem smul_eq_mapM (g : J) (W : Pts) : g • W = mapM (𝕄 g⁻¹) W := by
  conv_lhs => rw [← inv_inv g]
  exact inv_smul_eq g⁻¹ W

/-- Corpus: `CFSG.Certificates.ThDemp.Stab.mat_mul'`, CFSG/Certificates/Kernel/ThDemp/OrbStab.lean:30. -/
theorem mat_mul' (g h : J) : 𝕄 (g * h) = 𝕄 g * 𝕄 h := by
  rw [Subgroup.coe_mul, Units.val_mul]

/-- Corpus: `CFSG.Certificates.ThDemp.Stab.mat_mul_inv`, CFSG/Certificates/Kernel/ThDemp/OrbStab.lean:33. -/
theorem mat_mul_inv (g : J) : 𝕄 g * 𝕄 g⁻¹ = 1 := by
  rw [← mat_mul', mul_inv_cancel, Subgroup.coe_one, Units.val_one]

/-- Corpus: `CFSG.Certificates.ThDemp.Stab.mat_inv_mul`, CFSG/Certificates/Kernel/ThDemp/OrbStab.lean:36. -/
theorem mat_inv_mul (g : J) : 𝕄 g⁻¹ * 𝕄 g = 1 := by
  rw [← mat_mul', inv_mul_cancel, Subgroup.coe_one, Units.val_one]

/-- Corpus: `CFSG.Certificates.ThDemp.Stab.Ctx`, CFSG/Certificates/Kernel/ThDemp/OrbStab.lean:39. -/
structure Ctx (D : DempData) (O : OrbData) (J : Subgroup (GL (Fin 248) (ZMod 2))) where
  d₀ : J
  d₁ : J
  t : ℕ → ℕ → J
  mem : ∀ l < 6, ∀ i < D.oszL l, t l i ∈ Subgroup.closure ({d₀, d₁} : Set J)
  mat : ∀ l < 6, ∀ i < D.oszL l, 𝕄 (t l i) = pkMat (D.T l i)
  uniq : ∀ x ∈ Subgroup.closure ({d₀, d₁} : Set J), ∃! y : Coords, chainProd t y = x
  inv : ∀ l < 3, ∀ i < D.oszL l, pkMat (O.TI l i) = 𝕄 (t l i)⁻¹
  osz : D.oszL 0 = 31 ∧ D.oszL 1 = 30 ∧ D.oszL 2 = 28 ∧ D.oszL 3 = 24 ∧ D.oszL 4 = 16 ∧
    D.oszL 5 = 32
  md₀ : 𝕄 d₀ = pkMat (gen D 0)
  md₁ : 𝕄 d₁ = pkMat (gen D 1)
  lev5 : ∀ x ∈ Subgroup.closure ({d₀, d₁} : Set J),
    (∀ l < 5, Matrix.vecMul (pkVec (D.bvL l)) (𝕄 x) = pkVec (D.bvL l)) → ∃ z < 32, x = t 5 z

namespace Ctx

variable {D : DempData} {O : OrbData} (C : Ctx D O J)

/-- Corpus: `CFSG.Certificates.ThDemp.Stab.Ctx.Dg`, CFSG/Certificates/Kernel/ThDemp/OrbStab.lean:58. -/
abbrev Dg : Subgroup J := Subgroup.closure ({C.d₀, C.d₁} : Set J)

end Ctx
end CFSGOutside.Corpus.Th.Certificates.ThDemp.Stab

namespace CFSGOutside.Corpus.Th.Certificates.ThDemp.Pts

open MulAction CFSGOutside.Corpus.Th.KC.Th CFSGOutside.Corpus.Th.KC.Th.BigS CFSGOutside.Corpus.Th.KC.Th.Spec CFSGOutside.Corpus.Th.KC.ThDemp CFSGOutside.Corpus.Th.Certificates.ThDemp.Act CFSGOutside.Corpus.Th.Certificates.ThDemp.Key CFSGOutside.Corpus.Th.Certificates.ThDemp.Stab CFSGOutside.Corpus.Th.KC.Loop

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

/-- Corpus: `CFSG.Certificates.ThDemp.Pts.RegJ`, CFSG/Certificates/Kernel/ThDemp/OrbPtsBase.lean:22. -/
def RegJ (D : DempData) (J : Subgroup (GL (Fin 248) (ZMod 2))) : Prop :=
  ∀ r, 0 < r → r < D.nreg → ∃ x : J, 𝕄 x = pkMat (D.RB r)

end CFSGOutside.Corpus.Th.Certificates.ThDemp.Pts

namespace CFSGOutside.Corpus.Th.Certificates.ThDemp.OrbMain

open MulAction

/-- Corpus: `CFSG.Certificates.ThDemp.OrbMain.sOf`, CFSG/Certificates/Kernel/ThDemp/OrbMain.lean:21. -/
def sOf : Fin 9 → ℕ := ![5376, 126, 48, 9, 3, 5, 5, 155, 155]

/-- Corpus: `CFSG.Certificates.ThDemp.OrbMain.SuborbitHyp`, CFSG/Certificates/Kernel/ThDemp/OrbMain.lean:23. -/
structure SuborbitHyp {G X : Type*} [Group G] [MulAction G X] [Finite G] (D : Subgroup G) (u : X)
    (p : Fin 10 → X) : Prop where
  cardG : Nat.card G ≤ 90745943887872000
  cardD : Nat.card D = 319979520
  fixD : D ≤ stabilizer G u
  mem : ∀ i, p i ∈ orbit G u
  stab : ∀ i : Fin 9, Nat.card (stabilizer D (p i.castSucc)) = sOf i
  orb9 : (orbit D (p 9)).ncard = 248
  dis56 : p 6 ∉ orbit D (p 5)
  dis78 : p 8 ∉ orbit D (p 7)

variable {G X : Type*} [Group G] [MulAction G X] [Finite G] {D : Subgroup G} {u : X}
  {p : Fin 10 → X}

/-- Corpus: `CFSG.Certificates.ThDemp.OrbMain.pts`, CFSG/Certificates/Kernel/ThDemp/OrbMain.lean:37. -/
def pts (u : X) (p : Fin 10 → X) : Fin 11 → X := Fin.cons u p

/-- Corpus: `CFSG.Certificates.ThDemp.OrbMain.oSize`, CFSG/Certificates/Kernel/ThDemp/OrbMain.lean:39. -/
def oSize : Fin 11 → ℕ :=
  ![1, 59520, 2539520, 6666240, 35553280, 106659840, 63995904, 63995904, 2064384, 2064384, 248]

end CFSGOutside.Corpus.Th.Certificates.ThDemp.OrbMain

namespace CFSGOutside.Corpus.Th.Certificates.ThDemp

open CFSGOutside.Corpus.Th.KC.Th CFSGOutside.Corpus.Th.KC.Th.BigS CFSGOutside.Corpus.Th.KC.Th.Spec CFSGOutside.Corpus.Th.KC.ThDemp

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

/-- Corpus: `CFSG.Certificates.ThDemp.DempFacts`, CFSG/Certificates/Kernel/ThDemp/Sound.lean:22. -/
structure DempFacts (D : DempData) : Prop where
  consts : constsOK D.c D.rm D.tm0 D.tm1 D.tm2 D.tm3 D.tm4 D.tm5 D.tm6 D.tm7 D.up D.dg D.ONE = true
  rb1 : D.RB 1 = D.SA
  rb2 : D.RB 2 = D.SB
  slp1 : runSlp D.RB D.c D.rm D.ONE D.cs1 3 = D.r1
  slp2 : runSlp D.RB D.c D.rm D.ONE D.cs2 D.r1 = D.nreg
  nreg_lt : D.nreg < 2048
  rd : ∀ k < 2, 0 < regAt D.rd k ∧ regAt D.rd k < D.r1
  pr : ∀ g < D.npr, 0 < regAt D.pr g ∧ regAt D.pr g < D.nreg
  npr2 : 2 ≤ D.npr
  pr0 : regAt D.pr 0 = regAt D.rd 0
  pr1 : regAt D.pr 1 = regAt D.rd 1
  marks_ok : ∀ g < D.npr,
    marked (runMarked D.cs2 (D.r1 + 2048 * D.marks) / 2048) (regAt D.pr g) = true
  L6 : D.L = 6
  osz : D.oszL 0 = 31 ∧ D.oszL 1 = 30 ∧ D.oszL 2 = 28 ∧ D.oszL 3 = 24 ∧ D.oszL 4 = 16 ∧
    D.oszL 5 = 32
  fr0 : D.frL 0 = 0
  frL : D.frL D.L = D.npr
  mono : ∀ l < D.L, D.frL l ≤ D.frL (l + 1)
  bv_lt : ∀ l < D.L, D.bvL l < 2 ^ 248
  P0 : ∀ l < D.L, D.P l 0 = D.bvL l
  tr0 : ∀ l < D.L, D.trR l 0 = 0
  tree : ∀ l < D.L, ∀ i, 0 < i → i < D.oszL l → ∃ par g, par < i ∧ D.frL l ≤ g ∧ g < D.npr ∧
    0 < D.trR l i ∧ D.trR l i < D.nreg ∧ D.RB (D.trR l i) = D.mul (D.T l par) (D.S g) ∧
    D.P l i = vecB D.rm (D.P l par) (D.S g)
  inj : ∀ l < D.L, ∀ i j, i < D.oszL l → j < D.oszL l → D.P l i = D.P l j → i = j
  fix : ∀ l < D.L, ∀ g, D.frL (l + 1) ≤ g → g < D.npr → vecB D.rm (D.bvL l) (D.S g) = D.bvL l
  res : ∀ l < D.L, ∀ i < D.oszL l, ∀ g, D.frL l ≤ g → g < D.npr → ∃ z < D.oszL l, ∃ e : ℕ,
    (∀ q, l + 1 + q < D.L → bitsN e (8 * (q + 1)) 8 < D.oszL (l + 1 + q)) ∧
    D.mul (D.T l i) (D.S g) = D.sift l e (D.T l z)


end CFSGOutside.Corpus.Th.Certificates.ThDemp

namespace CFSGOutside.Corpus.Th.Certificates.ThDemp.Bound

open MulAction CFSGOutside.Corpus.Th.KC.Th CFSGOutside.Corpus.Th.KC.Th.BigS CFSGOutside.Corpus.Th.KC.Th.Spec CFSGOutside.Corpus.Th.KC.ThDemp CFSGOutside.Corpus.Th.KC.Loop CFSGOutside.Corpus.Th.Certificates.ThDemp.Act CFSGOutside.Corpus.Th.Certificates.ThDemp.Key CFSGOutside.Corpus.Th.Certificates.ThDemp.Stab CFSGOutside.Corpus.Th.Certificates.ThDemp.Pts

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

variable {J : Subgroup (GL (Fin 248) (ZMod 2))} {D : DempData} {O : OrbData}

/-- Corpus: `CFSG.Certificates.ThDemp.Bound.OrbChecks`, CFSG/Certificates/Kernel/ThDemp/OrbBoundBase.lean:24. -/
structure OrbChecks (D : DempData) (O : OrbData) : Prop where
  inv : invChk D O = true
  batch : ∀ i < 9, ∀ y3 < 24, batchChk D O i y3 = true
  cross56 : ∀ y3 < 24, crossChk D O 5 6 y3 = true
  cross78 : ∀ y3 < 24, crossChk D O 7 8 y3 = true
  ky : ∀ i < 9, kyChk D O i = true
  low : ∀ i < 9, lowChk D O i = true
  orb : orbChk D O = true
  codes : codesChk D O = true
  elt1 : eltChk1 D O = true
  cent : centChk D O = true
  q : qChk D O = true
  norm : normChk D O = true
  sb : ∀ i : Fin 9, lget O.sb i = OrbMain.sOf i
  w9 : lgetL O.words 9 ≠ []

end CFSGOutside.Corpus.Th.Certificates.ThDemp.Bound
