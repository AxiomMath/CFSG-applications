import CFSGOutside.Corpus.HallPaige.Th.Setup
import CFSGOutside.Corpus.HallPaige.Th.Model
import CFSGOutside.Corpus.HallPaige.Th.Data
import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

/-!
# Corpus input for the Thompson group

The corpus theorems used for `Th` (AxiomMath/CFSG @ 69cb972), stated as fields of classes with their
exact statements, over the copied definitions of `CFSGOutside.Corpus.Th` (`Th/Setup.lean`,
`Th/Kernel.lean`, `Th/Model.lean`, `Th/Data.lean`). They describe the action of the 248-dimensional
model `J = ⟨gA, gB⟩ ≤ GL₂₄₈(𝔽₂)` on the `J`-orbit of the 5-dimensional subspace `sp (U0 dempData)`,
whose stabilizer is the Dempwolff group `Dg = 2⁵·L₅(2)` (rank 11, degree 283599225):

* `Seed`: `matA * matA = 1`, `matB ^ 3 = 1` (in `Th/Setup.lean`; needed to define `J`);
* `Theorems`:
  - `nonempty_mulEquiv`, `card_J`: the model is the presented group `Th`, of order 90745943887872000;
  - `dempChk_facts`, `demp_chk`, `exists_chain`, `invChk_sound`, `pkMat_SA`, `pkMat_SB`: the
    certified chain of `Dg = ⟨d₀, d₁⟩` (the corpus assembly `th_centralizer_bounds`,
    Certificates/Kernel/ThDemp/OrbAssembly.lean:39, builds the context `Stab.Ctx` from these);
  - `orb_checks`, `suborbitHyp`: the suborbit data of `Dg` on the orbit (`OrbMain.SuborbitHyp`);
  - `pkMat_mulB`, `pkMat_one`, `sp_mulB`, `sp_le_of_combChk`: packed-matrix and span lemmas;
* `Generic`: `SuborbitHyp.cover`, the stabilizer is `Dg` and the 11 `Dg`-orbits cover the orbit.
-/

namespace CFSGOutside.Corpus.Th

open MulAction KC.Th KC.Th.BigS KC.Th.Spec KC.ThDemp Certificates.ThDemp Certificates.ThDemp.Act
  Certificates.ThDemp.Key Certificates.ThDemp.Stab Certificates.ThDemp.Pts Sporadic.Th
  KernelThDemp

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

/-- The corpus theorems for `Th` in the Dempwolff model. -/
class Theorems : Prop where
  /-- Corpus: `CFSG.Sporadic.Th.matA_mul_self`, `matB_cube`, CFSG/Sporadic/Th/Setup.lean:51, :55. -/
  seed : Seed
  /-- Corpus: `CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv`, CFSG/Sporadic/Bridge/ThSurj.lean:199. -/
  nonempty_mulEquiv :
    Nonempty (Blueprint.NativeSporadic.Th ≃* TauCeti.SporadicName.Th.Group)
  /-- Corpus: `CFSG.Sporadic.Bridge.Th.card_J`, CFSG/Sporadic/Bridge/ThSurj.lean:168. -/
  card_J [Seed] :
    Nat.card J = 90745943887872000
  /-- Corpus: `CFSG.Certificates.ThDemp.dempChk_facts`, CFSG/Certificates/Kernel/ThDemp/Sound.lean:128. -/
  dempChk_facts (D : DempData) (h : dempChk D = true) : DempFacts D
  /-- Corpus: `CertificateChecks.KernelThDemp.demp_chk`,
  Certificates/Kernel/ThDemp/AssemblyBase.lean:29. -/
  demp_chk : dempChk dempData = true
  /-- Corpus: `CertificateChecks.KernelThDemp.pkMat_SA`,
  Certificates/Kernel/ThDemp/AssemblyBase.lean:35. -/
  pkMat_SA :
    KC.Th.Spec.pkMat dempData.SA = matA
  /-- Corpus: `CertificateChecks.KernelThDemp.pkMat_SB`,
  Certificates/Kernel/ThDemp/AssemblyBase.lean:41. -/
  pkMat_SB :
    KC.Th.Spec.pkMat dempData.SB = matB
  /-- Corpus: `CFSG.KC.Th.Spec.pkMat_mulB`, CFSG/Certificates/Kernel/Th/Spec/Big.lean:798. -/
  pkMat_mulB {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
    (h : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    (A B : ℕ) : pkMat (mulB c rm A B) = pkMat A * pkMat B
  /-- Corpus: `CFSG.KC.Th.Spec.pkMat_one`, CFSG/Certificates/Kernel/Th/Spec/Big.lean:822. -/
  pkMat_one {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
    (h : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true) :
    pkMat ONE = 1
  /-- Corpus: `CFSG.Certificates.ThDemp.exists_chain`, CFSG/Certificates/Kernel/ThDemp/ChainEx.lean:19. -/
  exists_chain {D : DempData} (hF : DempFacts D) {J : Subgroup (GL (Fin 248) (ZMod 2))}
    {a b : J} (ha : 𝕄 a = pkMat D.SA) (hb : 𝕄 b = pkMat D.SB) :
    (∀ r, 0 < r → r < D.nreg → ∃ x : J, 𝕄 x = pkMat (D.RB r)) ∧
    ∃ d₀ d₁ : J, 𝕄 d₀ = pkMat (D.RB (regAt D.rd 0)) ∧ 𝕄 d₁ = pkMat (D.RB (regAt D.rd 1)) ∧
      ∃ t : ℕ → ℕ → J,
        (∀ l < 6, ∀ i < D.oszL l, t l i ∈ Subgroup.closure ({d₀, d₁} : Set J) ∧
          𝕄 (t l i) = pkMat (D.T l i)) ∧
        (∀ x ∈ Subgroup.closure ({d₀, d₁} : Set J), ∃! y : Coords, chainProd t y = x) ∧
        Nat.card (Subgroup.closure ({d₀, d₁} : Set J)) = 319979520 ∧
        (∀ x ∈ Subgroup.closure ({d₀, d₁} : Set J),
          (∀ l < 5, Matrix.vecMul (pkVec (D.bvL l)) (𝕄 x) = pkVec (D.bvL l)) →
          ∃ z < 32, x = t 5 z)
  /-- Corpus: `CFSG.Certificates.ThDemp.Unfold.invChk_sound`,
  CFSG/Certificates/Kernel/ThDemp/OrbUnfold.lean:19. -/
  invChk_sound {D : DempData} {O : OrbData} (h : invChk D O = true) :
    ∀ l < 3, ∀ i < D.oszL l, i < 64 → D.mul (D.T l i) (O.TI l i) = D.ONE
  /-- Corpus: `CertificateChecks.KernelThDemp.orb_checks`,
  Certificates/Kernel/ThDemp/OrbAssemblyBase.lean:44. -/
  orb_checks : Bound.OrbChecks dempData orbData
  /-- Corpus: `CFSG.Certificates.ThDemp.Bound.Ctx.suborbitHyp`,
  CFSG/Certificates/Kernel/ThDemp/OrbBound.lean:121. -/
  suborbitHyp {J : Subgroup (GL (Fin 248) (ZMod 2))} {D : DempData} {O : OrbData}
    (C : Ctx D O J) (hF : DempFacts D) (hJ : RegJ D J) (hc : Bound.OrbChecks D O)
    [Finite J] (hcard : Nat.card J ≤ 90745943887872000)
    (hD : Nat.card C.Dg = 319979520) :
    OrbMain.SuborbitHyp C.Dg (sp (U0 D)) (fun i : Fin 10 => sp (pt D O i))
  /-- Corpus: `CFSG.Certificates.ThDemp.Act.sp_mulB`, CFSG/Certificates/Kernel/ThDemp/Action.lean:131. -/
  sp_mulB (P N : ℕ) : sp (mulB (rep 1 256 5) (2 ^ 248 - 1) P N) = mapM (pkMat N) (sp P)
  /-- Corpus: `CFSG.Certificates.ThDemp.Act.sp_le_of_combChk`,
  CFSG/Certificates/Kernel/ThDemp/Action.lean:201. -/
  sp_le_of_combChk {P Q G : ℕ} (h : combChk (2 ^ 248 - 1) P Q G = true) : sp P ≤ sp Q

universe u v

/-- A generic corpus theorem, stated at universes `u`, `v`. -/
class Generic : Prop where
  /-- Corpus: `CFSG.Certificates.ThDemp.OrbMain.SuborbitHyp.cover`,
  CFSG/Certificates/Kernel/ThDemp/OrbMain.lean:101. -/
  cover {G : Type u} {X : Type v} [Group G] [MulAction G X] [Finite G] {D : Subgroup G} {u : X}
    {p : Fin 10 → X} (H : OrbMain.SuborbitHyp D u p) :
    stabilizer G u = D ∧ ∀ x ∈ orbit G u, ∃ i, x ∈ orbit D (OrbMain.pts u p i)

instance (priority := 100) Theorems.toSeed [Theorems] : Seed := Theorems.seed

end CFSGOutside.Corpus.Th
