import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Action
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Group.Submonoid.Units
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Pointwise
import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

/-!
# Corpus input for the Fischer group `Fi₂₃`

The matrix model `J ≤ GL₂₅₃(𝔽₃)` of `Fi₂₃` with its transposition `d`, the Fischer-theoretic
definitions of `CFSG/Blueprint/FischerDefs.lean`, the action of `C_J(d)` on the transpositions
commuting with `d`, and the corpus theorems used for the Wilcox criterion, stated as classes with
their exact signatures. Definitions are copied verbatim from AxiomMath/CFSG @ 69cb972, except
that the two determinant side conditions inside `gA`, `gB` (proof terms, irrelevant to the
values) are proved here from `matrixFacts`. The seed files `Data/F23G1-f3r253B0.m1`, `.m2` are
copies of `CFSG/Blueprint/Data/F23G1-f3r253B0.m1`, `.m2`.
-/

namespace CFSGOutside.Corpus.Fi23

noncomputable section

/-! ### `CFSG/Blueprint/NativeSporadic.lean` -/

/-- Corpus: `CFSG.Blueprint.NativeSporadic.asciiWhitespace`, CFSG/Blueprint/NativeSporadic.lean:10. -/
def asciiWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c.toNat == 11 || c.toNat == 12

/-- Corpus: `CFSG.Blueprint.NativeSporadic.decode`, CFSG/Blueprint/NativeSporadic.lean:13. -/
def decode (p d mode : ℕ) (s : String) : Matrix (Fin d) (Fin d) (ZMod p) :=
  let body := (s.toList.dropWhile (· != '\n')).drop 1
  let entries : List ℕ := if mode = 1 then
    (body.filter fun c => !asciiWhitespace c).map fun c =>
      if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0
    else
      ((String.ofList (body.map fun c => if asciiWhitespace c then ' ' else c)).splitOn " ").filter
        (· != "") |>.map fun token => if token.toList.all (fun c => '0' ≤ c && c ≤ '9') then token.toNat?.getD 0 else 0
  fun i j => (entries[i.val * d + j.val]?.getD 0 : ZMod p)

/-- Corpus: `CFSG.Blueprint.NativeSporadic.seedMonoid`, CFSG/Blueprint/NativeSporadic.lean:23. -/
def seedMonoid (p d mode : ℕ) (s₁ s₂ : String) :
    Submonoid (Matrix (Fin d) (Fin d) (ZMod p)) :=
  Submonoid.closure {decode p d mode s₁, decode p d mode s₂}

/-- Corpus: `CFSG.Blueprint.NativeSporadic.Fi23Seed1`, CFSG/Blueprint/NativeSporadic.lean:79. -/
def Fi23Seed1 : String := include_str "Data"/"F23G1-f3r253B0.m1"

/-- Corpus: `CFSG.Blueprint.NativeSporadic.Fi23Seed2`, CFSG/Blueprint/NativeSporadic.lean:80. -/
def Fi23Seed2 : String := include_str "Data"/"F23G1-f3r253B0.m2"

/-- Corpus: `CFSG.Blueprint.NativeSporadic.Fi23`, CFSG/Blueprint/NativeSporadic.lean:81. -/
abbrev Fi23 : Type := (seedMonoid 3 253 1 Fi23Seed1 Fi23Seed2)ˣ

/-! ### `CFSG/Blueprint/MatrixSeedIdentification.lean` -/

/-- Corpus: `CFSG.Blueprint.NativeSporadic.unit_seed_closure_eq_ofUnits`,
CFSG/Blueprint/MatrixSeedIdentification.lean:9 (proof copied). -/
theorem unit_seed_closure_eq_ofUnits {M : Type*} [Monoid M] [Finite M] (a b : Mˣ) :
    Submonoid.closure ({(a : M), (b : M)} : Set M) =
      (Subgroup.closure ({a, b} : Set Mˣ)).ofUnits := by
  rw [Subgroup.ofUnits, Subgroup.closure_toSubmonoid_of_finite,
    MonoidHom.map_mclosure]
  simp

/-- Corpus: `CFSG.Blueprint.NativeSporadic.unitSeedEquiv`,
CFSG/Blueprint/MatrixSeedIdentification.lean:16. -/
noncomputable def unitSeedEquiv {M : Type*} [Monoid M] [Finite M] (a b : Mˣ) :
    (Submonoid.closure ({(a : M), (b : M)} : Set M))ˣ ≃*
      Subgroup.closure ({a, b} : Set Mˣ) :=
  (Submonoid.unitsEquivUnitsType _).symm.trans
    (MulEquiv.subgroupCongr (by
      rw [unit_seed_closure_eq_ofUnits, Subgroup.units_ofUnits_eq]))

/-- Corpus: `CFSG.Blueprint.NativeSporadic.matrixSeedEquiv`,
CFSG/Blueprint/MatrixSeedIdentification.lean:27. -/
noncomputable def matrixSeedEquiv (p d : ℕ) [Fact p.Prime] (_hd : 1 ≤ d)
    (A B : Matrix (Fin d) (Fin d) (ZMod p)) (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    (Submonoid.closure ({A, B} : Set (Matrix (Fin d) (Fin d) (ZMod p))))ˣ ≃*
      Subgroup.closure
        ({Matrix.GeneralLinearGroup.mkOfDetNeZero A hA,
          Matrix.GeneralLinearGroup.mkOfDetNeZero B hB} :
            Set (Matrix.GeneralLinearGroup (Fin d) (ZMod p))) :=
  unitSeedEquiv (Matrix.GeneralLinearGroup.mkOfDetNeZero A hA)
    (Matrix.GeneralLinearGroup.mkOfDetNeZero B hB)

/-! ### `CFSG/Blueprint/FischerDefs.lean` -/

/-- Corpus: `CFSG.Blueprint.Fischer.K`, CFSG/Blueprint/FischerDefs.lean:9. -/
abbrev K := GaloisField 2 2

/-- Corpus: `CFSG.Blueprint.Fischer.V`, CFSG/Blueprint/FischerDefs.lean:10. -/
abbrev V := Fin 6 → K

/-- Corpus: `CFSG.Blueprint.Fischer.hermitian`, CFSG/Blueprint/FischerDefs.lean:12. -/
def hermitian (H : Matrix (Fin 6) (Fin 6) K) (x y : V) : K :=
  ∑ i, ∑ j, x i * H i j * (y j) ^ 2

/-- Corpus: `CFSG.Blueprint.Fischer.IsNondegenerateHermitian`,
CFSG/Blueprint/FischerDefs.lean:15. -/
def IsNondegenerateHermitian (H : Matrix (Fin 6) (Fin 6) K) : Prop :=
  (∀ i j, H j i = (H i j) ^ 2) ∧
    ∀ x : V, (∀ y : V, hermitian H x y = 0) → x = 0

/-- Corpus: `CFSG.Blueprint.Fischer.SU`, CFSG/Blueprint/FischerDefs.lean:19. -/
def SU (H : Matrix (Fin 6) (Fin 6) K) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 6) K) :=
  Subgroup.closure {g | Matrix.GeneralLinearGroup.det g = 1 ∧
    ∀ x y : V, hermitian H (Matrix.mulVec (g : Matrix (Fin 6) (Fin 6) K) x)
      (Matrix.mulVec (g : Matrix (Fin 6) (Fin 6) K) y) = hermitian H x y}

/-- Corpus: `CFSG.Blueprint.Fischer.PSU`, CFSG/Blueprint/FischerDefs.lean:25. -/
abbrev PSU (H : Matrix (Fin 6) (Fin 6) K) := SU H ⧸ Subgroup.center (SU H)

/-- Corpus: `CFSG.Blueprint.Fischer.Transvections`, CFSG/Blueprint/FischerDefs.lean:27. -/
def Transvections (H : Matrix (Fin 6) (Fin 6) K) : Set (PSU H) :=
  {g | ∃ u : SU H, QuotientGroup.mk u = g ∧ ∃ v : V, v ≠ 0 ∧ hermitian H v v = 0 ∧
    ∀ x : V, Matrix.mulVec ((u : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) x =
      x + hermitian H x v • v}

/-- Corpus: `CFSG.Blueprint.Fischer.Pair`, CFSG/Blueprint/FischerDefs.lean:32. -/
def Pair (X : Type) [Group X] (E : Set X) : Prop :=
  Finite X ∧ (∃ e : X, E = {x | IsConj e x}) ∧
    (∀ e ∈ E, orderOf e = 2) ∧
    (∀ e ∈ E, ∀ f ∈ E, orderOf (e * f) ∈ ({1, 2, 3} : Set ℕ)) ∧
    Subgroup.closure E = ⊤

/-- Corpus: `CFSG.Blueprint.Fischer.LocalClass`, CFSG/Blueprint/FischerDefs.lean:38. -/
def LocalClass {X : Type} [Group X] (E : Set X) (e : X) : Set X :=
  {f | f ∈ E ∧ f ≠ e ∧ f * e = e * f}

/-- Corpus: `CFSG.Blueprint.Fischer.LocalGroup`, CFSG/Blueprint/FischerDefs.lean:41. -/
def LocalGroup {X : Type} [Group X] (E : Set X) (e : X) : Subgroup X :=
  Subgroup.closure (LocalClass E e)

/-- Corpus: `CFSG.Blueprint.Fischer.LocalQuotient`, CFSG/Blueprint/FischerDefs.lean:44. -/
abbrev LocalQuotient {X : Type} [Group X] (E : Set X) (e : X) :=
  LocalGroup E e ⧸ Subgroup.center (LocalGroup E e)

/-- Corpus: `CFSG.Blueprint.Fischer.LocalImages`, CFSG/Blueprint/FischerDefs.lean:47. -/
def LocalImages {X : Type} [Group X] (E : Set X) (e : X) : Set (LocalQuotient E e) :=
  {q | ∃ f : LocalGroup E e, (f : X) ∈ LocalClass E e ∧ QuotientGroup.mk f = q}

/-- Corpus: `CFSG.Blueprint.Fischer.F22`, CFSG/Blueprint/FischerDefs.lean:50. -/
def F22 (X : Type) [Group X] (E : Set X) : Prop :=
  Pair X E ∧ ∃ e ∈ E, ∃ H : Matrix (Fin 6) (Fin 6) K, IsNondegenerateHermitian H ∧
    ∃ iso : LocalQuotient E e ≃* PSU H, iso '' LocalImages E e = Transvections H

/-- Corpus: `CFSG.Blueprint.Fischer.F23`, CFSG/Blueprint/FischerDefs.lean:54. -/
def F23 (X : Type) [Group X] (E : Set X) : Prop :=
  Pair X E ∧ ∃ e ∈ E, F22 (LocalQuotient E e) (LocalImages E e)

/-! ### `CFSG/Sporadic/Fi23/SetupBase.lean`, `Certificates/Data/CFSGNative/Fi23/Data.lean` -/

/-- Corpus: `CFSG.Sporadic.Fi23.mA`, CFSG/Sporadic/Fi23/SetupBase.lean:17. -/
noncomputable abbrev mA : Matrix (Fin 253) (Fin 253) (ZMod 3) :=
  decode 3 253 1 Fi23Seed1

/-- Corpus: `CFSG.Sporadic.Fi23.mB`, CFSG/Sporadic/Fi23/SetupBase.lean:20. -/
noncomputable abbrev mB : Matrix (Fin 253) (Fin 253) (ZMod 3) :=
  decode 3 253 1 Fi23Seed2

/-- Corpus: `CFSG.Sporadic.Fi23.Native.dWord`, Certificates/Data/CFSGNative/Fi23/Data.lean:15. -/
def dWord : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1]

/-- Corpus: `CFSG.Sporadic.Fi23.Native.eWord`, Certificates/Data/CFSGNative/Fi23/Data.lean:18. -/
def eWord : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1]

/-- Corpus: `CFSG.Sporadic.Fi23.genMat`, CFSG/Sporadic/Fi23/SetupBase.lean:93. -/
noncomputable def genMat (x : ℕ) : Matrix (Fin 253) (Fin 253) (ZMod 3) :=
  if x = 0 then mA else mB

/-- Corpus: `CFSG.Sporadic.Fi23.mW`, CFSG/Sporadic/Fi23/SetupBase.lean:138. -/
noncomputable abbrev mW : Matrix (Fin 253) (Fin 253) (ZMod 3) := (dWord.map genMat).prod

/-- Corpus: `CFSG.Sporadic.Fi23.mE`, CFSG/Sporadic/Fi23/SetupBase.lean:140. -/
noncomputable abbrev mE : Matrix (Fin 253) (Fin 253) (ZMod 3) := (eWord.map genMat).prod

/-- Corpus: `CFSG.Sporadic.Fi23.MatrixFacts`, CFSG/Sporadic/Fi23/SetupBase.lean:151. -/
structure MatrixFacts : Prop where
  A_sq : mA * mA = 1
  B_inv : mB * (mB * mB) = 1
  E_pow : mE ^ 5 = 1
  D_sq : mW ^ 7 * mW ^ 7 = 1
  A_ne : mA ≠ 1
  B_ne : mB ≠ 1
  D_ne : mW ^ 7 ≠ 1

/-- The corpus check of the generator matrices of `Fi₂₃`. -/
class Setup : Prop where
  /-- The generator matrices satisfy the defining checks.
  Corpus: `CFSG.Sporadic.Fi23.matrixFacts`, CFSG/Sporadic/Fi23/Setup.lean:37. -/
  matrixFacts : MatrixFacts

section
variable [h0 : Corpus.Fi23.Setup]
include h0

/-- `det mA ≠ 0` (here from `mA * mA = 1`; the corpus proof `det_mA_ne_zero matrixFacts` goes
through `det mA = 1`). -/
theorem det_mA_ne_zero : mA.det ≠ 0 := fun h => by
  have := congrArg Matrix.det Corpus.Fi23.Setup.matrixFacts.A_sq
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

/-- `det mB ≠ 0` (here from `mB³ = 1`). -/
theorem det_mB_ne_zero : mB.det ≠ 0 := fun h => by
  have := congrArg Matrix.det Corpus.Fi23.Setup.matrixFacts.B_inv
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

/-! ### `CFSG/Sporadic/Fi23/Setup.lean` -/

/-- Corpus: `CFSG.Sporadic.Fi23.gA`, CFSG/Sporadic/Fi23/Setup.lean:40. -/
noncomputable abbrev gA : GL (Fin 253) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero mA det_mA_ne_zero

/-- Corpus: `CFSG.Sporadic.Fi23.gB`, CFSG/Sporadic/Fi23/Setup.lean:43. -/
noncomputable abbrev gB : GL (Fin 253) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero mB det_mB_ne_zero

/-- Corpus: `CFSG.Sporadic.Fi23.J`, CFSG/Sporadic/Fi23/Setup.lean:46. -/
noncomputable abbrev J :
    Subgroup (GL (Fin 253) (ZMod 3)) := Subgroup.closure {gA, gB}

/-- Corpus: `CFSG.Sporadic.Fi23.a`, CFSG/Sporadic/Fi23/Setup.lean:49. -/
noncomputable def a :
    J := ⟨gA, Subgroup.subset_closure (Set.mem_insert _ _)⟩

/-- Corpus: `CFSG.Sporadic.Fi23.b`, CFSG/Sporadic/Fi23/Setup.lean:52. -/
noncomputable def b :
    J := ⟨gB, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

/-- Corpus: `CFSG.Sporadic.Fi23.fi23EquivJ`, CFSG/Sporadic/Fi23/Setup.lean:86. -/
noncomputable def fi23EquivJ : Fi23 ≃* J :=
  matrixSeedEquiv 3 253 (by norm_num) mA mB det_mA_ne_zero det_mB_ne_zero

/-- Corpus: `CFSG.Sporadic.Fi23.wordJ`, CFSG/Sporadic/Fi23/Setup.lean:118. -/
noncomputable def wordJ
    (w : List ℕ) : J := (w.map fun x => if x = 0 then a else b).prod

/-- Corpus: `CFSG.Sporadic.Fi23.d`, CFSG/Sporadic/Fi23/Setup.lean:131. -/
noncomputable def d : J := wordJ dWord ^ 7

/-! ### `CFSG/Sporadic/Fi23/Centralizer.lean` -/

/-- Corpus: `CFSG.Sporadic.Fi23.D23`, CFSG/Sporadic/Fi23/Centralizer.lean:146. -/
abbrev D23 : Set J := {x | IsConj d x}

/-- Corpus: `CFSG.Sporadic.Fi23.star`, CFSG/Sporadic/Fi23/Centralizer.lean:196. -/
noncomputable abbrev star : Set J := LocalClass D23 d

/-- Corpus: `CFSG.Sporadic.Fi23.Cd`, CFSG/Sporadic/Fi23/Centralizer.lean:300. -/
noncomputable abbrev Cd : Subgroup J := Subgroup.centralizer {d}

/-- Corpus: `CFSG.Sporadic.Fi23.mem_Cd`, CFSG/Sporadic/Fi23/Centralizer.lean:302 (proof copied). -/
theorem mem_Cd
    {g : J} : g ∈ Cd ↔ g * d = d * g := Subgroup.mem_centralizer_singleton_iff

/-- Corpus: `CFSG.Sporadic.Fi23.conj_mem_star`, CFSG/Sporadic/Fi23/Centralizer.lean:305
(proof copied). -/
theorem conj_mem_star
    {g : J} (hg : g ∈ Cd) {x : J} (hx : x ∈ star) : g * x * g⁻¹ ∈ star := by
  obtain ⟨hxD, hxd, hxc⟩ := hx
  have hgd := mem_Cd.1 hg
  have hgdg : g⁻¹ * d * g = d := by rw [mul_assoc, ← hgd, ← mul_assoc, inv_mul_cancel, one_mul]
  refine ⟨(hxD : IsConj d x).trans (isConj_iff.2 ⟨g, rfl⟩), fun h => hxd ?_, ?_⟩
  · have : x = g⁻¹ * d * g := by rw [← h]; group
    rw [this, hgdg]
  · calc g * x * g⁻¹ * d = g * x * (g⁻¹ * d * g) * g⁻¹ := by group
      _ = g * x * d * g⁻¹ := by rw [hgdg]
      _ = g * d * x * g⁻¹ := by rw [mul_assoc g x d, hxc, ← mul_assoc]
      _ = d * (g * x * g⁻¹) := by rw [hgd]; group

/-- Corpus: `CFSG.Sporadic.Fi23.starAction`, CFSG/Sporadic/Fi23/Centralizer.lean:318. -/
noncomputable instance starAction : MulAction Cd star where
  smul g x := ⟨(g : J) * x * (g : J)⁻¹, conj_mem_star g.2 x.2⟩
  one_smul x := Subtype.ext (show ((1 : Cd) : J) * (x : J) * ((1 : Cd) : J)⁻¹ = x by simp)
  mul_smul g h x := Subtype.ext (show ((g * h : Cd) : J) * (x : J) * ((g * h : Cd) : J)⁻¹ =
      (g : J) * ((h : J) * x * (h : J)⁻¹) * (g : J)⁻¹ by
    rw [Subgroup.coe_mul, mul_inv_rev]; group)

end

/-! ### Corpus theorems -/

/-- Corpus theorems about the native model of `Fi₂₃`. -/
class Theorems [Corpus.Fi23.Setup] : Prop where
  /-- The native model of `Fi₂₃` is isomorphic to the TauCeti presented group.
  Corpus: `CFSG.Sporadic.Bridge.Fi23.nonempty_mulEquiv`, CFSG/Sporadic/Bridge/Fi23Surj.lean:344. -/
  nonempty_mulEquiv : Nonempty (Fi23 ≃* TauCeti.SporadicName.Fi23.Group)
  /-- The conjugacy class of `d` is a class of `3`-transpositions of Fischer type `F₂₃`.
  Corpus: `CFSG.Sporadic.Fi23.f23_J`, CFSG/Sporadic/Fi23/Fischer.lean:112. -/
  f23_J :
    F23 J D23
  /-- The class of `d` has `31671` elements.
  Corpus: `CFSG.Sporadic.Fi23.card_class_d`, CFSG/Sporadic/Fi23/Transposition.lean:187. -/
  card_class_d : Nat.card {x : J // IsConj d x} = 31671
  /-- `C_J(d)` is transitive on the transpositions commuting with `d`.
  Corpus: `CFSG.Sporadic.Fi23.star_transitive`, CFSG/Sporadic/Fi23/Centralizer.lean:506. -/
  star_transitive
    (x y : star) : ∃ c : Cd, c • x = y

end

end CFSGOutside.Corpus.Fi23
