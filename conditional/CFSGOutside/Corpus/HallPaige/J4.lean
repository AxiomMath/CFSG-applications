import Mathlib
import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

/-!
# Corpus input for the Janko group `J₄`

The `112`-dimensional matrix model `J ≤ GL₁₁₂(𝔽₂)` of `J₄`, its subgroup `Hj = ⟨xJ 0, xJ 1, xJ 2⟩`
(`≅ 2¹¹:M₂₄`), the path elements `pathElt`, the row action and the root vector, and three corpus
theorems stated as classes with their exact signatures. Definitions are copied verbatim from
AxiomMath/CFSG @ 69cb972 (proofs of the membership side conditions inside `locGL_mem` and the
action axioms of `rowAction` copied too). The seed files `Data/J4G1-f2r112B0.m1`, `.m2` are copies
of `CFSG/Blueprint/Data/J4G1-f2r112B0.m1`, `.m2`.
-/

namespace CFSGOutside.Corpus.J4

open Matrix

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

/-- Corpus: `CFSG.Blueprint.NativeSporadic.J4Seed1`, CFSG/Blueprint/NativeSporadic.lean:59. -/
def J4Seed1 : String := include_str "Data"/"J4G1-f2r112B0.m1"

/-- Corpus: `CFSG.Blueprint.NativeSporadic.J4Seed2`, CFSG/Blueprint/NativeSporadic.lean:60. -/
def J4Seed2 : String := include_str "Data"/"J4G1-f2r112B0.m2"

/-- Corpus: `CFSG.Blueprint.NativeSporadic.J4`, CFSG/Blueprint/NativeSporadic.lean:61. -/
abbrev J4 : Type := (seedMonoid 2 112 1 J4Seed1 J4Seed2)ˣ

/-! ### `CFSG/Sporadic/J4/Setup.lean`, `CFSG/Sporadic/J4/Group.lean` -/

/-- Corpus: `CFSG.Sporadic.J4.matA`, CFSG/Sporadic/J4/Setup.lean:19. -/
noncomputable abbrev matA : Matrix (Fin 112) (Fin 112) (ZMod 2) :=
  decode 2 112 1 J4Seed1

/-- Corpus: `CFSG.Sporadic.J4.matB`, CFSG/Sporadic/J4/Setup.lean:22. -/
noncomputable abbrev matB : Matrix (Fin 112) (Fin 112) (ZMod 2) :=
  decode 2 112 1 J4Seed2

/-- Corpus: `CFSG.Sporadic.J4.wordProd`, CFSG/Sporadic/J4/Setup.lean:35. -/
def wordProd {G : Type*} [Group G] (gs : ℕ → G) (w : List ℤ) : G :=
  (w.map fun l => if 0 < l then gs (l.toNat - 1) else (gs ((-l).toNat - 1))⁻¹).prod

/-- Corpus: `CFSG.Sporadic.J4.wordProd_mem`, CFSG/Sporadic/J4/Setup.lean:38 (proof copied). -/
theorem wordProd_mem {G : Type*} [Group G] (K : Subgroup G) {gs : ℕ → G} (h : ∀ m, gs m ∈ K)
    (w : List ℤ) : wordProd gs w ∈ K := by
  unfold wordProd
  induction w with
  | nil => exact K.one_mem
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons]
    refine K.mul_mem ?_ ih
    split_ifs
    · exact h _
    · exact K.inv_mem (h _)

/-- Corpus: `CFSG.Sporadic.J4.gA`, CFSG/Sporadic/J4/Group.lean:11. -/
noncomputable def gA : GL (Fin 112) (ZMod 2) :=
  @dite _ (matA.det ≠ 0) (Classical.propDecidable _)
    (fun h => Matrix.GeneralLinearGroup.mkOfDetNeZero matA h) (fun _ => 1)

/-- Corpus: `CFSG.Sporadic.J4.gB`, CFSG/Sporadic/J4/Group.lean:15. -/
noncomputable def gB : GL (Fin 112) (ZMod 2) :=
  @dite _ (matB.det ≠ 0) (Classical.propDecidable _)
    (fun h => Matrix.GeneralLinearGroup.mkOfDetNeZero matB h) (fun _ => 1)

/-- Corpus: `CFSG.Sporadic.J4.J`, CFSG/Sporadic/J4/Group.lean:19. -/
noncomputable abbrev J : Subgroup (GL (Fin 112) (ZMod 2)) := Subgroup.closure {gA, gB}

/-- Corpus: `CFSG.Sporadic.J4.a`, CFSG/Sporadic/J4/Group.lean:21. -/
noncomputable def a : J := ⟨gA, Subgroup.subset_closure (Set.mem_insert _ _)⟩

/-- Corpus: `CFSG.Sporadic.J4.b`, CFSG/Sporadic/J4/Group.lean:23. -/
noncomputable def b : J := ⟨gB, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

/-- Corpus: `CFSG.Sporadic.J4.Native.localWords`, Certificates/Data/CFSGNative/J4/Data.lean:17. -/
def localWords (_ : Unit := ()) : List (List Int) := [
    [1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2,
      2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, -1, -2, -1, -2, -2, -1, -2,
      -1, -2, -1, -2, -2, -2, -1, -2, -1, -2, -2, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -1,
      -2, -1, -2, -2, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -1, -2],
    [1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2,
      2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, -1, -2, -2, -2, -1, -2, -2, -1, -2,
      -1, -2, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -2, -2, -1, -2, -2, -2, -1, -2, -1,
      -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, -2, -2, -2],
    [1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2,
      2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, -1, -2, -1, -2, -1, -2, -2, -1,
      -2, -1, -2, -2, -2, -1, -2, -2, -2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -1,
      -2, -2, -2, -1, -2, -1, -2, -2, -2, -1, -2, -2, -1, -2]]

/-- Corpus: `CFSG.Sporadic.J4.baseGL`, CFSG/Sporadic/J4/Group.lean:88. -/
noncomputable def baseGL (m : ℕ) : GL (Fin 112) (ZMod 2) :=
  if m = 0 then gA else if m = 1 then gB else 1

/-- Corpus: `CFSG.Sporadic.J4.locGL`, CFSG/Sporadic/J4/Group.lean:91. -/
noncomputable def locGL (k : ℕ) : GL (Fin 112) (ZMod 2) :=
  wordProd baseGL (localWords[k]?.getD [])

/-- Corpus: `CFSG.Sporadic.J4.baseGL_mem`, CFSG/Sporadic/J4/Group.lean:99 (proof copied). -/
theorem baseGL_mem (m : ℕ) : baseGL m ∈ J := by
  unfold baseGL
  split_ifs
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  · exact J.one_mem

/-- Corpus: `CFSG.Sporadic.J4.locGL_mem`, CFSG/Sporadic/J4/Group.lean:106 (proof copied). -/
theorem locGL_mem (k : ℕ) : locGL k ∈ J := wordProd_mem J baseGL_mem _

/-! ### `CFSG/Sporadic/J4/Local.lean`, `CFSG/Sporadic/J4/QT2LocPath.lean` -/

/-- Corpus: `CFSG.Sporadic.J4.xJ`, CFSG/Sporadic/J4/Local.lean:17. -/
noncomputable def xJ (k : ℕ) : J := ⟨locGL k, locGL_mem k⟩

/-- Corpus: `CFSG.Sporadic.J4.Hj`, CFSG/Sporadic/J4/Local.lean:19. -/
noncomputable abbrev Hj : Subgroup J := Subgroup.closure {xJ 0, xJ 1, xJ 2}

/-- Corpus: `CFSG.Sporadic.J4.QT2.letterElt`, CFSG/Sporadic/J4/QT2LocPath.lean:12. -/
noncomputable def letterElt (l : ℕ) : J := if l = 1 then a else b

/-- Corpus: `CFSG.Sporadic.J4.QT2.pathElt`, CFSG/Sporadic/J4/QT2LocPath.lean:14. -/
noncomputable def pathElt : List ℕ → J
  | [] => 1
  | l :: ls => letterElt l * pathElt ls

/-- Corpus: `CFSG.Sporadic.J4.QT2.repPaths`, CFSG/Sporadic/J4/QT2LocNative.lean:12. -/
def repPaths : List (List Nat) :=
  [[], [1], [2], [1, 2], [2, 2], [2, 1, 2, 2, 2],
    [1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 2]]

/-! ### `CFSG/Sporadic/J4/Action.lean` -/

/-- Corpus: `CFSG.Sporadic.J4.Row`, CFSG/Sporadic/J4/Action.lean:14. -/
def Row : Type := Fin 112 → ZMod 2

/-- Corpus: `CFSG.Sporadic.J4.toRow`, CFSG/Sporadic/J4/Action.lean:16. -/
def toRow (w : Fin 112 → ZMod 2) : Row := w

/-- Corpus: `CFSG.Sporadic.J4.ofRow`, CFSG/Sporadic/J4/Action.lean:18. -/
def ofRow (w : Row) : Fin 112 → ZMod 2 := w

/-- Corpus: `CFSG.Sporadic.J4.rowAction`, CFSG/Sporadic/J4/Action.lean:20 (proofs copied). -/
noncomputable instance rowAction : MulAction J Row where
  smul g w := toRow (ofRow w ᵥ* (((g⁻¹ : J) : GL (Fin 112) (ZMod 2)) :
    Matrix (Fin 112) (Fin 112) (ZMod 2)))
  one_smul w := by
    show toRow (ofRow w ᵥ* (((1⁻¹ : J) : GL (Fin 112) (ZMod 2)) :
      Matrix (Fin 112) (Fin 112) (ZMod 2))) = w
    rw [inv_one, OneMemClass.coe_one, Units.val_one, Matrix.vecMul_one]; rfl
  mul_smul g h w := by
    show toRow (ofRow w ᵥ* ((((g * h)⁻¹ : J) : GL (Fin 112) (ZMod 2)) :
      Matrix (Fin 112) (Fin 112) (ZMod 2))) =
      toRow (ofRow (toRow (ofRow w ᵥ* (((h⁻¹ : J) : GL (Fin 112) (ZMod 2)) :
        Matrix (Fin 112) (Fin 112) (ZMod 2)))) ᵥ* (((g⁻¹ : J) : GL (Fin 112) (ZMod 2)) :
          Matrix (Fin 112) (Fin 112) (ZMod 2)))
    rw [_root_.mul_inv_rev, Subgroup.coe_mul, Units.val_mul, ← Matrix.vecMul_vecMul]; rfl

/-! ### The root vector -/

/-- Corpus: `CFSG.Sporadic.J4.Native.V2`, Certificates/Data/CFSGNative/J4/F2.lean:11. -/
structure V2 where
  lo : UInt64
  hi : UInt64
deriving Inhabited, DecidableEq

/-- Corpus: `CFSG.Sporadic.J4.Native.V2.word`, Certificates/Data/CFSGNative/J4/F2.lean:26. -/
def V2.word (a : V2) (k : Nat) : UInt64 := if k = 0 then a.lo else a.hi

/-- Corpus: `CFSG.Sporadic.J4.Native.V2.testBit`, Certificates/Data/CFSGNative/J4/F2.lean:28. -/
def V2.testBit (a : V2) (j : Nat) : Bool :=
  ((a.word (j / 64) >>> (UInt64.ofNat (j % 64))) &&& 1) == 1

/-- Corpus: `CFSG.Sporadic.J4.Native.V2.toVec`, CFSG/Sporadic/J4/F2Spec.lean:16. -/
def V2.toVec (a : V2) : Fin 112 → ZMod 2 := fun j => if a.testBit j.val then 1 else 0

/-- Corpus: `CFSG.Sporadic.J4.Native.rootV`, Certificates/Data/CFSGNative/J4/Data.lean:13. -/
def rootV : V2 := ⟨0xE7A0656667F0383B, 0x0000CF8BE69F1659⟩

/-- Corpus: `CFSG.Sporadic.SmallF2.toVecD`, CFSG/Sporadic/HS/SmallF2Spec.lean:14. -/
def toVecD (d : ℕ) (x : ℕ) : Fin d → ZMod 2 := fun j => if x.testBit j.val then 1 else 0

/-- Corpus: `CFSG.Sporadic.J4Schreier.rootBits`, CFSG/Sporadic/Schreier/J4SData.lean:22. -/
def rootBits : ℕ := 0xcf8be69f1659e7a0656667f0383b

/-- Corpus: `CFSG.Sporadic.J4Schreier.v`, CFSG/Sporadic/Schreier/J4SLocal.lean:37. -/
def v : Row := toRow (toVecD 112 rootBits)

end

/-! ### Corpus theorems -/

/-- The corpus identification of the native model with the TauCeti presented group. -/
class Bridge : Prop where
  /-- The native model of `J₄` is isomorphic to the TauCeti presented group.
  Corpus: `CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv`, CFSG/Sporadic/Bridge/J4Surj.lean:74. -/
  nonempty_mulEquiv :
    Nonempty (J4 ≃* TauCeti.SporadicName.J4.Group)

/-- The corpus double coset decomposition of `J` with respect to `Hj`. -/
class Cover : Prop where
  /-- Every element of `J` lies in one of the seven double cosets `Hj (pathElt pℓ)⁻¹ Hj`, and the
  suborbits of the root vector have the listed sizes.
  Corpus: `Certificates.certificate4008`, Certificates/Certificate4008.lean:71. -/
  certificate4008 : (∀ g : J, ∃ ℓ < 7, ∃ h ∈ Hj, ∃ h' ∈ Hj,
      g = h * (pathElt (repPaths.getD ℓ []))⁻¹ * h') ∧
    ∀ ℓ < 7,
      (MulAction.orbit Hj ((pathElt (repPaths.getD ℓ []))⁻¹ • toRow rootV.toVec)).ncard =
        [1, 32643072, 82575360, 54405120, 3400320, 15180, 28336].getD ℓ 0

/-- The corpus identification of `Hj` as a point stabilizer. -/
class Stab : Prop where
  /-- `Hj` is the stabilizer of the root vector `v`.
  Corpus: `CFSG.Sporadic.J4Schreier.stabilizer_v_eq_Hj`, CFSG/Sporadic/Schreier/J4SOrder.lean:23. -/
  stabilizer_v_eq_Hj : MulAction.stabilizer J v = Hj

end CFSGOutside.Corpus.J4
