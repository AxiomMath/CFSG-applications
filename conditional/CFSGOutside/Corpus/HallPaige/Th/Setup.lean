import Mathlib

/-!
# Copied corpus definitions: the 248-dimensional model of `Th`

Definitions copied verbatim from AxiomMath/CFSG @ 69cb972 (each docstring names the corpus declaration and
file:line). The seed strings `ThSeed1`, `ThSeed2` read `Data/ThG1-f2r248B0.m1`, `.m2`, byte-for-byte
copies of `CFSG/Blueprint/Data/ThG1-f2r248B0.m1`, `.m2`.

The corpus proves `matA * matA = 1` and `matB * matB * matB = 1` (from which `gA`, `gB` get their
determinant side conditions) by a row computation; here these two corpus theorems are the fields of the
class `Seed`, and `gA`, `gB`, `J`, `a`, `b` take `[Seed]`, with the copied corpus proofs of
`matA_det_ne_zero`, `matB_det_ne_zero` inside.
-/

namespace CFSGOutside.Corpus.Th.Blueprint.NativeSporadic

noncomputable section

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

/-- Corpus: `CFSG.Blueprint.NativeSporadic.ThSeed1`, CFSG/Blueprint/NativeSporadic.lean:119
(`include_str "Data"/"ThG1-f2r248B0.m1"`). -/
def ThSeed1 : String := include_str "../Data"/"ThG1-f2r248B0.m1"

/-- Corpus: `CFSG.Blueprint.NativeSporadic.ThSeed2`, CFSG/Blueprint/NativeSporadic.lean:120
(`include_str "Data"/"ThG1-f2r248B0.m2"`). -/
def ThSeed2 : String := include_str "../Data"/"ThG1-f2r248B0.m2"

/-- Corpus: `CFSG.Blueprint.NativeSporadic.Th`, CFSG/Blueprint/NativeSporadic.lean:121. -/
abbrev Th : Type := (seedMonoid 2 248 1 ThSeed1 ThSeed2)ˣ

/-! ### `CFSG/Blueprint/MatrixSeedIdentification.lean` (with the corpus proofs) -/

/-- Corpus: `CFSG.Blueprint.NativeSporadic.unit_seed_closure_eq_ofUnits`,
CFSG/Blueprint/MatrixSeedIdentification.lean:9. -/
theorem unit_seed_closure_eq_ofUnits {M : Type*} [Monoid M] [Finite M] (a b : Mˣ) :
    Submonoid.closure ({(a : M), (b : M)} : Set M) =
      (Subgroup.closure ({a, b} : Set Mˣ)).ofUnits := by
  rw [Subgroup.ofUnits, Subgroup.closure_toSubmonoid_of_finite,
    MonoidHom.map_mclosure]
  simp

/-- Corpus: `CFSG.Blueprint.NativeSporadic.unitSeedEquiv`,
CFSG/Blueprint/MatrixSeedIdentification.lean:16. -/
def unitSeedEquiv {M : Type*} [Monoid M] [Finite M] (a b : Mˣ) :
    (Submonoid.closure ({(a : M), (b : M)} : Set M))ˣ ≃*
      Subgroup.closure ({a, b} : Set Mˣ) :=
  (Submonoid.unitsEquivUnitsType _).symm.trans
    (MulEquiv.subgroupCongr (by
      rw [unit_seed_closure_eq_ofUnits, Subgroup.units_ofUnits_eq]))

/-- Corpus: `CFSG.Blueprint.NativeSporadic.matrixSeedEquiv`,
CFSG/Blueprint/MatrixSeedIdentification.lean:27. -/
def matrixSeedEquiv (p d : ℕ) [Fact p.Prime] (_hd : 1 ≤ d)
    (A B : Matrix (Fin d) (Fin d) (ZMod p)) (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    (Submonoid.closure ({A, B} : Set (Matrix (Fin d) (Fin d) (ZMod p))))ˣ ≃*
      Subgroup.closure
        ({Matrix.GeneralLinearGroup.mkOfDetNeZero A hA,
          Matrix.GeneralLinearGroup.mkOfDetNeZero B hB} :
            Set (Matrix.GeneralLinearGroup (Fin d) (ZMod p))) :=
  unitSeedEquiv (Matrix.GeneralLinearGroup.mkOfDetNeZero A hA)
    (Matrix.GeneralLinearGroup.mkOfDetNeZero B hB)

end

end CFSGOutside.Corpus.Th.Blueprint.NativeSporadic

namespace CFSGOutside.Corpus.Th.Sporadic.Th

open Matrix

/-- Corpus: `CFSG.Sporadic.Th.matA`, CFSG/Sporadic/Th/SetupBase.lean:19. -/
noncomputable abbrev matA : Matrix (Fin 248) (Fin 248) (ZMod 2) :=
  Blueprint.NativeSporadic.decode 2 248 1 Blueprint.NativeSporadic.ThSeed1

/-- Corpus: `CFSG.Sporadic.Th.matB`, CFSG/Sporadic/Th/SetupBase.lean:22. -/
noncomputable abbrev matB : Matrix (Fin 248) (Fin 248) (ZMod 2) :=
  Blueprint.NativeSporadic.decode 2 248 1 Blueprint.NativeSporadic.ThSeed2

/-- The two corpus theorems on the seed matrices. -/
class Seed : Prop where
  /-- Corpus: `CFSG.Sporadic.Th.matA_mul_self`, CFSG/Sporadic/Th/Setup.lean:51. -/
  matA_mul_self : matA * matA = 1
  /-- Corpus: `CFSG.Sporadic.Th.matB_cube`, CFSG/Sporadic/Th/Setup.lean:55. -/
  matB_cube : matB * matB * matB = 1

theorem matA_mul_self [Seed] : matA * matA = 1 := Seed.matA_mul_self

theorem matB_cube [Seed] : matB * matB * matB = 1 := Seed.matB_cube

/-- Corpus: `CFSG.Sporadic.Th.matA_det_ne_zero`, CFSG/Sporadic/Th/Setup.lean:69 (corpus proof). -/
theorem matA_det_ne_zero [Seed] : matA.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det matA_mul_self
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

/-- Corpus: `CFSG.Sporadic.Th.matB_det_ne_zero`, CFSG/Sporadic/Th/Setup.lean:75 (corpus proof). -/
theorem matB_det_ne_zero [Seed] : matB.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det matB_cube
  rw [Matrix.det_mul, Matrix.det_mul, h, zero_mul, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

/-- Corpus: `CFSG.Sporadic.Th.gA`, CFSG/Sporadic/Th/Setup.lean:81. -/
noncomputable abbrev gA [Seed] : GL (Fin 248) (ZMod 2) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero matA matA_det_ne_zero

/-- Corpus: `CFSG.Sporadic.Th.gB`, CFSG/Sporadic/Th/Setup.lean:84. -/
noncomputable abbrev gB [Seed] : GL (Fin 248) (ZMod 2) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero matB matB_det_ne_zero

/-- Corpus: `CFSG.Sporadic.Th.J`, CFSG/Sporadic/Th/Setup.lean:87. -/
noncomputable abbrev J [Seed] : Subgroup (GL (Fin 248) (ZMod 2)) := Subgroup.closure {gA, gB}

/-- Corpus: `CFSG.Sporadic.Th.a`, CFSG/Sporadic/Th/Setup.lean:89. -/
noncomputable def a [Seed] : J := ⟨gA, Subgroup.subset_closure (Set.mem_insert _ _)⟩

/-- Corpus: `CFSG.Sporadic.Th.b`, CFSG/Sporadic/Th/Setup.lean:91. -/
noncomputable def b [Seed] : J := ⟨gB, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

/-- Corpus: `CFSG.Sporadic.Th.a_val`, CFSG/Sporadic/Th/Setup.lean:93 (corpus proof). -/
theorem a_val [Seed] :
    ((a : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2)) = matA := rfl

/-- Corpus: `CFSG.Sporadic.Th.b_val`, CFSG/Sporadic/Th/Setup.lean:95 (corpus proof). -/
theorem b_val [Seed] :
    ((b : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2)) = matB := rfl

end CFSGOutside.Corpus.Th.Sporadic.Th
