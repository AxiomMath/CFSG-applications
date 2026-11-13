import Mathlib

/-!
# Copied corpus definitions: the 111-dimensional model of `Ly` and its action on `Ω`

Definitions copied verbatim from AxiomMath/CFSG @ 69cb972 (each docstring names the corpus
declaration and file:line), all in the namespace `CFSGOutside.Corpus.Ly`. The data files
`Data/LyG1-f5r111B0.m1`, `.m2` copy `CFSG/Blueprint/Data/LyG1-f5r111B0.m1`, `.m2`, and
`Data/Ly-root-digits.txt`, `Data/Ly-form-digits.txt`, `Data/Ly-strong-words.txt` copy
`Certificates/Data/CFSGNative/LySchreier/ly-root-digits.txt`, `ly-form-digits.txt`,
`ly-strong-words.txt`. The determinant side conditions inside `gA`, `gB` (proof terms) are proved
by the copied corpus proofs `det_mA_ne_zero`, `det_mB_ne_zero`.
-/

namespace CFSGOutside.Corpus.Ly

noncomputable section

open Matrix MulAction

/-- `5` is prime (the corpus files get this instance from their imports). -/
instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

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

/-- Corpus: `CFSG.Blueprint.NativeSporadic.LySeed1`, CFSG/Blueprint/NativeSporadic.lean:115. -/
def LySeed1 : String := include_str "../Data"/"LyG1-f5r111B0.m1"

/-- Corpus: `CFSG.Blueprint.NativeSporadic.LySeed2`, CFSG/Blueprint/NativeSporadic.lean:116. -/
def LySeed2 : String := include_str "../Data"/"LyG1-f5r111B0.m2"

/-! ### Digit data (`Certificates/Data/CFSGNative/...`) -/

/-- Corpus: `CFSG.Sporadic.LySchreier.Native.rootDigitsTxt`,
Certificates/Data/CFSGNative/LySchreier/Data.lean:7. -/
def rootDigitsTxt : String := include_str "../Data"/"Ly-root-digits.txt"

/-- Corpus: `CFSG.Sporadic.LySchreier.Native.formDigitsTxt`,
Certificates/Data/CFSGNative/LySchreier/Data.lean:9. -/
def formDigitsTxt : String := include_str "../Data"/"Ly-form-digits.txt"

/-- Corpus: `CFSG.Sporadic.LySchreier.Native.strongWordsTxt`,
Certificates/Data/CFSGNative/LySchreier/Data.lean:21. -/
def strongWordsTxt : String := include_str "../Data"/"Ly-strong-words.txt"

/-- Corpus: `CFSG.Sporadic.Ly.Native.digitsOf`, Certificates/Data/CFSGNative/Ly/Faith.lean:12. -/
def digitsOf (s : String) : Array Nat := s.toList.toArray.map fun c => c.toNat - '0'.toNat

/-- Corpus: `CFSG.Sporadic.Ly.Native.matOfDigits`, Certificates/Data/CFSGNative/Ly/Faith.lean:14. -/
def matOfDigits (s : String) : Array (Array Nat) :=
  let e := digitsOf s
  Array.ofFn (n := 111) fun i => Array.ofFn (n := 111) fun j => e[111 * i.val + j.val]!

/-- Corpus: `CFSG.Sporadic.LySchreier.Native.parseInts`, CFSG/Sporadic/Schreier/LyCheckOrbit.lean:14. -/
def parseInts (s : String) : List Int :=
  (s.splitOn " ").filterMap fun t => (t.replace "\n" "").toInt?

/-- Corpus: `CFSG.Sporadic.LySchreier.Native.digitsTxt`, CFSG/Sporadic/Schreier/LyCheckOrbit.lean:20. -/
def digitsTxt (s : String) : Array Nat := digitsOf (s.replace "\n" "")

/-- Corpus: `CFSG.Sporadic.LySchreier.Native.bpRootArr`, CFSG/Sporadic/Schreier/LyCheckOrbit.lean:22. -/
def bpRootArr : Array Nat := digitsTxt rootDigitsTxt

/-- Corpus: `CFSG.Sporadic.LySchreier.Native.bpForm`, CFSG/Sporadic/Schreier/LyCheckOrbit.lean:27. -/
def bpForm : Array (Array Nat) := matOfDigits (formDigitsTxt.replace "\n" "")

/-- Corpus: `CFSG.Sporadic.He.Native.toMat`, CFSG/Sporadic/He/FpSpec.lean:14. -/
def toMat (p d : ℕ) (X : Array (Array ℕ)) : Matrix (Fin d) (Fin d) (ZMod p) :=
  Matrix.of fun i j => ((X[i.val]!)[j.val]! : ZMod p)

/-! ### `CFSG/Sporadic/Ly/Setup.lean` -/

/-- Corpus: `CFSG.Sporadic.Ly.mA`, CFSG/Sporadic/Ly/Setup.lean:17. -/
noncomputable abbrev mA : Matrix (Fin 111) (Fin 111) (ZMod 5) :=
  decode 5 111 1 LySeed1

/-- Corpus: `CFSG.Sporadic.Ly.mB`, CFSG/Sporadic/Ly/Setup.lean:20. -/
noncomputable abbrev mB : Matrix (Fin 111) (Fin 111) (ZMod 5) :=
  decode 5 111 1 LySeed2

/-- Corpus: `CFSG.Sporadic.Ly.mX`, CFSG/Sporadic/Ly/Setup.lean:37. -/
noncomputable abbrev mX : Matrix (Fin 111) (Fin 111) (ZMod 5) :=
  mA * ((mB * mA) * (mB * mA)) * mB * ((mA * mB ^ 4) * (mA * mB ^ 4))

/-- Corpus: `CFSG.Sporadic.LySchreier.lyF`, CFSG/Sporadic/Ly/Setup.lean:47. -/
def lyF : Matrix (Fin 111) (Fin 111) (ZMod 5) :=
  toMat 5 111 bpForm

/-- Corpus: `CFSG.Sporadic.Ly.LySeed`, CFSG/Sporadic/Ly/Setup.lean:57. -/
class LySeed : Prop where
  mA_sq : mA * mA = 1
  mB_pow : mB ^ 5 = 1
  mX_pow : mX ^ 67 = 1
  form_A : mAᵀ * lyF * mA = lyF
  form_B : mBᵀ * lyF * mB = lyF

theorem mB_pow [LySeed] : mB ^ 5 = 1 := LySeed.mB_pow

theorem mX_pow [LySeed] : mX ^ 67 = 1 := LySeed.mX_pow

theorem mA_sq [LySeed] : mA * mA = 1 := LySeed.mA_sq

/-- Corpus proof: `CFSG.Sporadic.Ly.det_mB`, CFSG/Sporadic/Ly/Setup.lean:75. -/
theorem det_mB [LySeed] : mB.det = 1 := by
  have h := congrArg Matrix.det mB_pow
  rwa [Matrix.det_pow, Matrix.det_one, ZMod.pow_card] at h

/-- Corpus proof: `CFSG.Sporadic.Ly.det_mA`, CFSG/Sporadic/Ly/Setup.lean:79. -/
theorem det_mA [LySeed] : mA.det = 1 := by
  have h2 : mA.det * mA.det = 1 := by
    have := congrArg Matrix.det mA_sq
    rwa [Matrix.det_mul, Matrix.det_one] at this
  have hX : mX.det = mA.det ^ 5 := by
    simp only [mX, Matrix.det_mul, Matrix.det_pow, det_mB, one_pow, mul_one]
    ring
  have h67 : mX.det ^ 67 = 1 := by rw [← Matrix.det_pow, mX_pow, Matrix.det_one]
  calc mA.det = (mA.det * mA.det) ^ 167 * mA.det := by rw [h2, one_pow, one_mul]
    _ = (mA.det ^ 5) ^ 67 := by ring
    _ = 1 := by rw [← hX, h67]

theorem det_mA_ne_zero [LySeed] : mA.det ≠ 0 := by rw [det_mA]; exact one_ne_zero

theorem det_mB_ne_zero [LySeed] : mB.det ≠ 0 := by rw [det_mB]; exact one_ne_zero

/-- Corpus: `CFSG.Sporadic.Ly.gA`, CFSG/Sporadic/Ly/Setup.lean:97. -/
noncomputable abbrev gA [LySeed] : GL (Fin 111) (ZMod 5) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero mA det_mA_ne_zero

/-- Corpus: `CFSG.Sporadic.Ly.gB`, CFSG/Sporadic/Ly/Setup.lean:100. -/
noncomputable abbrev gB [LySeed] : GL (Fin 111) (ZMod 5) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero mB det_mB_ne_zero

/-- Corpus: `CFSG.Sporadic.Ly.J`, CFSG/Sporadic/Ly/Setup.lean:103. -/
noncomputable abbrev J
    [LySeed] : Subgroup (GL (Fin 111) (ZMod 5)) := Subgroup.closure {gA, gB}

/-- Corpus: `CFSG.Sporadic.Ly.a`, CFSG/Sporadic/Ly/Setup.lean:106. -/
noncomputable def a
    [LySeed] : J := ⟨gA, Subgroup.subset_closure (Set.mem_insert _ _)⟩

/-- Corpus: `CFSG.Sporadic.Ly.b`, CFSG/Sporadic/Ly/Setup.lean:109. -/
noncomputable def b
    [LySeed] : J := ⟨gB, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

/-- Corpus: `CFSG.Sporadic.Ly.mat`, CFSG/Sporadic/Ly/Setup.lean:112. -/
noncomputable abbrev mat [LySeed]
    (g : J) : Matrix (Fin 111) (Fin 111) (ZMod 5) :=
  ((g : GL (Fin 111) (ZMod 5)) : Matrix (Fin 111) (Fin 111) (ZMod 5))

theorem mat_mul [LySeed] (g h : J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one [LySeed] : mat (1 : J) = 1 := rfl

/-! ### `CFSG/Sporadic/Schreier/LyWords.lean` -/

section Words

variable {G : Type*} [Group G]

/-- Corpus: `CFSG.Sporadic.LySchreier.letterVal`, CFSG/Sporadic/Schreier/LyWords.lean:45. -/
def letterVal (g : ℕ → G) (l : ℤ) : G :=
  if 0 < l then g (l.toNat - 1) else (g ((-l).toNat - 1))⁻¹

/-- Corpus: `CFSG.Sporadic.LySchreier.evalWord`, CFSG/Sporadic/Schreier/LyWords.lean:48. -/
def evalWord (g : ℕ → G) (w : List ℤ) : G := (w.map (letterVal g)).prod

/-- Corpus: `CFSG.Sporadic.LySchreier.extendByWords`, CFSG/Sporadic/Schreier/LyWords.lean:51. -/
def extendByWords (start : List G) (ws : List (List ℤ)) : List G :=
  ws.foldl (fun l w => l ++ [evalWord (fun i => l.getD i 1) w]) start

end Words

/-! ### `CFSG/Sporadic/Schreier/LyData.lean` -/

/-- Corpus: `CFSG.Sporadic.LySchreier.strongWord`, CFSG/Sporadic/Schreier/LyData.lean:64. -/
def strongWord (j : ℕ) : List ℤ := parseInts ((strongWordsTxt.splitOn "\n").getD j "")

/-- Corpus: `CFSG.Sporadic.LySchreier.aStarList`, CFSG/Sporadic/Schreier/LyData.lean:66. -/
def aStarList [LySeed] : List J :=
  extendByWords [a, b] ((List.range 5).map fun j => strongWord (j + 2))

/-- Corpus: `CFSG.Sporadic.LySchreier.aStar`, CFSG/Sporadic/Schreier/LyData.lean:69. -/
def aStar [LySeed] (j : ℕ) : J := aStarList.getD j 1

/-- Corpus: `CFSG.Sporadic.LySchreier.lyH`, CFSG/Sporadic/Schreier/LyData.lean:71. -/
def lyH
    [LySeed] : Subgroup J := Subgroup.closure (aStar '' Set.Icc 2 6)

/-- Corpus: `CFSG.Sporadic.LySchreier.lyU`, CFSG/Sporadic/Schreier/LyData.lean:74. -/
def lyU : Matrix (Fin 111) (Fin 7) (ZMod 5) :=
  Matrix.of fun j m => (bpRootArr[111 * m.val + j.val]! : ZMod 5)

/-- Corpus: `CFSG.Sporadic.LySchreier.lySmall`, CFSG/Sporadic/Schreier/LyData.lean:77. -/
def lySmall : Matrix (Fin 7) (Fin 7) (ZMod 5) :=
  Matrix.of fun i j => (bpRootArr[777 + 7 * i.val + j.val]! : ZMod 5)

/-- Corpus: `CFSG.Sporadic.LySchreier.lyE`, CFSG/Sporadic/Schreier/LyData.lean:80. -/
def lyE : Matrix (Fin 111) (Fin 111) (ZMod 5) := lyU * lySmall * lyUᵀ * lyF

/-- Corpus: `CFSG.Sporadic.LySchreier.LyOperator`, CFSG/Sporadic/Schreier/LyData.lean:111. -/
@[ext] structure LyOperator where
  val : Matrix (Fin 111) (Fin 111) (ZMod 5)

/-- Corpus: the `MulAction J LyOperator` instance, CFSG/Sporadic/Schreier/LyData.lean:114. -/
instance [LySeed] : MulAction J LyOperator where
  smul g E := ⟨mat g * E.val * mat g⁻¹⟩
  one_smul E := by
    ext1
    change mat 1 * E.val * mat 1⁻¹ = E.val
    rw [inv_one, mat_one, Matrix.one_mul, Matrix.mul_one]
  mul_smul g h E := by
    ext1
    change mat (g * h) * E.val * mat (g * h)⁻¹ = mat g * (mat h * E.val * mat h⁻¹) * mat g⁻¹
    rw [_root_.mul_inv_rev, mat_mul, mat_mul]
    simp only [Matrix.mul_assoc]

/-- Corpus: `CFSG.Sporadic.Ly.Omega.opE`, CFSG/Sporadic/Schreier/LyData.lean:136. -/
def opE : LyOperator := ⟨lyE⟩

/-! ### `Certificates/Kernel/Ly3085` -/

/-- Corpus: `CFSG.KD.LyOm.WG1` (`#kc_nat_items_gz`, Certificates/Kernel/Ly3085/Omega/Data.lean:10,
data `Omega/data/base_nats.bin.gz`). -/
def WG1 : List ℕ :=
  [1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0]

/-- Corpus: `CFSG.KD.LyOm.WG2` (as `WG1`). -/
def WG2 : List ℕ :=
  [1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1]

/-- Corpus: `CFSG.KD.LyOm.WG3` (as `WG1`). -/
def WG3 : List ℕ :=
  [0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1]

/-- Corpus: `CFSG.KD.LyOm.WG4` (as `WG1`). -/
def WG4 : List ℕ :=
  [0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0]

/-- Corpus: `CertificateChecks.KernelLy.Omega.abLet`, Certificates/Kernel/Ly3085/Bridge.lean:250. -/
def abLet [LySeed] (l : ℕ) : J := [a, b, a⁻¹, b⁻¹].getD l 1

/-- Corpus: `CertificateChecks.KernelLy.Omega.abWord`, Certificates/Kernel/Ly3085/Bridge.lean:252. -/
def abWord [LySeed] (w : List ℕ) : J := (w.map abLet).prod

/-- Corpus: `CertificateChecks.KernelLy.Omega.gRep`, Certificates/Kernel/Ly3085/Bridge.lean:501. -/
def gRep [LySeed] (c : ℕ) : J :=
  abWord ([WG1, WG2, WG3, WG4].getD (c - 1) [])

/-- Corpus: `CertificateChecks.KernelLy.Omega.repOp`, Certificates/Kernel/Ly3085/SqueezeBase.lean:199. -/
def repOp [LySeed] (c : ℕ) : LyOperator :=
  if c = 0 then opE else gRep c • opE

/-- Corpus: `CFSG.Sporadic.Ly.Omega.lyOperator_finite`, CFSG/Sporadic/Ly/OmegaAct.lean:141. -/
instance lyOperator_finite : Finite LyOperator :=
  Finite.of_injective LyOperator.val fun _ _ h => LyOperator.ext h

/-- Corpus: `CertificateChecks.KernelLy.Omega.subO`, Certificates/Kernel/Ly3085/SqueezeBase.lean:202. -/
def subO [LySeed] (i : Fin 5) : Finset LyOperator :=
  (Set.toFinite (orbit lyH (repOp i.val))).toFinset

end

end CFSGOutside.Corpus.Ly
