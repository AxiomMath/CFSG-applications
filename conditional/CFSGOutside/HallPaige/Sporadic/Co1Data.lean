import CFSGOutside.Corpus.HallPaige.Co1
import CFSGOutside.HallPaige.Sporadic.F2Packed

/-!
# Packed generators of `Co₁`

The two generators of the native model `CFSGOutside.Corpus.Co1.Co1` (decoded from the corpus seed
strings) as packed `𝔽₂`-matrices, words in the generators, and their actions on packed vectors,
with the kernel computations used in `CFSGOutside.HallPaige.Sporadic.Co1`: two commuting involutions
fixing `v₂`.
-/

namespace CFSGOutside.HallPaige.Co1

open CFSGOutside.Corpus.Co1 CFSGOutside.HallPaige.F2

/-! ### The generators as packed matrices -/

/-- The entry list read by `decode` in mode `1` (digits after the header line). -/
def entriesOf (s : String) : List ℕ :=
  (((s.toList.dropWhile (· != '\n')).drop 1).filter fun c => !asciiWhitespace c).map fun c =>
    if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0

theorem decode_eq (s : String) :
    decode 2 24 1 s = fun i j => ((((entriesOf s)[i.val * 24 + j.val]?.getD 0 : ℕ)) : ZMod 2) :=
  rfl

/-- The digits of the first seed. -/
def digitsA : List ℕ := [0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1]

/-- The digits of the second seed. -/
def digitsB : List ℕ := [1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1]

/-- The rows of the first generator, packed (bit `j` of row `i` is entry `(i, j)`). -/
def rowsA : List ℕ := [14568742, 8730514, 16056698, 3053411, 7222122, 11550909, 6184221, 8477716, 11437002, 10461699, 6969765, 13973477, 1322595, 15457769, 1328873, 13337339, 10191992, 3643281, 15394642, 8995024, 9732588, 6652923, 12246250, 12562466]

/-- The rows of the second generator, packed. -/
def rowsB : List ℕ := [6360623, 14740635, 11798632, 6366879, 7578691, 12993865, 16345908, 15448472, 7321200, 2745588, 9841156, 1296923, 6426820, 2765237, 12296090, 4376699, 12707437, 5432847, 14747083, 16526157, 2229586, 2736718, 1418073, 12866597]

theorem entriesOf_seed1 : entriesOf Co1Seed1 = digitsA := by decide +kernel

theorem entriesOf_seed2 : entriesOf Co1Seed2 = digitsB := by decide +kernel

theorem decode_seed1 : decode 2 24 1 Co1Seed1 = matOf 24 rowsA := by
  rw [decode_eq, entriesOf_seed1]
  refine Matrix.ext fun i j => ?_
  simp only [matOf, Matrix.of_apply]
  revert i j
  decide +kernel

theorem decode_seed2 : decode 2 24 1 Co1Seed2 = matOf 24 rowsB := by
  rw [decode_eq, entriesOf_seed2]
  refine Matrix.ext fun i j => ?_
  simp only [matOf, Matrix.of_apply]
  revert i j
  decide +kernel

/-- The submonoid of matrices underlying `Co1`. -/
abbrev S : Submonoid (Matrix (Fin 24) (Fin 24) (ZMod 2)) := seedMonoid 2 24 1 Co1Seed1 Co1Seed2

/-- The first generator, as an element of the submonoid. -/
def sA : S := ⟨decode 2 24 1 Co1Seed1, Submonoid.subset_closure (Set.mem_insert _ _)⟩

/-- The second generator, as an element of the submonoid. -/
def sB : S := ⟨decode 2 24 1 Co1Seed2, Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

theorem sA_val : (sA : Matrix (Fin 24) (Fin 24) (ZMod 2)) = matOf 24 rowsA := decode_seed1

theorem sB_val : (sB : Matrix (Fin 24) (Fin 24) (ZMod 2)) = matOf 24 rowsB := decode_seed2

theorem sA_mul_sA : sA * sA = 1 := by
  apply Subtype.ext
  change (sA : Matrix (Fin 24) (Fin 24) (ZMod 2)) * sA = 1
  rw [sA_val, ← matOf_mm, show mm 24 rowsA rowsA = idm 24 by decide +kernel, matOf_idm]

theorem sB_mul_sB_sB : sB * (sB * sB) = 1 := by
  apply Subtype.ext
  change (sB : Matrix (Fin 24) (Fin 24) (ZMod 2)) * (sB * sB) = 1
  rw [sB_val, ← matOf_mm, ← matOf_mm,
    show mm 24 rowsB (mm 24 rowsB rowsB) = idm 24 by decide +kernel, matOf_idm]

theorem sB_sB_mul_sB : sB * sB * sB = 1 := by
  rw [mul_assoc, sB_mul_sB_sB]

/-- The first generator of `Co₁` (an involution). -/
def gA : Co1 := ⟨sA, sA, sA_mul_sA, sA_mul_sA⟩

/-- The second generator of `Co₁` (of order `3`). -/
def gB : Co1 := ⟨sB, sB * sB, sB_mul_sB_sB, sB_sB_mul_sB⟩

/-- Generator `0` is `gA`, any other is `gB`. -/
def gen (l : ℕ) : Co1 := if l = 0 then gA else gB

/-- The packed matrix of `gen l`. -/
def rows (l : ℕ) : List ℕ := if l = 0 then rowsA else rowsB

theorem gen_val (l : ℕ) :
    ((gen l : Co1) : S).val = matOf 24 (rows l) := by
  unfold gen rows
  split_ifs
  · exact sA_val
  · exact sB_val

/-- The element `gen l₀ * gen l₁ * ⋯` of a word. -/
def wordE (w : List ℕ) : Co1 := (w.map gen).prod

theorem wordE_append (v w : List ℕ) : wordE (v ++ w) = wordE v * wordE w := by
  simp [wordE]

/-- The packed matrix of a word. -/
def wm (w : List ℕ) : List ℕ := w.foldr (fun l acc => mm 24 (rows l) acc) (idm 24)

theorem wordE_val (w : List ℕ) : ((wordE w : Co1) : S).val = matOf 24 (wm w) := by
  induction w with
  | nil => rw [wm, List.foldr_nil, matOf_idm]; rfl
  | cons l w ih =>
    rw [wordE, List.map_cons, List.prod_cons, ← wordE, wm, List.foldr_cons, ← wm, matOf_mm,
      ← ih, ← gen_val]
    rfl

theorem smul_def (g : Co1) (v : Vec24) : g • v = ((g : S) : Matrix (Fin 24) (Fin 24) (ZMod 2)).mulVec v :=
  rfl

/-- The action of a word on a packed vector. -/
def wv (w : List ℕ) (x : ℕ) : ℕ := w.foldr (fun l acc => mv 24 (rows l) acc) x

theorem wordE_smul (w : List ℕ) (x : ℕ) : wordE w • vecOf 24 x = vecOf 24 (wv w x) := by
  induction w with
  | nil => simp [wordE, wv]
  | cons l w ih =>
    rw [wordE, List.map_cons, List.prod_cons, ← wordE, mul_smul, ih, smul_def, gen_val,
      mulVec_matOf]
    rfl

theorem val_mul (g h : Co1) : ((g * h : Co1) : S).val = (g : S).val * (h : S).val := rfl

theorem val_pow (g : Co1) (k : ℕ) : ((g ^ k : Co1) : S).val = (g : S).val ^ k := by
  rw [Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow]

theorem eq_of_val {g h : Co1} (H : (g : S).val = (h : S).val) : g = h :=
  Units.ext (Subtype.ext H)

theorem smul_matOf (g : Co1) {R : List ℕ} (hg : (g : S).val = matOf 24 R) (x : ℕ) :
    g • vecOf 24 x = vecOf 24 (mv 24 R x) := by
  rw [smul_def, hg, mulVec_matOf]

/-! ### The vectors `v₂`, `v₃`, `v₄` -/

theorem v₂_eq : v₂ = vecOf 24 2 := (vecOf_two_pow 24 1).symm

theorem v₃_eq : v₃ = vecOf 24 4096 := (vecOf_two_pow 24 12).symm

theorem v₄_eq : v₄ = vecOf 24 1 := (vecOf_two_pow 24 0).symm

theorem vecOf_ne {x y : ℕ} (hx : x < 2 ^ 24) (hy : y < 2 ^ 24) (h : x ≠ y) :
    vecOf 24 x ≠ vecOf 24 y := fun e => h (vecOf_injective hx hy e)

/-! ### Involutions in the stabilizer of `v₂` -/

/-- A word for an involution fixing `v₂`. -/
def uw : List ℕ := [1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1]

/-- A word for a second involution fixing `v₂`. -/
def vw : List ℕ := [1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1]

/-- The involution `u`. -/
def uE : Co1 := wordE uw

/-- The involution `c = (u v)⁵`, central in the dihedral group `⟨u, v⟩` of order `20`. -/
def cE : Co1 := (wordE uw * wordE vw) ^ 5

/-- The packed matrix of `c`. -/
def cMat : List ℕ := mpow 24 (mm 24 (wm uw) (wm vw)) 5

theorem uE_val : ((uE : Co1) : S).val = matOf 24 (wm uw) := wordE_val uw

theorem cE_val : ((cE : Co1) : S).val = matOf 24 cMat := by
  rw [cE, val_pow, val_mul, wordE_val, wordE_val, cMat, matOf_mpow, matOf_mm]

theorem uE_sq : uE ^ 2 = 1 := by
  apply eq_of_val
  rw [val_pow, uE_val, ← matOf_mpow, show mpow 24 (wm uw) 2 = idm 24 by decide +kernel,
    matOf_idm]
  rfl

theorem cE_sq : cE ^ 2 = 1 := by
  apply eq_of_val
  rw [val_pow, cE_val, ← matOf_mpow, show mpow 24 cMat 2 = idm 24 by decide +kernel, matOf_idm]
  rfl

theorem uE_cE : uE * cE = cE * uE := by
  apply eq_of_val
  rw [val_mul, val_mul, uE_val, cE_val, ← matOf_mm, ← matOf_mm,
    show mm 24 (wm uw) cMat = mm 24 cMat (wm uw) by decide +kernel]

theorem uE_ne_one : uE ≠ 1 := by
  intro h
  have h1 := smul_matOf uE uE_val 1
  rw [h, one_smul] at h1
  exact vecOf_ne (by norm_num) (by decide +kernel) (by decide +kernel) h1

theorem cE_ne_one : cE ≠ 1 := by
  intro h
  have h1 := smul_matOf cE cE_val 1
  rw [h, one_smul] at h1
  exact vecOf_ne (by norm_num) (by decide +kernel) (by decide +kernel) h1

theorem uE_ne_cE : uE ≠ cE := by
  intro h
  have h1 := smul_matOf uE uE_val 1
  rw [h, smul_matOf cE cE_val 1] at h1
  exact vecOf_ne (by decide +kernel) (by decide +kernel) (by decide +kernel) h1

theorem uE_fix : uE • v₂ = v₂ := by
  rw [v₂_eq, smul_matOf uE uE_val, show mv 24 (wm uw) 2 = 2 by decide +kernel]

theorem cE_fix : cE • v₂ = v₂ := by
  rw [v₂_eq, smul_matOf cE cE_val, show mv 24 cMat 2 = 2 by decide +kernel]

end CFSGOutside.HallPaige.Co1
