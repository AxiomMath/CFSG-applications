import CFSGOutside.Corpus.HallPaige.Th.Data

/-!
# The cube witnesses for the Dempwolff double cosets of `Th`

For each of the ten nontrivial suborbits `i` (corpus representative `sp (pt dempData orbData i)`, the image
of `sp (U0 dempData)` under the word `orbData.words i` in the registers), `wY i` are the chain coordinates
`y` of an element `h = t 5 y₅ * t 4 y₄ * ⋯ * t 0 y₀` of the Dempwolff group and `wC i` the coefficient code
of the corpus check `combChk`: the five rows of `U0 · (G·H)·(G·H)·G` (`G`, `H` the matrices of the word
and of `h`) are the combinations `wC i` of the rows of `U0`, so `(h * g)³` fixes the subspace.
Found offline by a generator script and `gen_witness.py`.
-/

namespace CFSGOutside.HallPaige.Th

open CFSGOutside.Corpus.Th.KC.Th CFSGOutside.Corpus.Th.KC.Th.BigS CFSGOutside.Corpus.Th.KC.ThDemp
  CFSGOutside.Corpus.Th.KernelThDemp

/-- The 5-row product `P · N₁ ⋯ Nₖ` (packed rows of stride 256). -/
noncomputable def blk (P : ℕ) (ms : List ℕ) : ℕ :=
  ms.foldl (fun S N => mulB (rep 1 256 5) (2 ^ 248 - 1) S N) P

/-- The packed matrices of `t 5 y₅, …, t 0 y₀`. -/
noncomputable def hMats (y : List ℕ) : List ℕ :=
  [dempData.T 5 (y.getD 5 0), dempData.T 4 (y.getD 4 0), dempData.T 3 (y.getD 3 0),
    dempData.T 2 (y.getD 2 0), dempData.T 1 (y.getD 1 0), dempData.T 0 (y.getD 0 0)]

/-- The packed matrices of the letters of the word of representative `i`. -/
noncomputable def gMats (i : ℕ) : List ℕ := (lgetL orbData.words i).map dempData.RB

/-- The factors of `g h g h g`. -/
noncomputable def cubeMats (i : ℕ) (y : List ℕ) : List ℕ :=
  gMats i ++ hMats y ++ gMats i ++ hMats y ++ gMats i

/-- Chain coordinates of the witnesses. -/
def wY : ℕ → List ℕ
  | 0 => [6, 25, 9, 20, 14, 7]
  | 1 => [3, 18, 19, 6, 10, 19]
  | 2 => [27, 26, 2, 4, 3, 2]
  | 3 => [20, 13, 27, 17, 9, 11]
  | 4 => [7, 15, 11, 20, 12, 13]
  | 5 => [15, 11, 24, 21, 13, 16]
  | 6 => [12, 24, 0, 17, 8, 11]
  | 7 => [8, 12, 14, 12, 6, 29]
  | 8 => [3, 24, 15, 8, 13, 28]
  | _ => [11, 29, 9, 19, 13, 12]

/-- Coefficient codes of the witnesses. -/
def wC : ℕ → ℕ
  | 0 => 28916143
  | 1 => 32021673
  | 2 => 22362653
  | 3 => 33173802
  | 4 => 21388723
  | 5 => 1583035
  | 6 => 21244485
  | 7 => 25834953
  | 8 => 12381832
  | _ => 12850424

theorem words_lt : ∀ i < 10, ∀ r ∈ lgetL orbData.words i, 0 < r ∧ r < dempData.nreg := by
  decide +kernel

theorem wY_lt : ∀ i < 10, ∀ l < 6, (wY i).getD l 0 < dempData.oszL l := by
  decide +kernel

theorem rm_eq : dempData.rm = 2 ^ 248 - 1 := by decide +kernel

/-! Two commuting involutions `t 5 1`, `t 5 2` of the normal `2⁵`. -/

theorem chkU : dempData.mul (dempData.T 5 1) (dempData.T 5 1) = dempData.ONE := by decide +kernel

theorem chkV : dempData.mul (dempData.T 5 2) (dempData.T 5 2) = dempData.ONE := by decide +kernel

theorem chkUV : dempData.mul (dempData.mul (dempData.T 5 1) (dempData.T 5 2))
    (dempData.mul (dempData.T 5 1) (dempData.T 5 2)) = dempData.ONE := by decide +kernel

theorem bitU : (dempData.T 5 1).testBit 257 = false := by decide +kernel

theorem bitV : (dempData.T 5 2).testBit 257 = false := by decide +kernel

theorem bitUV : (dempData.mul (dempData.T 5 1) (dempData.T 5 2)).testBit 0 = false := by
  decide +kernel

end CFSGOutside.HallPaige.Th
