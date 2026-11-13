import CFSGOutside.HallPaige.Sporadic.J4.XC0
import CFSGOutside.HallPaige.Sporadic.J4.XC1
import CFSGOutside.HallPaige.Sporadic.J4.XC2
import CFSGOutside.HallPaige.Sporadic.J4.Seeds

/-!
# Matrices of the generators of `J₄`

The seed matrices decode to the packed matrices `lm 6`, `lm 7`; this gives the matrices of the
corpus generators `a`, `b` of `J` and of the generators `xJ k` of `Hj` (the corpus words
`localWords`, multiplied out by the kernel in `XC*`). The letters `lt0 i` (`i < 9`) are
`xJ k`, `(xJ k)⁻¹`, `a`, `b`, `b⁻¹`; the pool elements `poolE j` are words in them (the involution
`aI` and elements of its centralizer, built as in Bray's method).
-/

namespace CFSGOutside.HallPaige.J4

open CFSGOutside.Corpus.J4 CFSGOutside.HallPaige.F2 Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

/-! ### Decoding the seeds -/

/-- The entry list read by `decode` in mode `1`. -/
def entriesOf (s : String) : List ℕ :=
  (((s.toList.dropWhile (· != '\n')).drop 1).filter fun c => !asciiWhitespace c).map fun c =>
    if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0

/-- `entriesOf` on the character list. -/
def entriesOfL (cs : List Char) : List ℕ :=
  (((cs.dropWhile (· != '\n')).drop 1).filter fun c => !asciiWhitespace c).map fun c =>
    if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0

theorem entriesOf_eq (s : String) : entriesOf s = entriesOfL s.toList := rfl

theorem decode_eq (s : String) :
    decode 2 112 1 s = fun i j => ((((entriesOf s)[i.val * 112 + j.val]?.getD 0 : ℕ)) : ZMod 2) :=
  rfl

def rowDigits (r : ℕ) : List ℕ := (List.range 112).map fun j => if r.testBit j then 1 else 0

def digitsOf (R : List ℕ) : List ℕ := (R.map rowDigits).flatten

theorem length_rowDigits (r : ℕ) : (rowDigits r).length = 112 := by simp [rowDigits]

theorem digitsOf_get (R : List ℕ) (i j : ℕ) (hi : i < R.length) (hj : j < 112) :
    (digitsOf R)[i * 112 + j]?.getD 0 = if (R.getD i 0).testBit j then 1 else 0 := by
  induction R generalizing i with
  | nil => simp at hi
  | cons r R ih =>
    rcases i with _ | i
    · simp only [digitsOf, List.map_cons, List.flatten_cons, Nat.zero_mul, Nat.zero_add]
      rw [List.getElem?_append_left (by rw [length_rowDigits]; exact hj)]
      simp [rowDigits, List.getElem?_range hj]
    · have h1 : (i + 1) * 112 + j = 112 + (i * 112 + j) := by ring
      have h2 := ih i (by simp at hi; omega)
      simp only [digitsOf] at h2
      simp only [digitsOf, List.map_cons, List.flatten_cons, List.getD_cons_succ]
      rw [h1, List.getElem?_append_right (by rw [length_rowDigits]; omega), length_rowDigits,
        Nat.add_sub_cancel_left]
      exact h2

theorem decode_of (s : String) (R : List ℕ) (hR : R.length = 112) (h : entriesOf s = digitsOf R) :
    decode 2 112 1 s = matOf 112 R := by
  rw [decode_eq, h]
  ext i j
  simp only [matOf, Matrix.of_apply]
  rw [digitsOf_get R i j (by omega) j.2]
  cases (R.getD i 0).testBit j <;> simp [b2z]

theorem eq_of_chunks {α : Type*} (c : ℕ) : ∀ (n : ℕ) (l₁ l₂ : List α),
    (∀ k < n, (l₁.drop (c * k)).take c = (l₂.drop (c * k)).take c) →
    l₁.drop (c * n) = [] → l₂.drop (c * n) = [] → l₁ = l₂
  | 0, l₁, l₂, _, h₁, h₂ => by simp at h₁ h₂; rw [h₁, h₂]
  | n + 1, l₁, l₂, h, h₁, h₂ => by
    rw [← List.take_append_drop c l₁, ← List.take_append_drop c l₂]
    have h0 := h 0 (by omega)
    simp only [Nat.mul_zero, List.drop_zero] at h0
    rw [h0]
    congr 1
    refine eq_of_chunks c n _ _ (fun k hk => ?_) ?_ ?_
    · have := h (k + 1) (by omega)
      rwa [List.drop_drop, List.drop_drop, show c + c * k = c * (k + 1) by ring]
    · rwa [List.drop_drop, show c + c * n = c * (n + 1) by ring]
    · rwa [List.drop_drop, show c + c * n = c * (n + 1) by ring]

set_option maxRecDepth 200000 in
theorem entries1 : entriesOf J4Seed1 = digitsOf (lm 6) := by
  rw [entriesOf_eq, seed1_toList]
  refine eq_of_chunks 1000 13 _ _ (fun k hk => ?_) (by decide +kernel) (by decide +kernel)
  interval_cases k <;> decide +kernel

set_option maxRecDepth 200000 in
theorem entries2 : entriesOf J4Seed2 = digitsOf (lm 7) := by
  rw [entriesOf_eq, seed2_toList]
  refine eq_of_chunks 1000 13 _ _ (fun k hk => ?_) (by decide +kernel) (by decide +kernel)
  interval_cases k <;> decide +kernel

theorem matA_eq : matA = matOf 112 (lm 6) := decode_of _ _ (length_lm 6) entries1

theorem matB_eq : matB = matOf 112 (lm 7) := decode_of _ _ (length_lm 7) entries2

theorem mmA : mmL (lm 6) (lm 6) = idm 112 := by decide +kernel

theorem mmB : mmL (lm 7) (lm 8) = idm 112 := by decide +kernel

theorem det_matA : matA.det ≠ 0 := fun h => by
  have e : matA * matA = 1 := by
    rw [matA_eq, ← matOf_mmL _ _ (length_lm 6), mmA, matOf_idm]
  have := congrArg Matrix.det e
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem det_matB : matB.det ≠ 0 := fun h => by
  have e : matB * matOf 112 (lm 8) = 1 := by
    rw [matB_eq, ← matOf_mmL _ _ (length_lm 8), mmB, matOf_idm]
  have := congrArg Matrix.det e
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem gA_eq : gA = Matrix.GeneralLinearGroup.mkOfDetNeZero matA det_matA := by
  unfold gA; rw [dif_pos det_matA]

theorem gB_eq : gB = Matrix.GeneralLinearGroup.mkOfDetNeZero matB det_matB := by
  unfold gB; rw [dif_pos det_matB]

theorem certG_gA : CertG gA (lm 6) := ⟨by rw [gA_eq]; exact matA_eq, length_lm 6⟩

theorem certG_gB : CertG gB (lm 7) := ⟨by rw [gB_eq]; exact matB_eq, length_lm 7⟩

theorem certG_gAi : CertG gA⁻¹ (lm 6) := certG_gA.inv mmA (length_lm 6)

theorem certG_gBi : CertG gB⁻¹ (lm 8) := certG_gB.inv mmB (length_lm 8)

theorem cert_a : Cert a (lm 6) := certG_gA

theorem cert_b : Cert b (lm 7) := certG_gB

theorem cert_ai : Cert a⁻¹ (lm 6) := cert_a.inv mmA (length_lm 6)

theorem cert_bi : Cert b⁻¹ (lm 8) := cert_b.inv mmB (length_lm 8)

theorem a_inv : a⁻¹ = a := Mx_injective (by rw [cert_ai.mx_eq, cert_a.mx_eq])

/-! ### The generators of `Hj` -/

theorem certG_wordProd (w : List ℤ) (hw : ∀ l ∈ w, l = 1 ∨ l = 2 ∨ l = -1 ∨ l = -2) :
    CertG (wordProd baseGL w) (wordZ w) := by
  induction w with
  | nil => exact CertG.one
  | cons l w ih =>
    have ih' := ih (fun l' h' => hw l' (List.mem_cons_of_mem _ h'))
    have e : wordProd baseGL (l :: w) =
        (if 0 < l then baseGL (l.toNat - 1) else (baseGL ((-l).toNat - 1))⁻¹) * wordProd baseGL w := by
      simp [wordProd]
    rw [e]
    refine CertG.mul ?_ ih' rfl
    rcases hw l List.mem_cons_self with rfl | rfl | rfl | rfl
    · simpa [baseGL, letZ] using certG_gA
    · simpa [baseGL, letZ] using certG_gB
    · simpa [baseGL, letZ] using certG_gAi
    · simpa [baseGL, letZ] using certG_gBi

theorem cert_xJ0 : Cert (xJ 0) (lm 0) := by
  have h := certG_wordProd ((localWords ())[0]?.getD []) (by decide +kernel)
  rw [xc0] at h; exact h

theorem cert_xJ1 : Cert (xJ 1) (lm 1) := by
  have h := certG_wordProd ((localWords ())[1]?.getD []) (by decide +kernel)
  rw [xc1] at h; exact h

theorem cert_xJ2 : Cert (xJ 2) (lm 2) := by
  have h := certG_wordProd ((localWords ())[2]?.getD []) (by decide +kernel)
  rw [xc2] at h; exact h

theorem cert_xJi0 : Cert (xJ 0)⁻¹ (lm 3) := cert_xJ0.inv (by decide +kernel) (length_lm _)

theorem cert_xJi1 : Cert (xJ 1)⁻¹ (lm 4) := cert_xJ1.inv (by decide +kernel) (length_lm _)

theorem cert_xJi2 : Cert (xJ 2)⁻¹ (lm 5) := cert_xJ2.inv (by decide +kernel) (length_lm _)

/-! ### The letters -/

/-- The letters `xJ 0, xJ 1, xJ 2, (xJ 0)⁻¹, (xJ 1)⁻¹, (xJ 2)⁻¹, a, b, b⁻¹`. -/
def lt0 : ℕ → J
  | 0 => xJ 0
  | 1 => xJ 1
  | 2 => xJ 2
  | 3 => (xJ 0)⁻¹
  | 4 => (xJ 1)⁻¹
  | 5 => (xJ 2)⁻¹
  | 6 => a
  | 7 => b
  | 8 => b⁻¹
  | _ => 1

theorem cert_lt0 (i : ℕ) (hi : i < 9) : Cert (lt0 i) (lm i) := by
  interval_cases i
  · exact cert_xJ0
  · exact cert_xJ1
  · exact cert_xJ2
  · exact cert_xJi0
  · exact cert_xJi1
  · exact cert_xJi2
  · exact cert_a
  · exact cert_b
  · exact cert_bi

theorem cert_word0 (w : List ℕ) (hw : w.all (fun l => decide (l < 9)) = true) (T : List ℕ)
    (h : wordM lm w = T) : Cert (wordE lt0 w) T := by
  rw [← h]
  refine cert_wordE lt0 lm w (fun l hl => cert_lt0 l ?_)
  have := List.all_eq_true.1 hw l hl
  simpa using this

theorem cert_pow {g : J} {R : List ℕ} (hg : Cert g R) (n : ℕ) : Cert (g ^ n) (powM R n) := by
  induction n with
  | zero => rw [pow_zero]; exact CertG.one
  | succ n ih => rw [pow_succ]; exact ih.mul hg rfl

/-! ### The pool -/

/-- The involution `aI ∈ O₂(Hj)` (its `Hj`-class has `1771` elements). -/
def aI : J := (wordE lt0 awL) ^ aeN

def gE (j : ℕ) : J := wordE lt0 (gwsL.getD j [])

def cE (j : ℕ) : J := aI * (gE j)⁻¹ * aI * gE j

/-- The pool: elements of the centralizer of `aI` (Bray's elements) and `aI` itself. -/
def poolE (j : ℕ) : J :=
  if j = 16 then aI else if kindsL.getD j true then cE j ^ esL.getD j 0 else gE j * cE j ^ esL.getD j 0

theorem poolE_16 : poolE 16 = aI := by rw [poolE, if_pos rfl]

theorem poolE_even (j : ℕ) (h16 : j ≠ 16) (hk : kindsL.getD j true = true) :
    poolE j = cE j ^ esL.getD j 0 := by rw [poolE, if_neg h16, if_pos hk]

theorem poolE_odd (j : ℕ) (h16 : j ≠ 16) (hk : kindsL.getD j true = false) :
    poolE j = gE j * cE j ^ esL.getD j 0 := by
  rw [poolE, if_neg h16, if_neg (by rw [hk]; decide)]

end

end CFSGOutside.HallPaige.J4
