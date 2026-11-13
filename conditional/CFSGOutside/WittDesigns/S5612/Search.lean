import Mathlib
import CFSGOutside.WittDesigns.AutS5612.Hexads

/-!
# Exhaustive completion of an `S(5,6,12)` containing a given block

A depth-first search on bit masks completes the block `{0,...,5}` to a Steiner system `S(5,6,12)` by
repeatedly taking the first 5-set that is not covered and trying the six-sets containing it that meet
every chosen block in at most four points.  Every Steiner system containing `{0,...,5}` is one of the
leaves, and a kernel evaluation counts them: there are exactly 720.
-/

namespace CFSGOutside.WittDesigns.Witt5612

open CFSGOutside.WittDesigns.Witt5612

def fiveMasks : List ℕ := (List.range 4096).filter fun m => decide ((maskSet m).card = 5)

def sub5 (B : ℕ) : List ℕ :=
  ((List.range 12).filter fun i => B.testBit i).map fun i => B ^^^ 2 ^ i

def addCov (cov B : ℕ) : ℕ := (sub5 B).foldl (fun c t => c ||| 2 ^ t) cov

def go : List ℕ → ℕ → List ℕ → List (List ℕ)
  | [], _, P => [P]
  | s :: rest, cov, P =>
    if cov.testBit s then go rest cov P
    else (List.range 12).flatMap fun x =>
      if s.testBit x then []
      else
        let B := s ||| 2 ^ x
        if (sub5 B).all (fun t => !cov.testBit t) then go rest (addCov cov B) (B :: P) else []

theorem mem_fiveMasks {t : ℕ} : t ∈ fiveMasks ↔ t < 4096 ∧ (maskSet t).card = 5 := by
  simp [fiveMasks]

theorem testBit_lt_twelve {m i : ℕ} (hm : m < 4096) (hi : 12 ≤ i) : m.testBit i = false := by
  apply Nat.testBit_lt_two_pow
  exact lt_of_lt_of_le hm (by
    calc 4096 = 2 ^ 12 := by norm_num
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi)

theorem maskSet_inj {m n : ℕ} (hm : m < 4096) (hn : n < 4096) (h : maskSet m = maskSet n) : m = n := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 12
  · have := congrArg (fun S => (⟨i, hi⟩ : Fin 12) ∈ S) h
    simp only [mem_maskSet, eq_iff_iff] at this
    exact Bool.eq_iff_iff.2 this
  · rw [testBit_lt_twelve hm (by omega), testBit_lt_twelve hn (by omega)]

theorem maskSet_or_pow (s : ℕ) {x : ℕ} (hx : x < 12) :
    maskSet (s ||| 2 ^ x) = insert ⟨x, hx⟩ (maskSet s) := by
  refine Finset.ext fun i => ?_
  rw [mem_maskSet, Finset.mem_insert, mem_maskSet, Nat.testBit_or, Nat.testBit_two_pow]
  simp only [Bool.or_eq_true, decide_eq_true_eq, Fin.ext_iff]
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h.symm
  · rintro (h | h)
    · exact Or.inr h.symm
    · exact Or.inl h

theorem maskSet_xor_pow (B : ℕ) {i : ℕ} (hi : i < 12) (hb : B.testBit i = true) :
    maskSet (B ^^^ 2 ^ i) = (maskSet B).erase ⟨i, hi⟩ := by
  refine Finset.ext fun j => ?_
  rw [mem_maskSet, Finset.mem_erase, mem_maskSet, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases h : i = j.val
  · subst h; simp [hb, Fin.ext_iff]
  · simp [h, Fin.ext_iff, Ne.symm h]

theorem lt_xor_pow {B i : ℕ} (hB : B < 4096) (hi : i < 12) : B ^^^ 2 ^ i < 4096 := by
  have h12 : 2 ^ i < 4096 := lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) hi) (by norm_num)
  have := Nat.xor_lt_two_pow (n := 12) (x := B) (y := 2 ^ i) (by simpa using hB) (by simpa using h12)
  simpa using this

theorem lt_or_pow {s x : ℕ} (hs : s < 4096) (hx : x < 12) : s ||| 2 ^ x < 4096 := by
  have h12 : 2 ^ x < 4096 := lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) hx) (by norm_num)
  have := Nat.or_lt_two_pow (n := 12) (x := s) (y := 2 ^ x) (by simpa using hs) (by simpa using h12)
  simpa using this

theorem mem_sub5 {B t : ℕ} : t ∈ sub5 B ↔ ∃ i < 12, B.testBit i = true ∧ B ^^^ 2 ^ i = t := by
  simp only [sub5, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩, h3⟩; exact ⟨i, h1, h2, h3⟩
  · rintro ⟨i, h1, h2, h3⟩; exact ⟨i, ⟨h1, h2⟩, h3⟩

theorem sub5_iff {B t : ℕ} (hB : B < 4096) (hBc : (maskSet B).card = 6) (ht : t < 4096)
    (htc : (maskSet t).card = 5) : t ∈ sub5 B ↔ maskSet t ⊆ maskSet B := by
  constructor
  · intro h
    obtain ⟨i, hi, hb, rfl⟩ := mem_sub5.1 h
    rw [maskSet_xor_pow B hi hb]
    exact Finset.erase_subset _ _
  · intro hsub
    have hc := Finset.card_sdiff_add_card_eq_card hsub
    rw [htc, hBc] at hc
    obtain ⟨j, hj⟩ := Finset.card_eq_one.1 (by omega : (maskSet B \ maskSet t).card = 1)
    have hjB : j ∈ maskSet B := (Finset.mem_sdiff.1 (hj ▸ Finset.mem_singleton_self j)).1
    refine mem_sub5.2 ⟨j.val, j.2, (mem_maskSet _ _).1 hjB, ?_⟩
    apply maskSet_inj (lt_xor_pow hB j.2) ht
    rw [maskSet_xor_pow B j.2 ((mem_maskSet _ _).1 hjB)]
    refine Finset.ext fun k => ?_
    have hk := Finset.ext_iff.1 hj k
    simp only [Finset.mem_sdiff, Finset.mem_singleton] at hk
    simp only [Finset.mem_erase]
    constructor
    · rintro ⟨hne, hkB⟩
      by_contra hkt
      exact hne (hk.1 ⟨hkB, hkt⟩)
    · intro hkt
      exact ⟨fun e => (hk.2 e).2 hkt, hsub hkt⟩

theorem testBit_foldl (l : List ℕ) (c u : ℕ) :
    (l.foldl (fun c t => c ||| 2 ^ t) c).testBit u = (c.testBit u || decide (u ∈ l)) := by
  induction l generalizing c with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or, Nat.testBit_two_pow]
    simp only [List.mem_cons]
    by_cases h : u = a
    · subst h; simp
    · simp [h, Ne.symm h]

theorem testBit_addCov (cov B u : ℕ) :
    (addCov cov B).testBit u = (cov.testBit u || decide (u ∈ sub5 B)) := testBit_foldl _ _ _

theorem cov_step {cov B : ℕ} {P : List ℕ}
    (hb : ∀ t, t < 4096 → (maskSet t).card = 5 →
      (cov.testBit t = true ↔ ∃ m ∈ P, maskSet t ⊆ maskSet m))
    (hB : B < 4096) (hBc : (maskSet B).card = 6) :
    ∀ t, t < 4096 → (maskSet t).card = 5 →
      ((addCov cov B).testBit t = true ↔ ∃ m ∈ B :: P, maskSet t ⊆ maskSet m) := by
  intro t ht htc
  rw [testBit_addCov, Bool.or_eq_true, hb t ht htc, decide_eq_true_eq, sub5_iff hB hBc ht htc]
  constructor
  · rintro (⟨m, hm, h⟩ | h)
    · exact ⟨m, List.mem_cons_of_mem _ hm, h⟩
    · exact ⟨B, by simp, h⟩
  · rintro ⟨m, hm, h⟩
    rcases List.mem_cons.1 hm with rfl | hm
    · exact Or.inr h
    · exact Or.inl ⟨m, hm, h⟩

theorem go_sound {𝒮 : Finset (Finset (Fin 12))} (hS : IsSteiner56 𝒮) :
    ∀ (rest pre : List ℕ) (cov : ℕ) (P : List ℕ), fiveMasks = pre ++ rest →
      (∀ m ∈ P, m < 4096 ∧ maskSet m ∈ 𝒮) →
      (∀ t, t < 4096 → (maskSet t).card = 5 →
        (cov.testBit t = true ↔ ∃ m ∈ P, maskSet t ⊆ maskSet m)) →
      (∀ s ∈ pre, cov.testBit s = true) →
      ∃ L ∈ go rest cov P, (∀ m ∈ L, m < 4096) ∧ (L.map maskSet).toFinset = 𝒮 := by
  intro rest
  induction rest with
  | nil =>
    intro pre cov P hpre ha hb hc
    simp only [go, List.mem_singleton, exists_eq_left]
    refine ⟨fun m hm => (ha m hm).1, ?_⟩
    refine Finset.ext fun B => ?_
    simp only [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨m, hm, rfl⟩; exact (ha m hm).2
    · intro hB
      obtain ⟨t, htB, htc⟩ := Finset.exists_subset_card_eq
        (show 5 ≤ B.card by rw [hS.1 B hB]; norm_num)
      obtain ⟨mt, hmt, rfl⟩ := exists_mask t
      have hmem : mt ∈ fiveMasks := mem_fiveMasks.2 ⟨hmt, htc⟩
      rw [hpre, List.append_nil] at hmem
      obtain ⟨m, hm, hsub⟩ := (hb mt hmt htc).1 (hc mt hmem)
      refine ⟨m, hm, ?_⟩
      have hu := hS.2 _ htc
      exact hu.unique ⟨(ha m hm).2, hsub⟩ ⟨hB, htB⟩
  | cons s rest ih =>
    intro pre cov P hpre ha hb hc
    have hs : s ∈ fiveMasks := by rw [hpre]; simp
    obtain ⟨hs4, hsc⟩ := mem_fiveMasks.1 hs
    have hpre' : fiveMasks = (pre ++ [s]) ++ rest := by rw [hpre]; simp
    by_cases hcov : cov.testBit s = true
    · obtain ⟨L, hL, h⟩ := ih (pre ++ [s]) cov P hpre' ha hb (by
        intro u hu
        rcases List.mem_append.1 hu with hu | hu
        · exact hc u hu
        · simp at hu; subst hu; exact hcov)
      exact ⟨L, by simp only [go, hcov, if_true]; exact hL, h⟩
    · have hcov' : cov.testBit s = false := by simpa using hcov
      obtain ⟨B, ⟨hB, hsB⟩, huniq⟩ := hS.2 (maskSet s) hsc
      have hBc := hS.1 B hB
      obtain ⟨x, hx⟩ := Finset.card_eq_one.1
        (by have := Finset.card_sdiff_add_card_eq_card hsB; omega : (B \ maskSet s).card = 1)
      have hxB : x ∈ B ∧ x ∉ maskSet s := Finset.mem_sdiff.1 (hx ▸ Finset.mem_singleton_self x)
      obtain ⟨mB, hmBdef⟩ : ∃ mB, mB = s ||| 2 ^ x.val := ⟨_, rfl⟩
      have hmB4 : mB < 4096 := hmBdef ▸ lt_or_pow hs4 x.2
      have hBm : maskSet mB = B := by
        rw [hmBdef, maskSet_or_pow s x.2]
        refine Finset.ext fun k => ?_
        have hk := Finset.ext_iff.1 hx k
        simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_insert] at hk ⊢
        constructor
        · rintro (rfl | hk')
          · exact hxB.1
          · exact hsB hk'
        · intro hkB
          by_cases hks : k ∈ maskSet s
          · exact Or.inr hks
          · exact Or.inl (hk.1 ⟨hkB, hks⟩)
      have hxs : s.testBit x.val = false := by
        by_contra h
        exact hxB.2 ((mem_maskSet _ _).2 (by simpa using h))
      have hok : (sub5 mB).all (fun t => !cov.testBit t) = true := by
        rw [List.all_eq_true]
        intro t ht
        obtain ⟨i, hi, hbi, rfl⟩ := mem_sub5.1 ht
        have h4 : mB ^^^ 2 ^ i < 4096 := lt_xor_pow hmB4 hi
        have hmem : (⟨i, hi⟩ : Fin 12) ∈ maskSet mB := (mem_maskSet _ _).2 hbi
        have hcard : (maskSet (mB ^^^ 2 ^ i)).card = 5 := by
          rw [maskSet_xor_pow mB hi hbi, Finset.card_erase_of_mem hmem, hBm, hBc]
        by_contra hcv
        have hcv' : cov.testBit (mB ^^^ 2 ^ i) = true := by simpa using hcv
        obtain ⟨m, hm, hsub⟩ := (hb _ h4 hcard).1 hcv'
        have hu := hS.2 _ hcard
        have e : maskSet m = B := hu.unique ⟨(ha m hm).2, hsub⟩ ⟨hB, by
          rw [maskSet_xor_pow mB hi hbi, hBm]; exact Finset.erase_subset _ _⟩
        have : cov.testBit s = true := (hb s hs4 hsc).2 ⟨m, hm, e ▸ hsB⟩
        exact hcov this
      have hBc' : (maskSet mB).card = 6 := by rw [hBm]; exact hBc
      have hb' := cov_step hb hmB4 hBc'
      obtain ⟨L, hL, h⟩ := ih (pre ++ [s]) (addCov cov mB) (mB :: P) hpre'
        (by
          intro m hm
          rcases List.mem_cons.1 hm with rfl | hm
          · exact ⟨hmB4, hBm ▸ hB⟩
          · exact ha m hm)
        hb'
        (by
          intro u hu
          rcases List.mem_append.1 hu with hu | hu
          · rw [testBit_addCov, hc u hu]; simp
          · simp at hu; subst hu
            exact (hb' u hs4 hsc).2 ⟨mB, by simp, by rw [hBm]; exact hsB⟩)
      refine ⟨L, ?_, h⟩
      simp only [go, hcov', Bool.false_eq_true, if_false, List.mem_flatMap, List.mem_range]
      refine ⟨x.val, x.2, ?_⟩
      rw [hxs]
      simp only [Bool.false_eq_true, if_false, ← hmBdef, hok, if_true]
      exact hL

end CFSGOutside.WittDesigns.Witt5612
