import CFSGOutside.HallPaige.Defs
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Lifting complete mappings through a central subgroup of order two

Wilcox, *Reduction of the Hall–Paige conjecture to sporadic simple groups*, Lemma 6 and
Proposition 7: if `G` is good, `N ⊴ G` has order `2` and `G ⧸ N` has a complete mapping, then so
does `G`.
-/

namespace CFSGOutside.HallPaige

section Lemma6

variable {I : Type*} {S T : Equiv.Perm I}

/-- With `U = T * S`, no power `U ^ n` sends `i` to `S i`. -/
private lemma pow_apply_ne_of_invol (hS : ∀ i, S (S i) = i) (hS' : ∀ i, S i ≠ i)
    (hT : ∀ i, T (T i) = i) (hT' : ∀ i, T i ≠ i) (n : ℕ) : ∀ i, ((T * S) ^ n) i ≠ S i := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i h
    match n, ih, h with
    | 0, _, h => exact hS' i (by simpa using h.symm)
    | 1, _, h =>
      simp only [pow_one, Equiv.Perm.mul_apply] at h
      exact hT' _ h
    | m + 2, ih, h =>
      have h1 : (T * S) (((T * S) ^ m) ((T * S) i)) = S i := by
        rw [← h, show m + 2 = 1 + m + 1 by omega, pow_succ, pow_add, pow_one]; rfl
      have h2 : (T * S) (S ((T * S) i)) = S i := by simp [hS, hT]
      exact ih m (by omega) ((T * S) i) ((T * S).injective (h1.trans h2.symm))

/-- **Wilcox, Lemma 6.** Two fixed-point-free involutions `S`, `T` of a finite set `I` admit a
splitting `I = J ⊔ K` (with `J = {i | p i}`) such that `S` and `T` both swap `J` and `K`. -/
theorem exists_split_of_involutions [Finite I] (hS : ∀ i, S (S i) = i) (hS' : ∀ i, S i ≠ i)
    (hT : ∀ i, T (T i) = i) (hT' : ∀ i, T i ≠ i) :
    ∃ p : I → Prop, ∀ i, (p (S i) ↔ ¬ p i) ∧ (p (T i) ↔ ¬ p i) := by
  set U := T * S
  let q : I → Quotient (Equiv.Perm.SameCycle.setoid U) := fun i => Quotient.mk _ i
  obtain ⟨e, he⟩ := exists_injective_nat (Quotient (Equiv.Perm.SameCycle.setoid U))
  have hne : ∀ i, e (q i) ≠ e (q (S i)) := by
    intro i h
    have h' : U.SameCycle i (S i) := Quotient.exact (he h)
    obtain ⟨n, -, hn⟩ := h'.exists_pow_eq'
    exact pow_apply_ne_of_invol hS hS' hT hT' n i hn
  have hTS : ∀ i, q (T i) = q (S i) := fun i =>
    Quotient.sound (Equiv.Perm.SameCycle.symm
      (show U.SameCycle (S i) (T i) from ⟨1, by simp [U, hS]⟩))
  have hST : ∀ i, q (S (T i)) = q i := fun i =>
    Quotient.sound (show U.SameCycle (S (T i)) i from ⟨1, by simp [U, hS, hT]⟩)
  refine ⟨fun i => e (q i) < e (q (S i)), fun i => ?_⟩
  have key : e (q (S i)) < e (q i) ↔ ¬ e (q i) < e (q (S i)) := by
    have := hne i; omega
  constructor
  · simpa only [hS] using key
  · simpa only [hTS, hST] using key

end Lemma6

section Prop7

variable {G : Type*} [Group G]

/-- A subgroup of order `2` is `{1, x}` for an element `x ≠ 1`. -/
private lemma exists_eq_one_or_eq_of_card_two (N : Subgroup G) (hN : Nat.card N = 2) :
    ∃ x ∈ N, x ≠ 1 ∧ ∀ n ∈ N, n = 1 ∨ n = x := by
  obtain ⟨x, hx1, hxu⟩ := (Nat.card_eq_two_iff' (1 : N)).1 hN
  refine ⟨x, x.2, fun h => hx1 (Subtype.ext h), fun n hn => ?_⟩
  by_cases h : (⟨n, hn⟩ : N) = 1
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val (hxu _ h))

/-- If `G` is good and `N ⊴ G` has order `2`, then `G ⧸ N` has even order. -/
private lemma two_dvd_card_quotient [Finite G] (hG : IsGood G) (N : Subgroup G)
    (hN : Nat.card N = 2) : 2 ∣ Nat.card (G ⧸ N) := by
  by_contra h
  have hp : IsPGroup 2 N := IsPGroup.of_card (n := 1) (by simpa using hN)
  rcases hG (hp.toSylow h) with h1 | h1
  · have h1' : N = ⊥ := h1
    have := Subgroup.card_eq_one.2 h1'
    omega
  · exact h1 (isCyclic_of_prime_card (p := 2) hN)

/-- **Wilcox, Proposition 7.** Let `G` be a good finite group and `N ⊴ G` of order `2`. If
`G ⧸ N` has a complete mapping, then so does `G`. -/
theorem hasCompleteMapping_of_normal_card_two [Finite G]
    (hG : IsGood G) (N : Subgroup G) [N.Normal] (hN : Nat.card N = 2)
    (hQ : HasCompleteMapping (G ⧸ N)) : HasCompleteMapping G := by
  classical
  -- `N = {1, x}` with `x` a central involution.
  obtain ⟨x, hxN, hx1, hmemN⟩ := exists_eq_one_or_eq_of_card_two N hN
  have hxx : x * x = 1 := by
    rcases hmemN (x * x) (N.mul_mem hxN hxN) with h | h
    · exact h
    · exact absurd (mul_eq_left.1 h) hx1
  have hxc : ∀ g, g * x = x * g := by
    intro g
    rcases hmemN (g * x * g⁻¹) (‹N.Normal›.conj_mem x hxN g) with h | h
    · exact absurd (by simpa using h) hx1
    · calc g * x = g * x * g⁻¹ * g := by group
        _ = x * g := by rw [h]
  have hfib : ∀ g h : G, (g : G ⧸ N) = h → h = g ∨ h = g * x := by
    intro g h e
    rcases hmemN _ (QuotientGroup.eq.1 e) with h' | h'
    · exact Or.inl (inv_mul_eq_one.1 h').symm
    · exact Or.inr (inv_mul_eq_iff_eq_mul.1 h')
  -- an involution `ȳ` of `G ⧸ N`, lifted to `y : G`.
  obtain ⟨ybar, hy⟩ := exists_prime_orderOf_dvd_card' 2 (two_dvd_card_quotient hG N hN)
  have hyy : ybar * ybar = 1 := by rw [← sq, ← hy, pow_orderOf_eq_one]
  have hy1 : ybar ≠ 1 := by rintro rfl; simp at hy
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective ybar
  -- a complete mapping of `G ⧸ N` in triple form.
  obtain ⟨ι, a₀, b₀, c₀, habc⟩ := hasCompleteMapping_iff_exists_triple.1 hQ
  have : Finite ι := Finite.of_equiv _ a₀.symm
  let S : Equiv.Perm ι := (b₀.trans (Equiv.mulRight ((y : G ⧸ N)))).trans b₀.symm
  let T : Equiv.Perm ι := (c₀.trans (Equiv.mulRight ((y : G ⧸ N)))).trans c₀.symm
  have hbS : ∀ i, b₀ (S i) = b₀ i * y := fun i => by simp [S]
  have hcT : ∀ i, c₀ (T i) = c₀ i * y := fun i => by simp [T]
  have hS : ∀ i, S (S i) = i := fun i =>
    b₀.injective (by rw [hbS, hbS, mul_assoc, hyy, mul_one])
  have hT : ∀ i, T (T i) = i := fun i =>
    c₀.injective (by rw [hcT, hcT, mul_assoc, hyy, mul_one])
  have hS' : ∀ i, S i ≠ i := fun i h => hy1 (by
    have := hbS i; rw [h] at this; exact mul_eq_left.1 this.symm)
  have hT' : ∀ i, T i ≠ i := fun i h => hy1 (by
    have := hcT i; rw [h] at this; exact mul_eq_left.1 this.symm)
  obtain ⟨p, hp⟩ := exists_split_of_involutions hS hS' hT hT'
  -- lifts `b`, `c` of `b₀`, `c₀` with `b (S j) = b j * y`, `c (T j) = c j * y` for `j ∈ J`.
  obtain ⟨b, hb, hbJ, hbK⟩ : ∃ b : ι → G, (∀ i, (b i : G ⧸ N) = b₀ i) ∧
      (∀ i, p i → b (S i) = b i * y) ∧ (∀ i, ¬ p i → b i = b (S i) * y) := by
    refine ⟨fun i => if p i then (b₀ i).out else (b₀ (S i)).out * y, fun i => ?_,
      fun i hi => ?_, fun i hi => ?_⟩
    · by_cases hi : p i
      · simp [hi]
      · simp [hi, hbS, mul_assoc, hyy]
    · simp [hi, (hp i).1, hS]
    · simp [hi, (hp i).1]
  obtain ⟨c, hc, hcJ, hcK⟩ : ∃ c : ι → G, (∀ i, (c i : G ⧸ N) = c₀ i) ∧
      (∀ i, p i → c (T i) = c i * y) ∧ (∀ i, ¬ p i → c i = c (T i) * y) := by
    refine ⟨fun i => if p i then (c₀ i).out else (c₀ (T i)).out * y, fun i => ?_,
      fun i hi => ?_, fun i hi => ?_⟩
    · by_cases hi : p i
      · simp [hi]
      · simp [hi, hcT, mul_assoc, hyy]
    · simp [hi, (hp i).2, hT]
    · simp [hi, (hp i).2]
  -- the lifted triple on `ι × Bool` (`true` standing for `x ∈ N`).
  let A : ι × Bool → G := fun it => c it.1 * (b it.1)⁻¹ * if it.2 then x else 1
  let B : ι × Bool → G := fun it =>
    if p it.1 then (if it.2 then b it.1 * y * x else b it.1)
    else (if it.2 then b it.1 else b it.1 * y⁻¹ * x)
  let C : ι × Bool → G := fun it =>
    if p it.1 then (if it.2 then c it.1 * y else c it.1)
    else (if it.2 then c it.1 * x else c it.1 * y⁻¹ * x)
  have hABC : ∀ it, A it * B it = C it := by
    rintro ⟨i, t⟩
    by_cases hi : p i <;> cases t <;> simp only [A, B, C, hi, if_true, if_false]
    · simp
    · rw [mul_assoc (c i * (b i)⁻¹) x, ← hxc]
      simp [mul_assoc, hxx]
    · simp [mul_assoc]
    · rw [mul_assoc (c i * (b i)⁻¹) x, ← hxc]
      simp [mul_assoc]
  have hcard : Nat.card (ι × Bool) ≤ Nat.card G := by
    rw [Nat.card_prod, Nat.card_congr b₀, Subgroup.card_eq_card_quotient_mul_card_subgroup N, hN]
    simp
  have hAs : Function.Surjective A := by
    intro g
    obtain ⟨i, hi⟩ := a₀.surjective (g : G ⧸ N)
    have : ((c i * (b i)⁻¹ : G) : G ⧸ N) = g := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hb, hc, ← hi, ← habc]
      simp
    rcases hfib _ g this with rfl | rfl
    · exact ⟨(i, false), by simp [A]⟩
    · exact ⟨(i, true), by simp [A]⟩
  have hBs : Function.Surjective B := by
    intro g
    obtain ⟨i, hi⟩ := b₀.surjective (g : G ⧸ N)
    rcases hfib (b i) g (by rw [hb, hi]) with rfl | rfl <;> by_cases hpi : p i
    · exact ⟨(i, false), by simp [B, hpi]⟩
    · exact ⟨(i, true), by simp [B, hpi]⟩
    · exact ⟨(S i, false), by simp [B, hpi, (hp i).1, hbJ i hpi, mul_assoc]⟩
    · exact ⟨(S i, true), by simp [B, hpi, (hp i).1, hbK i hpi, mul_assoc]⟩
  have hCs : Function.Surjective C := by
    intro g
    obtain ⟨i, hi⟩ := c₀.surjective (g : G ⧸ N)
    rcases hfib (c i) g (by rw [hc, hi]) with rfl | rfl <;> by_cases hpi : p i
    · exact ⟨(i, false), by simp [C, hpi]⟩
    · exact ⟨(T i, true), by simp [C, hpi, (hp i).2, hcK i hpi]⟩
    · exact ⟨(T i, false), by simp [C, hpi, (hp i).2, hcJ i hpi, mul_assoc]⟩
    · exact ⟨(i, true), by simp [C, hpi]⟩
  exact HasCompleteMapping.of_triple (Equiv.ofBijective A (hAs.bijective_of_nat_card_le hcard))
    (Equiv.ofBijective B (hBs.bijective_of_nat_card_le hcard))
    (Equiv.ofBijective C (hCs.bijective_of_nat_card_le hcard)) hABC

end Prop7

end CFSGOutside.HallPaige
