import CFSGOutside.HallPaige.Defs
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Index

/-!
# Index-two subgroups (Wilcox, Proposition 11)

If `G` is good and `N ⊴ G` has index `2` and a complete mapping, then `G` has a complete mapping
(`CFSGOutside.HallPaige.hasCompleteMapping_of_index_two`). Wilcox derives this from Evans (1992), Theorem 11;
we give a self-contained proof in two steps.

* **Step A** (`hasCompleteMapping_of_parity`, `exists_parity`). Let `u, v ∉ N` satisfy (★)
  (`NoOddConj`): no `N`-conjugate of an odd power of `v` is an odd power of `u`. The commuting
  permutations `λ n = u⁻² n` and `τ n = u⁻¹ n v` of `N` have orbits `{u ^ k n v ^ l | k + l even}`,
  and (★) says the parity of `l` is well defined on each orbit. Hence there is `B₁ ⊆ N` with
  `λ B₁ = B₁` and `τ B₁ = N ∖ B₁`, and from a complete mapping `(a, b, c)` of `N` the triples
  `(a j, b j, c j)`, `(a j u, u⁻¹ b j v, c j v)` (`b j ∈ B₁`) and `(a j, b j v, c j v)`,
  `(a j u, u⁻¹ b j, c j)` (`b j ∉ B₁`) form a complete mapping of `G`.
* **Step B** (`exists_noOddConj`, Wilcox's Lemma 10). Such `u, v` exist when `G` is good. This uses
  Frobenius' theorem that `|G|_p` divides the number of `p`-elements of `G`
  (`ordProj_dvd_card_pElements`, proved by Robinson's induction) and the normalizer condition in
  the Sylow `2`-subgroup (Wilcox's Lemma 9).
-/

namespace CFSGOutside.HallPaige

open Subgroup

universe u

section Frobenius

/-- The `p`-elements of a group: the elements of `p`-power order. -/
def pElements (p : ℕ) (G : Type*) [Group G] : Set G := {x | ∃ n : ℕ, x ^ p ^ n = 1}

/-- If `h` is constant on the orbits of a group action and `d` divides `|orbit b| * h b` for every
`b`, then `d` divides `∑ b, h b`. -/
theorem dvd_sum_of_dvd_index_mul {α β : Type*} [Group α] [MulAction α β] [Fintype β]
    (h : β → ℕ) (hinv : ∀ (a : α) b, h (a • b) = h b) (d : ℕ)
    (hd : ∀ b, d ∣ (MulAction.stabilizer α b).index * h b) : d ∣ ∑ b, h b := by
  classical
  rw [← (MulAction.selfEquivSigmaOrbits α β).symm.sum_comp, Fintype.sum_sigma]
  refine Finset.dvd_sum fun ω _ => ?_
  have : ∀ x : MulAction.orbit α ω.out,
      h ((MulAction.selfEquivSigmaOrbits α β).symm ⟨ω, x⟩) = h ω.out := by
    rintro ⟨x, a, rfl⟩
    exact hinv a _
  rw [Fintype.sum_congr _ _ this, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
  exact hd _

variable {p : ℕ}

/-- In a finite group, the `p`-elements are the solutions of `x ^ |G|_p = 1`. -/
theorem mem_pElements_iff {G : Type*} [Group G] [Finite G] (hp : p.Prime) {x : G} :
    x ∈ pElements p G ↔ x ^ p ^ (Nat.card G).factorization p = 1 := by
  refine ⟨fun ⟨n, hn⟩ => ?_, fun h => ⟨_, h⟩⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hn)
  rw [← orderOf_dvd_iff_pow_eq_one, hj]
  have h1 : p ^ j ∣ Nat.card G := hj ▸ orderOf_dvd_natCard x
  exact pow_dvd_pow p ((hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 h1)

/-- The number of solutions of `x ^ q = w` in terms of `p`-elements of the centralizer of `w`. -/
theorem card_pow_eq_eq {G : Type*} [Group G] {q m : ℕ} {s t : ℤ}
    (hst : (q : ℤ) * s + m * t = 1) {w : G} (hw : w ^ m = 1) :
    Nat.card {x : G // x ^ q = w} = Nat.card {z : G // z ∈ centralizer {w} ∧ z ^ q = 1} := by
  have hy : (w ^ s) ^ q = w := by
    rw [← zpow_natCast, ← zpow_mul, show s * q = 1 - m * t by linarith, zpow_sub, zpow_one,
      zpow_mul, zpow_natCast, hw, one_zpow, inv_one, mul_one]
  refine Nat.card_congr
    { toFun := fun x => ⟨x.1 * (w ^ s)⁻¹, ?_, ?_⟩
      invFun := fun z => ⟨z.1 * w ^ s, ?_⟩
      left_inv := fun x => by simp
      right_inv := fun z => by simp }
  · have hc : Commute x.1 w := by simpa [x.2] using Commute.self_pow x.1 q
    exact Subgroup.mul_mem _ (mem_centralizer_singleton_iff.2 hc)
      (inv_mem (mem_centralizer_singleton_iff.2 ((Commute.refl w).zpow_left s)))
  · have hc0 : Commute x.1 w := by simpa [x.2] using Commute.self_pow x.1 q
    have hc : Commute x.1 (w ^ s) := hc0.zpow_right s
    rw [hc.inv_right.mul_pow, inv_pow, hy, x.2, mul_inv_cancel]
  · have hc : Commute z.1 (w ^ s) :=
      (Commute.zpow_right (mem_centralizer_singleton_iff.1 z.2.1) s)
    rw [hc.mul_pow, z.2.2, hy, one_mul]

/-- Conjugation does not change the number of solutions of `x ^ q = w`. -/
theorem card_pow_eq_conj {G : Type*} [Group G] (q : ℕ) (g w : G) :
    Nat.card {x : G // x ^ q = g * w * g⁻¹} = Nat.card {x : G // x ^ q = w} := by
  refine (Nat.card_congr ((MulAut.conj g).toEquiv.subtypeEquiv fun x => ?_)).symm
  rw [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ← MulAut.conj_apply, ← map_pow,
    EmbeddingLike.apply_eq_iff_eq]

/-- The stabilizer of `w` under conjugation has the index of the centralizer of `w`. -/
theorem index_stabilizer_conjAct {G : Type*} [Group G] [Finite G] (w : G) :
    (MulAction.stabilizer (ConjAct G) w).index = (centralizer {w}).index := by
  have h1 : Nat.card (MulAction.stabilizer (ConjAct G) w) = Nat.card (centralizer {w}) :=
    Nat.card_congr (ConjAct.ofConjAct.toEquiv.subtypeEquiv fun c => by
      rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def, mem_centralizer_singleton_iff,
        mul_inv_eq_iff_eq_mul]
      rfl)
  have h2 := (MulAction.stabilizer (ConjAct G) w).card_mul_index
  have h3 := (centralizer {w}).card_mul_index
  have h4 : Nat.card (ConjAct G) = Nat.card G := Nat.card_congr ConjAct.ofConjAct.toEquiv
  rw [h4, h1, ← h3] at h2
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h2

/-- **Frobenius' theorem** for `n = |G|_p`: the number of `p`-elements of a finite group `G` is
divisible by the `p`-part of `|G|`. We follow G. R. Robinson's inductive proof (MathOverflow
109027): `x ↦ x ^ |G|_p` has fibres over `w ≠ 1` in bijection with the `p`-elements of
`C_G(w)`; the non-central fibres contribute multiples of `|G|_p` by induction, and the central
ones a number of copies of the `p`-elements of `G` that is prime to `p`. -/
theorem ordProj_dvd_card_pElements (hp : p.Prime) (G : Type u) [Group G] [Finite G] :
    p ^ (Nat.card G).factorization p ∣ Nat.card (pElements p G) := by
  induction hn : Nat.card G using Nat.strong_induction_on generalizing G with
  | _ n ih =>
  subst hn
  classical
  have := Fintype.ofFinite G
  have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  set q := p ^ (Nat.card G).factorization p with hq
  set m := Nat.card G / q with hm
  have hqm : q * m = Nat.card G := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hpm : p.Coprime m := Nat.coprime_ordCompl hp hG0
  have hcop : q.Coprime m := hpm.pow_left _
  have hst : (q : ℤ) * Nat.gcdA q m + m * Nat.gcdB q m = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one, Nat.cast_one]
  have hS : ∀ x : G, x ∈ pElements p G ↔ x ^ q = 1 := fun x => mem_pElements_iff hp
  have hSG : Nat.card (pElements p G) = Nat.card {x : G // x ^ q = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight hS)
  set K := Nat.card (pElements p G)
  let F : G → ℕ := fun w => Nat.card {x : G // x ^ q = w}
  have hsum : ∑ w, F w = Nat.card G := by
    simp only [F, Nat.card_eq_fintype_card]
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv (fun x : G => x ^ q))
  have hF0 : ∀ w : G, w ^ m ≠ 1 → F w = 0 := by
    intro w hw
    have : IsEmpty {x : G // x ^ q = w} :=
      ⟨fun x => hw (by rw [← x.2, ← pow_mul, hqm, pow_card_eq_one'])⟩
    exact Nat.card_of_isEmpty
  have hFw : ∀ w : G, w ^ m = 1 →
      F w = Nat.card {z : G // z ∈ centralizer {w} ∧ z ^ q = 1} :=
    fun w hw => card_pow_eq_eq hst hw
  -- central fibres
  have hFc : ∀ w ∈ center G, F w = if w ^ m = 1 then K else 0 := by
    intro w hwc
    split_ifs with hw
    · rw [hFw w hw, hSG]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun z =>
        and_iff_right (mem_centralizer_singleton_iff.2 (mem_center_iff.1 hwc z)))
    · exact hF0 w hw
  -- non-central fibres
  have hFn : ∀ w ∉ center G, q ∣ (centralizer {w}).index * F w := by
    intro w hwc
    by_cases hw : w ^ m = 1
    swap
    · rw [hF0 w hw, mul_zero]
      exact dvd_zero _
    set C := centralizer {w}
    have hCG : Nat.card C < Nat.card G := by
      have hC : C ≠ ⊤ := fun h => hwc (mem_center_iff.2 fun g =>
        mem_centralizer_singleton_iff.1 (show g ∈ C by rw [h]; exact mem_top g))
      exact (Subgroup.card_lt_of_lt (lt_top_iff_ne_top.2 hC)).trans_eq Subgroup.card_top
    have ihC := ih _ hCG C rfl
    have hFC : F w = Nat.card (pElements p C) := by
      rw [hFw w hw]
      exact Nat.card_congr
        { toFun := fun z => ⟨⟨z.1, z.2.1⟩, (Nat.card G).factorization p,
            Subtype.ext (by rw [SubgroupClass.coe_pow]; exact z.2.2)⟩
          invFun := fun z => ⟨z.1.1, z.1.2, (hS _).1 (by
            obtain ⟨n, hn⟩ := z.2
            exact ⟨n, by simpa using congrArg Subtype.val hn⟩)⟩
          left_inv := fun z => rfl
          right_inv := fun z => rfl }
    have h1 : Nat.card C * C.index = Nat.card G := C.card_mul_index
    have hC0 : Nat.card C ≠ 0 := Nat.card_pos.ne'
    have hI0 : C.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [hFC, mul_comm]
    calc q = p ^ (Nat.card C).factorization p * p ^ C.index.factorization p := by
          rw [hq, ← h1, Nat.ordProj_mul p hC0 hI0]
      _ ∣ Nat.card (pElements p C) * C.index := mul_dvd_mul ihC (Nat.ordProj_dvd _ _)
  -- the non-central part of the sum is divisible by `q`
  let h : G → ℕ := fun w => if w ∈ center G then 0 else F w
  have hinv : ∀ (c : ConjAct G) w, h (c • w) = h w := by
    intro c w
    by_cases hwc : w ∈ center G
    · rw [ConjAct.smul_def, mem_center_iff.1 hwc, mul_inv_cancel_right]
    · have : c • w ∉ center G := fun h' => hwc (by
        have e : c⁻¹ • (c • w) = c • w := by
          rw [ConjAct.smul_def c⁻¹ (c • w), mem_center_iff.1 h', mul_inv_cancel_right]
        rw [inv_smul_smul] at e
        rw [e]
        exact h')
      simp only [h, ite_eq_right hwc, ite_eq_right this]
      simp only [F, ConjAct.smul_def, card_pow_eq_conj]
  have hnc : q ∣ ∑ w, h w := by
    refine dvd_sum_of_dvd_index_mul h hinv q fun w => ?_
    by_cases hwc : w ∈ center G
    · simp [h, hwc]
    · simp only [h, ite_eq_right hwc, index_stabilizer_conjAct]
      exact hFn w hwc
  -- the central part of the sum
  let T : Subgroup G :=
    { carrier := {w | w ∈ center G ∧ w ^ m = 1}
      one_mem' := ⟨one_mem _, one_pow m⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [(show Commute a b from mem_center_iff.1 hb.1 a).mul_pow, ha.2, hb.2, one_mul]⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hT : (Nat.card T).Coprime p := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 (fun hdvd => ?_) |>.symm
    have := Fact.mk hp
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := T) p
      (by rwa [← Nat.card_eq_fintype_card])
    have : x ^ m = 1 := Subtype.ext x.2.2
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hpm (hx ▸ orderOf_dvd_of_pow_eq_one this)
  have hc : ∑ w, (if w ∈ center G then F w else 0) = Nat.card T * K := by
    have : ∀ w, (if w ∈ center G then F w else 0) = if w ∈ T then K else 0 := by
      intro w
      by_cases hwc : w ∈ center G
      · rw [ite_eq_left hwc, hFc w hwc]
        by_cases hw : w ^ m = 1
        · rw [ite_eq_left hw, ite_eq_left (show w ∈ T from ⟨hwc, hw⟩)]
        · rw [ite_eq_right hw, ite_eq_right (show w ∉ T from fun h' => hw h'.2)]
      · rw [ite_eq_right hwc, ite_eq_right (show w ∉ T from fun h' => hwc h'.1)]
    rw [Fintype.sum_congr _ _ this, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, smul_eq_mul, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsplit : Nat.card G = ∑ w, h w + Nat.card T * K := by
    rw [← hsum, ← hc, ← Finset.sum_add_distrib]
    refine Fintype.sum_congr _ _ fun w => ?_
    by_cases hwc : w ∈ center G <;> simp [h, hwc]
  have hqK : q ∣ Nat.card T * K := by
    have : q ∣ Nat.card G := Nat.ordProj_dvd _ _
    rw [hsplit] at this
    exact (Nat.dvd_add_right hnc).1 this
  exact ((hT.pow_right _).symm).dvd_of_dvd_mul_left hqK

end Frobenius

section Existence

variable {G : Type u} [Group G]

/-- Condition (★) on `u, v ∉ N`: no `N`-conjugate of an odd power of `v` is an odd power of `u`. -/
def NoOddConj (N : Subgroup G) (u v : G) : Prop :=
  ∀ n ∈ N, ∀ i j : ℤ, Odd i → Odd j → n * v ^ i * n⁻¹ ≠ u ^ j

/-- An element of `2`-power order lies in the cyclic group generated by any odd power of it. -/
theorem mem_zpowers_zpow_of_odd {x : G} {k : ℕ} (hx : x ^ 2 ^ k = 1) {t : ℤ} (ht : Odd t) :
    x ∈ zpowers (x ^ t) := by
  obtain ⟨r, rfl⟩ := ht
  have hc : IsCoprime (2 * r + 1) ((2 : ℤ) ^ k) :=
    IsCoprime.pow_right ⟨1, -r, by ring⟩
  obtain ⟨a, b, hab⟩ := hc
  have hx' : x ^ ((2 : ℤ) ^ k) = 1 := by
    rw [← hx, ← zpow_natCast]
    norm_cast
  refine mem_zpowers_iff.2 ⟨a, ?_⟩
  have : x ^ (a * (2 * r + 1) + b * 2 ^ k) = x := by rw [hab, zpow_one]
  rwa [zpow_add, mul_comm b, zpow_mul x (2 ^ k) b, hx', one_zpow, mul_one, mul_comm a,
    zpow_mul] at this

/-- For `u` outside a subgroup of index `2`, `u ^ t` lies in it iff `t` is even. -/
theorem zpow_mem_iff_even_of_index_two {N : Subgroup G} (hidx : N.index = 2) {u : G}
    (hu : u ∉ N) (t : ℤ) : u ^ t ∈ N ↔ Even t := by
  have hsq : u ^ (2 : ℤ) ∈ N := by
    rw [zpow_two, ← pow_two]
    exact sq_mem_of_index_two hidx u
  rcases Int.even_or_odd' t with ⟨r, rfl | rfl⟩
  · rw [zpow_mul]
    exact ⟨fun _ => even_two_mul r, fun _ => zpow_mem hsq r⟩
  · rw [zpow_add, zpow_mul, zpow_one, mul_mem_iff_of_index_two hidx]
    simp only [zpow_mem hsq r, true_iff, hu]
    exact ⟨fun h => h.elim, fun h => (Int.not_even_two_mul_add_one r) (by simpa using h)⟩

/-- Membership in a normal subgroup is invariant under conjugation. -/
theorem conj_mem_iff {N : Subgroup G} [hN : N.Normal] (g h : G) : g * h * g⁻¹ ∈ N ↔ h ∈ N :=
  ⟨fun hh => by simpa [mul_assoc] using hN.conj_mem _ hh g⁻¹, fun hh => hN.conj_mem _ hh g⟩

/-- A generator of a cyclic group `H = ⟨x⟩` of `2`-power order outside `N` is any element of
`H ∖ N`. -/
theorem zpowers_eq_of_not_mem {N : Subgroup G} (hidx : N.index = 2) {x : G} {k : ℕ}
    (hx : x ^ 2 ^ k = 1) (hxN : x ∉ N) {h : G} (hh : h ∈ zpowers x) (hhN : h ∉ N) :
    zpowers h = zpowers x := by
  obtain ⟨t, rfl⟩ := mem_zpowers_iff.1 hh
  have ht : Odd t := by
    rw [← Int.not_even_iff_odd, ← zpow_mem_iff_even_of_index_two hidx hxN]
    exact hhN
  exact le_antisymm (zpowers_le.2 hh) (zpowers_le.2 (mem_zpowers_zpow_of_odd hx ht))

/-- If `c` conjugates a generator of `H` to a generator of `H`, then `c` normalizes `H`. -/
theorem mem_normalizer_of_conj {H : Subgroup G} {a b c : G} (ha : zpowers a = H)
    (hb : zpowers b = H) (hc : c * a * c⁻¹ = b) : c ∈ normalizer (H : Set G) := by
  refine mem_normalizer_iff.2 fun z => ⟨fun hz => ?_, fun hz => ?_⟩
  · rw [← ha] at hz
    obtain ⟨t, rfl⟩ := mem_zpowers_iff.1 hz
    rw [← conj_zpow, hc, ← hb]
    exact zpow_mem_zpowers b t
  · rw [← hb] at hz
    obtain ⟨t, ht⟩ := mem_zpowers_iff.1 hz
    rw [← hc, conj_zpow] at ht
    have : z = a ^ t := by simpa using ht.symm
    rw [this, ← ha]
    exact zpow_mem_zpowers a t

/-- **Wilcox, Lemma 10**, in the form used for Proposition 11: if `G` is good and `N` has index
`2`, there are `u, v ∉ N` satisfying (★). Suppose not, and let `x ∈ P ∖ N` for a Sylow
`2`-subgroup `P`, `H = ⟨x⟩`. Then every `2`-element of `G ∖ N` is conjugate to a generator of
`H`, so the set `X` of these elements satisfies `|X| * |N_G(H)| = |G| * |H| / 2`. By Frobenius
(`ordProj_dvd_card_pElements`, applied to `G` and `N`), `|P| / 2` divides `|X|`, whence
`N_P(H) = H`, so `H = P` by the normalizer condition, and `P` is cyclic. -/
theorem exists_noOddConj [Finite G] (hG : IsGood G) {N : Subgroup G} (hidx : N.index = 2) :
    ∃ u v, u ∉ N ∧ v ∉ N ∧ NoOddConj N u v := by
  classical
  have := Fintype.ofFinite G
  have hN := normal_of_index_eq_two hidx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 G) := inferInstance
  have hPN : ¬ (P : Subgroup G) ≤ N := fun h => P.not_dvd_index (by
    rw [← relIndex_mul_index h, hidx]; exact dvd_mul_left 2 _)
  obtain ⟨x, hxP, hxN⟩ := IsConcreteLE.not_le_iff_exists.1 hPN
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hxP⟩
  have hx : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  by_contra hcon
  have key : ∀ y, y ∉ N → ∃ n ∈ N, ∃ i j : ℤ, Odd i ∧ Odd j ∧ n * y ^ i * n⁻¹ = x ^ j := by
    intro y hy
    have : ¬ NoOddConj N x y := fun h => hcon ⟨x, y, hxN, hy, h⟩
    simp only [NoOddConj] at this
    push Not at this
    exact this
  set H := zpowers x with hH
  have hH2 : ∀ h ∈ H, h ^ 2 ^ k = 1 := by
    intro h hh
    obtain ⟨t, rfl⟩ := mem_zpowers_iff.1 hh
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  have hgen : ∀ h ∈ H, h ∉ N → zpowers h = H := fun h hh hhN =>
    zpowers_eq_of_not_mem hidx hx hxN hh hhN
  -- the sets we count
  let SG := (Finset.univ : Finset G).filter (· ∈ pElements 2 G)
  let X := SG.filter (· ∉ N)
  let HF := (Finset.univ : Finset G).filter (· ∈ H)
  let D := HF.filter (· ∉ N)
  let NG := (Finset.univ : Finset G).filter (· ∈ normalizer (H : Set G))
  -- `|G| * |D| = |X| * |N_G(H)|`
  have hcount : Fintype.card G * D.card = X.card * NG.card := by
    have hmaps : Set.MapsTo (fun gh : G × G => gh.1 * gh.2 * gh.1⁻¹)
        (↑(Finset.univ ×ˢ D : Finset (G × G)) : Set (G × G)) ↑X := by
      rintro ⟨g, h⟩ hgh
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_univ, true_and, D, HF,
        Finset.mem_filter] at hgh
      simp only [Finset.mem_coe, X, SG, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨k, by rw [conj_pow, hH2 h hgh.1, mul_one, mul_inv_cancel]⟩,
        fun h' => hgh.2 ((conj_mem_iff g h).1 h')⟩
    have hA := Finset.card_eq_sum_card_fiberwise hmaps
    rw [Finset.card_product, Finset.card_univ] at hA
    rw [hA]
    have hfib : ∀ y ∈ X, ((Finset.univ ×ˢ D).filter
        (fun gh : G × G => gh.1 * gh.2 * gh.1⁻¹ = y)).card = NG.card := by
      intro y hy
      simp only [X, SG, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      obtain ⟨n, hnN, i, j, hi, hj, hnij⟩ := key y hy.2
      obtain ⟨kn, hkn⟩ := hy.1
      obtain ⟨a, ha⟩ := mem_zpowers_iff.1 (mem_zpowers_zpow_of_odd hkn hi)
      obtain ⟨g₀, h₀, hy0, hh₀, hh₀N⟩ :
          ∃ g₀ h₀ : G, g₀ * h₀ * g₀⁻¹ = y ∧ h₀ ∈ H ∧ h₀ ∉ N := by
        have hy0 : n⁻¹ * x ^ (j * a) * n⁻¹⁻¹ = y := by
          have e1 : y ^ i = n⁻¹ * x ^ j * n⁻¹⁻¹ := by rw [← hnij]; group
          rw [← ha, e1, conj_zpow, zpow_mul]
        exact ⟨n⁻¹, x ^ (j * a), hy0, zpow_mem_zpowers x _,
          fun h' => hy.2 (hy0 ▸ (conj_mem_iff _ _).2 h')⟩
      symm
      refine Finset.card_nbij' (fun c => (g₀ * c, c⁻¹ * h₀ * c)) (fun gh => g₀⁻¹ * gh.1)
        ?_ ?_ ?_ ?_
      · intro c hc
        simp only [NG, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hc
        simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_univ, true_and, D, HF,
          Finset.mem_filter, Set.mem_ofPred_eq]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · simpa using (mem_normalizer_iff.1 (inv_mem hc) h₀).1 hh₀
        · intro h'
          exact hh₀N ((conj_mem_iff c⁻¹ h₀).1 (by simpa using h'))
        · rw [← hy0]; group
      · rintro ⟨g, h⟩ hgh
        simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_univ, true_and, D, HF,
          Finset.mem_filter, Set.mem_ofPred_eq] at hgh
        simp only [NG, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
        refine mem_normalizer_of_conj (hgen h hgh.1.1 hgh.1.2) (hgen h₀ hh₀ hh₀N) ?_
        calc g₀⁻¹ * g * h * (g₀⁻¹ * g)⁻¹ = g₀⁻¹ * (g * h * g⁻¹) * g₀ := by group
          _ = h₀ := by rw [hgh.2, ← hy0]; group
      · intro c _
        simp
      · rintro ⟨g, h⟩ hgh
        simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_univ, true_and,
          Set.mem_ofPred_eq] at hgh
        have e : h₀ = g₀⁻¹ * g * h * (g₀⁻¹ * g)⁻¹ := by
          rw [← hy0] at hgh
          calc h₀ = g₀⁻¹ * (g₀ * h₀ * g₀⁻¹) * g₀ := by group
            _ = _ := by rw [← hgh.2]; group
        simp only [Prod.mk.injEq]
        refine ⟨by group, ?_⟩
        rw [e]; group
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
  -- `|D| * 2 = |H|`
  have hDH : D.card * 2 = Nat.card H := by
    have h1 := Finset.card_filter_add_card_filter_not (s := HF) (· ∈ N)
    have h2 : (HF.filter (· ∈ N)).card = D.card := by
      refine Finset.card_nbij' (· * x) (· * x⁻¹) ?_ ?_ ?_ ?_
      · intro z hz
        simp only [HF, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_ofPred_eq] at hz
        simp only [D, HF, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_ofPred_eq]
        refine ⟨mul_mem hz.1 (mem_zpowers x), fun h' => hxN ?_⟩
        exact ((mul_mem_iff_of_index_two hidx).1 h').1 hz.2
      · intro z hz
        simp only [D, HF, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_ofPred_eq] at hz
        simp only [HF, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_ofPred_eq]
        refine ⟨mul_mem hz.1 (inv_mem (mem_zpowers x)), ?_⟩
        exact (mul_mem_iff_of_index_two hidx).2 (iff_of_false hz.2 fun h => hxN (inv_mem_iff.1 h))
      · intro z _; simp
      · intro z _; simp
    have h3 : HF.card = Nat.card H := by
      rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    rw [← h3, ← h1, h2]
    ring
  -- Frobenius: `|P| / 2` divides `|X|`
  have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hNG : Nat.card N * 2 = Nat.card G := hidx ▸ N.card_mul_index
  set B := 2 ^ (Nat.card N).factorization 2
  have hfact : (Nat.card G).factorization 2 = (Nat.card N).factorization 2 + 1 := by
    rw [← hNG, Nat.factorization_mul Nat.card_pos.ne' two_ne_zero, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two]
  have hAB : 2 ^ (Nat.card G).factorization 2 = B * 2 := by rw [hfact, pow_succ]
  have hBX : B ∣ X.card := by
    have h1 := Finset.card_filter_add_card_filter_not (s := SG) (· ∈ N)
    have hSG : SG.card = Nat.card (pElements 2 G) := by
      rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    have hSN : (SG.filter (· ∈ N)).card = Nat.card (pElements 2 N) := by
      rw [Finset.filter_filter]
      have : Nat.card (pElements 2 N) = Nat.card {y : G // y ∈ pElements 2 G ∧ y ∈ N} :=
        Nat.card_congr
          { toFun := fun z => ⟨z.1.1, by
              obtain ⟨n, hn⟩ := z.2
              exact ⟨n, by simpa using congrArg Subtype.val hn⟩, z.1.2⟩
            invFun := fun z => ⟨⟨z.1, z.2.2⟩, by
              obtain ⟨n, hn⟩ := z.2.1
              exact ⟨n, Subtype.ext (by simpa using hn)⟩⟩
            left_inv := fun z => rfl
            right_inv := fun z => rfl }
      rw [this, Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    have hG' := ordProj_dvd_card_pElements Nat.prime_two G
    have hN' := ordProj_dvd_card_pElements Nat.prime_two N
    rw [← hSG, hAB] at hG'
    rw [← hSN] at hN'
    rw [← h1] at hG'
    exact (Nat.dvd_add_right hN').1 (dvd_trans (dvd_mul_right B 2) hG')
  -- hence `|N_G(H)|` divides `m * |H|`, `m` the odd part of `|G|`
  set m := Nat.card G / 2 ^ (Nat.card G).factorization 2
  have hm : 2 ^ (Nat.card G).factorization 2 * m = Nat.card G :=
    Nat.ordProj_mul_ordCompl_eq_self _ _
  have hNGc : NG.card = Nat.card (normalizer (H : Set G)) := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  have hdvd : NG.card ∣ m * Nat.card H := by
    obtain ⟨t, ht⟩ := hBX
    have hB0 : 0 < B := pow_pos two_pos _
    have : B * (m * Nat.card H) = B * (t * NG.card) := by
      calc B * (m * Nat.card H) = (B * 2 * m) * D.card := by rw [← hDH]; ring
        _ = X.card * NG.card := by rw [← hAB, hm, Nat.card_eq_fintype_card, hcount]
        _ = B * (t * NG.card) := by rw [ht]; ring
    rw [Nat.eq_of_mul_eq_mul_left hB0 this]
    exact dvd_mul_left _ _
  -- so `N_P(H) = H`
  set K := (P : Subgroup G) ⊓ normalizer (H : Set G)
  have hHK : H ≤ K := le_inf (zpowers_le.2 hxP) le_normalizer
  have hKH : H = K := by
    refine eq_of_le_of_card_ge hHK ?_
    have hK1 : Nat.card K ∣ NG.card := hNGc ▸ card_dvd_of_le inf_le_right
    have hK2 : Nat.card K ∣ 2 ^ (Nat.card G).factorization 2 :=
      P.card_eq_multiplicity ▸ card_dvd_of_le inf_le_left
    obtain ⟨r, -, hr⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hK2
    have hcop : Nat.Coprime (2 ^ r) m := (Nat.coprime_ordCompl Nat.prime_two hG0).pow_left r
    rw [hr] at hK1 ⊢
    exact Nat.le_of_dvd Nat.card_pos (hcop.dvd_of_dvd_mul_left (hK1.trans hdvd))
  -- the normalizer condition in the `2`-group `P` gives `H = P`
  have : Group.IsNilpotent P := IsPGroup.isNilpotent P.isPGroup'
  have hHP : H ≤ P := zpowers_le.2 hxP
  have htop : H.subgroupOf P = ⊤ := by
    by_contra hne
    have hlt := Group.normalizerCondition_of_isNilpotent _ (lt_top_iff_ne_top.2 hne)
    rw [← subgroupOf_normalizer_eq hHP] at hlt
    obtain ⟨y, hy1, hy2⟩ := IsConcreteLE.exists_of_lt hlt
    rw [mem_subgroupOf] at hy1 hy2
    exact hy2 (by rw [hKH]; exact ⟨y.2, hy1⟩)
  have hPH : (P : Subgroup G) = H := le_antisymm (subgroupOf_eq_top.1 htop) hHP
  rcases hG P with h | h
  · have : x ∈ (⊥ : Subgroup G) := h ▸ hxP
    exact hxN (by rw [mem_bot.1 this]; exact one_mem N)
  · exact h (by rw [hPH]; exact isCyclic_zpowers x)

end Existence

section Construction

variable {G : Type u} [Group G]

/-- `m ~ n` iff `m = u ^ k * n * v ^ l` with `k + l` even: the orbits of the commuting
permutations `n ↦ u⁻² n` and `n ↦ u⁻¹ n v`. -/
def paritySetoid (u v : G) : Setoid G where
  r m n := ∃ k l : ℤ, Even (k + l) ∧ m = u ^ k * n * v ^ l
  iseqv :=
    { refl := fun m => ⟨0, 0, by simp, by simp⟩
      symm := fun {m n} ⟨k, l, h, e⟩ => ⟨-k, -l, by rw [← neg_add]; exact h.neg, by
        rw [e]; group⟩
      trans := fun {m n o} ⟨k, l, h, e⟩ ⟨k', l', h', e'⟩ => ⟨k + k', l' + l, by
        convert h.add h' using 1; ring, by rw [e, e']; group⟩ }

variable {N : Subgroup G} (hidx : N.index = 2) {u v : G} (hu : u ∉ N) (hv : v ∉ N)
include hidx hu hv

/-- `u ^ k * m * v ^ l ∈ N` for `m ∈ N` and `k + l` even. -/
theorem mem_of_even_add {m : G} (hm : m ∈ N) {k l : ℤ} (h : Even (k + l)) :
    u ^ k * m * v ^ l ∈ N := by
  rw [mul_mem_iff_of_index_two hidx, mul_mem_iff_of_index_two hidx,
    zpow_mem_iff_even_of_index_two hidx hu, zpow_mem_iff_even_of_index_two hidx hv]
  simpa [hm] using Int.even_add.1 h

omit hidx hu hv in
/-- Under (★), the parity of `l` in `u ^ k * r * v ^ l` (with `k + l` even) is determined. -/
theorem even_iff_of_eq (hst : NoOddConj N u v) {r : G} (hr : r ∈ N) {k l k' l' : ℤ}
    (h1 : Even (k + l)) (h2 : Even (k' + l')) (he : u ^ k * r * v ^ l = u ^ k' * r * v ^ l') :
    (Even l ↔ Even l') := by
  by_contra hne
  have hodd : Odd (l' - l) := by
    rw [← Int.not_even_iff_odd, Int.even_sub]
    exact fun h => hne h.symm
  have hodd' : Odd (k - k') := by
    rw [← Int.not_even_iff_odd]
    intro hk
    have : Even ((k + l) - (k' + l') - (k - k')) := (h1.sub h2).sub hk
    rw [show (k + l) - (k' + l') - (k - k') = l - l' by ring, Int.even_sub] at this
    exact hne this
  refine hst r hr _ _ hodd hodd' ?_
  calc r * v ^ (l' - l) * r⁻¹ = u ^ (-k') * (u ^ k' * r * v ^ l') * v ^ (-l) * r⁻¹ := by group
    _ = u ^ (-k') * (u ^ k * r * v ^ l) * v ^ (-l) * r⁻¹ := by rw [he]
    _ = u ^ (k - k') := by group

/-- Under (★) there is a predicate `β` on `G` (the set `B₁ ⊆ N`) that is flipped by
`n ↦ u⁻¹ n v` and by `n ↦ u⁻¹ n v⁻¹` on `N`. -/
theorem exists_parity (hst : NoOddConj N u v) :
    ∃ β : G → Prop, (∀ n ∈ N, β (u⁻¹ * n * v) ↔ ¬ β n) ∧
      (∀ n ∈ N, β (u⁻¹ * n * v⁻¹) ↔ ¬ β n) := by
  let S := paritySetoid u v
  let rep : G → G := fun m => (Quotient.mk S m).out
  have hrep : ∀ m, ∃ k l : ℤ, Even (k + l) ∧ m = u ^ k * rep m * v ^ l := by
    intro m
    obtain ⟨k, l, h, e⟩ := Quotient.mk_out (s := S) m
    exact ⟨-k, -l, by rw [← neg_add]; exact h.neg, by
      rw [show rep m = u ^ k * m * v ^ l from e]; group⟩
  have hrepN : ∀ m ∈ N, rep m ∈ N := by
    intro m hm
    obtain ⟨k, l, h, e⟩ := Quotient.mk_out (s := S) m
    rw [show rep m = u ^ k * m * v ^ l from e]
    exact mem_of_even_add hidx hu hv hm h
  have hrep_eq : ∀ (m : G) (a b : ℤ), Even (a + b) → rep (u ^ a * m * v ^ b) = rep m := fun m a b h =>
    congrArg Quotient.out (Quotient.sound (s := S) ⟨a, b, h, rfl⟩)
  let β : G → Prop := fun m => ∃ k l : ℤ, Even (k + l) ∧ Even l ∧ m = u ^ k * rep m * v ^ l
  have hβ : ∀ m ∈ N, ∀ k l : ℤ, Even (k + l) → m = u ^ k * rep m * v ^ l → (β m ↔ Even l) := by
    intro m hm k l h e
    refine ⟨fun ⟨k', l', h', hl', e'⟩ => ?_, fun hl => ⟨k, l, h, hl, e⟩⟩
    exact (even_iff_of_eq hst (hrepN m hm) h h' (e.symm.trans e')).2 hl'
  have hshift : ∀ n ∈ N, ∀ a b : ℤ, Even (a + b) →
      (β (u ^ a * n * v ^ b) ↔ (β n ↔ Even b)) := by
    intro n hn a b hab
    obtain ⟨k, l, h, e⟩ := hrep n
    have hn' : u ^ a * n * v ^ b ∈ N := mem_of_even_add hidx hu hv hn hab
    have e' : u ^ a * n * v ^ b = u ^ (a + k) * rep (u ^ a * n * v ^ b) * v ^ (l + b) := by
      rw [hrep_eq n a b hab]
      conv_lhs => rw [e]
      group
    have h' : Even ((a + k) + (l + b)) := by
      convert hab.add h using 1; ring
    rw [hβ _ hn' _ _ h' e', hβ n hn k l h e, Int.even_add]
  refine ⟨β, fun n hn => ?_, fun n hn => ?_⟩
  · have := hshift n hn (-1) 1 (by decide)
    simp only [zpow_neg, zpow_one] at this
    rw [this]
    simp
  · have := hshift n hn (-1) (-1) (by decide)
    simp only [zpow_neg, zpow_one] at this
    rw [this]
    simp

omit hu hv in
/-- `|G| = 2 |N|`. -/
theorem card_eq_two_mul [Finite G] : Nat.card G = Nat.card N * 2 := by
  rw [← N.card_mul_index, hidx]

/-- **Step A** of Proposition 11: from a complete mapping `(a, b, c)` of `N` and a predicate `β`
flipped by `n ↦ u⁻¹ n v` and `n ↦ u⁻¹ n v⁻¹`, the triples `(a j, b j, c j)`,
`(a j u, u⁻¹ b j v, c j v)` (for `β (b j)`) and `(a j, b j v, c j v)`, `(a j u, u⁻¹ b j, c j)`
(otherwise) form a complete mapping of `G`. -/
theorem hasCompleteMapping_of_parity [Finite G] (β : G → Prop)
    (hτ : ∀ n ∈ N, β (u⁻¹ * n * v) ↔ ¬ β n) (hρ : ∀ n ∈ N, β (u⁻¹ * n * v⁻¹) ↔ ¬ β n)
    (hN : HasCompleteMapping N) : HasCompleteMapping G := by
  classical
  obtain ⟨J, a, b, c, habc⟩ := hasCompleteMapping_iff_exists_triple.1 hN
  have habc' : ∀ j, (a j : G) * b j = c j := fun j => congrArg Subtype.val (habc j)
  have mem : ∀ x ∈ N, x * v ∉ N ∧ u⁻¹ * x * v ∈ N ∧ u⁻¹ * x ∉ N ∧ x * u ∉ N := by
    intro x hx
    simp [mul_mem_iff_of_index_two hidx, inv_mem_iff, hu, hv, hx]
  have hv1 : v ≠ 1 := fun h => hv (h ▸ one_mem N)
  let A : J × Bool → G := fun p => if p.2 then (a p.1 : G) * u else a p.1
  let B : J × Bool → G := fun p =>
    if p.2 then (if β (b p.1) then u⁻¹ * b p.1 * v else u⁻¹ * b p.1)
    else (if β (b p.1) then b p.1 else b p.1 * v)
  let C : J × Bool → G := fun p =>
    if p.2 then (if β (b p.1) then c p.1 * v else c p.1)
    else (if β (b p.1) then c p.1 else c p.1 * v)
  have hcard : Nat.card G ≤ Nat.card (J × Bool) := by
    rw [Nat.card_prod, Nat.card_congr a, card_eq_two_mul hidx, Nat.card_eq_fintype_card (α := Bool),
      Fintype.card_bool]
  have hbool : ∀ x y : Bool, (x = false ↔ y = false) → x = y := by decide
  have hbool' : ∀ x y : Bool, (x = true ↔ y = true) → x = y := by decide
  -- `A` is injective
  have hA : Function.Injective A := by
    rintro ⟨j, _ | _⟩ ⟨j', _ | _⟩ h <;> simp only [A, ite_true, ite_false, Bool.false_eq_true] at h
    · simp [a.injective (Subtype.ext h)]
    · exact absurd (h ▸ (a j).2) (mem _ (a j').2).2.2.2
    · exact absurd (h.symm ▸ (a j').2) (mem _ (a j).2).2.2.2
    · simp [a.injective (Subtype.ext (mul_right_cancel h))]
  -- `C` is injective
  have hC : Function.Injective C := by
    have hγ : ∀ p, (if C p ∈ N then C p else C p * v⁻¹) = c p.1 := by
      rintro ⟨j, _ | _⟩ <;> by_cases hβ : β (b j) <;>
        simp [C, hβ, (c j).2, mem _ (c j).2]
    have hs : ∀ j, C (j, false) ≠ C (j, true) := by
      intro j
      by_cases hβ : β (b j) <;> simp [C, hβ, hv1, eq_comm (a := (c j : G))]
    rintro ⟨j, s⟩ ⟨j', s'⟩ h
    have hj : j = j' := c.injective (Subtype.ext (by rw [← hγ (j, s), ← hγ (j', s'), h]))
    subst hj
    cases s <;> cases s'
    · rfl
    · exact absurd h (hs j)
    · exact absurd h.symm (hs j)
    · rfl
  -- `B` is injective
  have hB : Function.Injective B := by
    have key1 : ∀ p, B p ∈ N ↔ β (b p.1) := by
      rintro ⟨j, _ | _⟩ <;> by_cases hβ : β (b j) <;> simp [B, hβ, (b j).2, mem _ (b j).2]
    have key2 : ∀ p, β (b p.1) → (β (B p) ↔ p.2 = false) := by
      rintro ⟨j, _ | _⟩ hβ <;> simp [B, hβ, hτ _ (b j).2]
    have key3 : ∀ p, ¬ β (b p.1) → (β (B p * v⁻¹) ↔ p.2 = true) := by
      rintro ⟨j, _ | _⟩ hβ <;> simp [B, hβ, hρ _ (b j).2]
    intro p q h
    have e1 : β (b p.1) ↔ β (b q.1) := by rw [← key1, ← key1, h]
    have e2 : p.2 = q.2 := by
      by_cases hβ : β (b p.1)
      · exact hbool _ _ ((key2 p hβ).symm.trans (h ▸ key2 q (e1.1 hβ)))
      · have h3 := (key3 p hβ).symm.trans (h ▸ key3 q (mt e1.2 hβ))
        exact hbool' _ _ h3
    rcases p with ⟨j, s⟩
    rcases q with ⟨j', s'⟩
    simp only at e1 e2
    subst e2
    by_cases hβ : β (b j)
    · have hβ' := e1.1 hβ
      cases s <;> simp [B, hβ, hβ'] at h <;> simp [h]
    · have hβ' := mt e1.2 hβ
      cases s <;> simp [B, hβ, hβ'] at h <;> simp [h]
  refine HasCompleteMapping.of_triple (Equiv.ofBijective A (hA.bijective_of_nat_card_le hcard))
    (Equiv.ofBijective B (hB.bijective_of_nat_card_le hcard))
    (Equiv.ofBijective C (hC.bijective_of_nat_card_le hcard)) ?_
  rintro ⟨j, _ | _⟩ <;> by_cases hβ : β (b j) <;>
    simp only [Equiv.ofBijective_apply, A, B, C, hβ, ite_true, ite_false, Bool.false_eq_true] <;>
    rw [← habc' j] <;> group

end Construction

/-- **Wilcox, Proposition 11.** If `G` is good and `N` is a normal subgroup of index `2` with a
complete mapping, then `G` has a complete mapping. -/
theorem hasCompleteMapping_of_index_two {G : Type*} [Group G] [Finite G]
    (hG : IsGood G) (N : Subgroup G) [N.Normal] (hidx : N.index = 2)
    (hN : HasCompleteMapping N) : HasCompleteMapping G := by
  obtain ⟨u, v, hu, hv, hst⟩ := exists_noOddConj hG hidx
  obtain ⟨β, hτ, hρ⟩ := exists_parity hidx hu hv hst
  exact hasCompleteMapping_of_parity hidx hu hv β hτ hρ hN

end CFSGOutside.HallPaige
