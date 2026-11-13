import CFSGOutside.Arad.Basic

/-!
# Arad, Theorem B(iii): reduction to simple groups

A minimal counterexample argument: if every nonabelian simple group satisfying the hypothesis has no prime of
`π` in its order, then every group satisfying it has a normal Hall π′-subgroup. The extension step is Arad's
Lemma 2.3 (Baer); it uses the Schur–Zassenhaus theorem and the corpus theorem that a coprime `p`-group
normalizes a Sylow subgroup.
-/

namespace CFSGOutside.Arad

open Subgroup

/-- `K` is a normal Hall π′-subgroup of `G`: normal, of π′-order and of π-index. -/
def IsNormalPiPrimeHall (π : Set ℕ) {G : Type*} [Group G] (K : Subgroup G) : Prop :=
  K.Normal ∧ (∀ p : ℕ, p.Prime → p ∣ Nat.card K → p ∉ π) ∧
    (∀ p : ℕ, p.Prime → p ∣ K.index → p ∈ π)

section Hall

variable {G : Type*} [Group G] [Finite G] {π : Set ℕ}

/-- A normal Hall π′-subgroup consists of the π′-elements. -/
theorem IsNormalPiPrimeHall.mem_iff {K : Subgroup G} (hK : IsNormalPiPrimeHall π K) (g : G) :
    g ∈ K ↔ IsPiPrimeElement π g := by
  obtain ⟨hN, hc, hi⟩ := hK
  constructor
  · intro hg p hp hpd
    refine hc p hp (hpd.trans ?_)
    rw [← Subgroup.orderOf_mk g hg]
    exact orderOf_dvd_natCard _
  · intro hg
    by_contra hgK
    have h1 : ((g : G ⧸ K)) ≠ 1 := fun h => hgK ((QuotientGroup.eq_one_iff g).mp h)
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (orderOf_eq_one_iff.not.mpr h1)
    exact hg p hp (hpd.trans (orderOf_map_dvd (QuotientGroup.mk' K) g))
      (hi p hp (hpd.trans (orderOf_dvd_natCard _)))

theorem isPiPrimeClosed_of_isNormalPiPrimeHall {K : Subgroup G} (hK : IsNormalPiPrimeHall π K) :
    IsPiPrimeClosed π G :=
  ⟨K, hK.mem_iff⟩

end Hall

section Coprime

variable {G : Type} [Group G] [Finite G] {π : Set ℕ}

theorem isPGroup_zpowers_of_pow_eq_one {s k : ℕ} {x : G} (hx : x ^ (s ^ k) = 1) :
    IsPGroup s (zpowers x) := by
  rintro ⟨_, i, rfl⟩
  refine ⟨k, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, Subgroup.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

/-- An `s`-element (`s ∉ π`) normalizing a π-subgroup centralizes it. -/
theorem mem_centralizer_of_sElement [CFSGOutside.Corpus.ExistsIsSylowOfNormalizedOfCoprime.{0}]
    (h : HomP π G) {H : Subgroup G} (hH : IsPiGroup π H) {s : ℕ} (hs : s.Prime) (hsπ : s ∉ π)
    {x : G} (hx : x ∈ normalizer (H : Set G)) {k : ℕ} (hk : x ^ (s ^ k) = 1) :
    x ∈ centralizer (H : Set G) := by
  have hA := isPGroup_zpowers_of_pow_eq_one hk
  have hAH : zpowers x ≤ normalizer (H : Set G) := (zpowers_le).mpr hx
  have hsH : ¬ s ∣ Nat.card H := fun hd => hsπ (hH s hs hd)
  let D : Subgroup H := (centralizer ({x} : Set G)).subgroupOf H
  have hD : D = ⊤ := by
    apply Subgroup.index_eq_one.mp
    by_contra hne
    obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hne
    haveI : Fact r.Prime := ⟨hr⟩
    obtain ⟨R, ⟨Q, hQ⟩, hAR⟩ :=
      CFSGOutside.Corpus.ExistsIsSylowOfNormalizedOfCoprime.exists_isSylowOf_normalized_of_coprime
        (r := r) hs hr hA hAH hsH
    have hQD : (Q : Subgroup H) ≤ D := by
      by_cases hR : R = ⊥
      · intro z hz
        have : (z : G) ∈ R := hQ ▸ ⟨z, hz, rfl⟩
        rw [hR, mem_bot] at this
        have : z = 1 := Subtype.ext this
        rw [this]; exact one_mem _
      · have hRr : IsPGroup r R := hQ ▸ Q.isPGroup'.map H.subtype
        have hrπ : r ∈ π := by
          obtain ⟨z, hz⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hR
          obtain ⟨n, hn⟩ := hRr z
          have hz1 : orderOf (z : G) ≠ 1 := by
            rw [Ne, orderOf_eq_one_iff]; exact fun h' => hz (Subtype.ext h')
          have hzR : (z : G) ∈ H := by
            obtain ⟨w, -, hw⟩ := (hQ ▸ z.2 : (z : G) ∈ (Q : Subgroup H).map H.subtype)
            rw [← hw]; exact w.2
          obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hr).mp
            (orderOf_dvd_of_pow_eq_one (by rw [← Subgroup.coe_pow, hn, Subgroup.coe_one] :
              (z : G) ^ (r ^ n) = 1))
          rcases i with _ | i
          · exact absurd (by simpa using hi) hz1
          · refine hH r hr (dvd_trans ?_ (orderOf_dvd_natCard (⟨z, hzR⟩ : H)))
            rw [Subgroup.orderOf_mk, hi]
            exact dvd_pow_self r (Nat.succ_ne_zero i)
        have hxR : x ∈ normalizer (R : Set G) := hAR (mem_zpowers x)
        have hc := h r hr hrπ R hR hRr s hs hsπ x hxR ⟨k, hk⟩
        intro z hz
        have hzR : (z : G) ∈ R := hQ ▸ ⟨z, hz, rfl⟩
        change (z : G) ∈ centralizer ({x} : Set G)
        rw [mem_centralizer_singleton_iff]
        exact (mem_centralizer_iff.mp hc) z hzR
    exact (Sylow.not_dvd_index Q) (hrd.trans (index_dvd_of_le hQD))
  rw [mem_centralizer_iff]
  intro z hz
  have : (⟨z, hz⟩ : H) ∈ D := hD ▸ mem_top _
  exact mem_centralizer_singleton_iff.mp this

/-- A π′-element normalizing a π-subgroup centralizes it. -/
theorem mem_centralizer_of_isPiPrimeElement [CFSGOutside.Corpus.ExistsIsSylowOfNormalizedOfCoprime.{0}]
    (h : HomP π G) {H : Subgroup G} (hH : IsPiGroup π H) :
    ∀ x ∈ normalizer (H : Set G), IsPiPrimeElement π x → x ∈ centralizer (H : Set G) := by
  intro x
  induction hn : orderOf x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
  intro hx hxπ
  by_cases h1 : n = 1
  · rw [h1, orderOf_eq_one_iff] at hn; rw [hn]; exact one_mem _
  obtain ⟨s, hs, hsd⟩ := Nat.exists_prime_and_dvd h1
  have hn0 : n ≠ 0 := by rw [← hn]; exact (orderOf_pos x).ne'
  obtain ⟨a, m, hm, hnam⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 s hs.ne_one
  have ha : a ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hnam
    exact hm (hnam ▸ hsd)
  have hcop : Nat.Coprime (s ^ a) m :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hs).mpr hm)
  -- `x = (x ^ (s ^ a)) ^ u * (x ^ m) ^ v`
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * (s ^ a : ℕ) + v * m = 1 := by
    obtain ⟨u, v, h'⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    exact ⟨u, v, h'⟩
  have hxeq : x = (x ^ (s ^ a)) ^ u * (x ^ m) ^ v := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, mul_comm _ u,
      mul_comm _ v]
    push_cast at huv ⊢
    rw [huv, zpow_one]
  rw [hxeq]
  refine mul_mem (zpow_mem ?_ u) (zpow_mem ?_ v)
  · -- `x ^ (s ^ a)` has smaller order
    have hord : orderOf (x ^ (s ^ a)) = m := by
      rw [orderOf_pow' x (pow_ne_zero a hs.ne_zero), hn, hnam, Nat.gcd_mul_right_left]
      · exact Nat.mul_div_cancel_left m (pow_pos hs.pos a)
    have hlt : m < n := by
      rw [hnam]
      exact lt_mul_left (Nat.pos_of_ne_zero (by rintro rfl; simp at hnam; exact hn0 hnam))
        (Nat.one_lt_pow ha hs.one_lt)
    refine ih m hlt (x ^ (s ^ a)) hord (pow_mem hx _) ?_
    intro p hp hpd
    exact hxπ p hp (hpd.trans (orderOf_pow_dvd _))
  · -- `x ^ m` is an `s`-element
    have hsm : (x ^ m) ^ (s ^ a) = 1 := by
      rw [← pow_mul, mul_comm, ← hnam, ← hn, pow_orderOf_eq_one]
    have hsπ : s ∉ π := hxπ s hs (hn ▸ hsd)
    exact mem_centralizer_of_sElement h hH hs hsπ (pow_mem hx m) hsm

end Coprime

section Induction

variable {π : Set ℕ}

theorem coprime_of_primes {a b : ℕ} (ha : ∀ p : ℕ, p.Prime → p ∣ a → p ∈ π)
    (hb : ∀ p : ℕ, p.Prime → p ∣ b → p ∉ π) : Nat.Coprime a b :=
  Nat.coprime_of_dvd fun p hp hpa hpb => hb p hp hpb (ha p hp hpa)

/-- The group itself is a normal Hall π′-subgroup when no prime of `π` divides `|G|`. -/
theorem isNormalPiPrimeHall_top {G : Type*} [Group G]
    (h : ∀ p : ℕ, p.Prime → p ∈ π → ¬ p ∣ Nat.card G) : IsNormalPiPrimeHall π (⊤ : Subgroup G) := by
  refine ⟨inferInstance, fun p hp hpd hpπ => h p hp hpπ (by rwa [card_top] at hpd), ?_⟩
  intro p hp hpd
  rw [index_top, Nat.dvd_one] at hpd
  exact absurd hpd hp.ne_one

theorem exists_normal_ne_bot_ne_top {G : Type*} [Group G] [Nontrivial G] (h : ¬ IsSimpleGroup G) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  by_contra hc
  push Not at hc
  exact h ⟨fun N hN => by
    by_cases hb : N = ⊥
    · exact Or.inl hb
    · exact Or.inr (hc N hN hb)⟩

/-- The extension step (Arad's Lemma 2.3 for a normal subgroup that is a π-group or a π′-group). -/
theorem extension [CFSGOutside.Corpus.ExistsIsSylowOfNormalizedOfCoprime.{0}]
    {G : Type} [Group G] [Finite G] (hH : HomP π G) (N : Subgroup G) [N.Normal]
    (hN : IsPiGroup π N ∨ ∀ p : ℕ, p.Prime → p ∣ Nat.card N → p ∉ π)
    {Lb : Subgroup (G ⧸ N)} (hLb : IsNormalPiPrimeHall π Lb) :
    ∃ K : Subgroup G, IsNormalPiPrimeHall π K := by
  classical
  obtain ⟨hLbN, hLbc, hLbi⟩ := hLb
  set q := QuotientGroup.mk' N
  set L : Subgroup G := Lb.comap q
  have hLN : L.Normal := hLbN.comap q
  have hLi : L.index = Lb.index := index_comap_of_surjective Lb (QuotientGroup.mk'_surjective N)
  have hNL : N ≤ L := by
    intro n hn
    change q n ∈ Lb
    rw [show q n = 1 from (QuotientGroup.eq_one_iff n).mpr hn]
    exact one_mem _
  have hcardL : Nat.card L = Nat.card N * Nat.card Lb := by
    have h1 := L.card_mul_index
    have h2 := card_eq_card_quotient_mul_card_subgroup N
    have h3 := Lb.card_mul_index
    have hpos : 0 < Lb.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc Nat.card L * Lb.index = Nat.card G := hLi ▸ h1
      _ = Nat.card (G ⧸ N) * Nat.card N := h2
      _ = Nat.card Lb * Lb.index * Nat.card N := by rw [h3]
      _ = Nat.card N * Nat.card Lb * Lb.index := by ring
  rcases hN with hNπ | hNπ'
  · -- `N` is a π-group: split `L = N × X`
    have hNcard : Nat.card (N.subgroupOf L) = Nat.card N :=
      Nat.card_congr (subgroupOfEquivOfLe hNL).toEquiv
    have hNidx : (N.subgroupOf L).index = Nat.card Lb := by
      have := (N.subgroupOf L).card_mul_index
      rw [hNcard, hcardL] at this
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos this
    have hcop : Nat.Coprime (Nat.card (N.subgroupOf L)) (N.subgroupOf L).index := by
      rw [hNcard, hNidx]
      exact coprime_of_primes hNπ hLbc
    obtain ⟨X, hX⟩ := exists_right_complement'_of_coprime hcop
    have hXcard : Nat.card X = Nat.card Lb := by
      have := hX.card_mul
      rw [hNcard, hcardL] at this
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos this
    set X₀ : Subgroup G := X.map L.subtype
    have hX₀card : Nat.card X₀ = Nat.card Lb := by
      rw [← hXcard]; exact Subgroup.card_map_of_injective L.subtype_injective
    have hX₀L : X₀ ≤ L := map_subtype_le _
    have hX₀π' : ∀ x ∈ X₀, IsPiPrimeElement π x := by
      intro x hx p hp hpd
      refine hLbc p hp (hX₀card ▸ hpd.trans ?_)
      rw [← Subgroup.orderOf_mk x hx]
      exact orderOf_dvd_natCard _
    have hX₀C : ∀ x ∈ X₀, x ∈ centralizer (N : Set G) := by
      intro x hx
      refine mem_centralizer_of_isPiPrimeElement hH hNπ x ?_ (hX₀π' x hx)
      rw [mem_normalizer_iff]
      intro h
      exact ⟨fun hh => ‹N.Normal›.conj_mem h hh x,
        fun hh => by simpa [mul_assoc] using ‹N.Normal›.conj_mem _ hh x⁻¹⟩
    have hX₀N : X₀.Normal := by
      constructor
      intro x hx g
      set y := g * x * g⁻¹
      have hyL : y ∈ L := hLN.conj_mem x (hX₀L hx) g
      obtain ⟨⟨n', x'⟩, hnx, -⟩ := hX.existsUnique ⟨y, hyL⟩
      have hn : ((n' : L) : G) ∈ N := n'.2
      have hx' : ((x' : L) : G) ∈ X₀ := ⟨x', x'.2, rfl⟩
      have hyeq : y = ((n' : L) : G) * ((x' : L) : G) := by
        have := congrArg Subtype.val hnx
        rw [Subgroup.coe_mul] at this
        exact this.symm
      have hcomm : Commute ((n' : L) : G) ((x' : L) : G) :=
        ((mem_centralizer_iff.mp (hX₀C _ hx')) _ hn)
      set m := orderOf y
      have hym : y ^ m = 1 := pow_orderOf_eq_one y
      have hnm : ((n' : L) : G) ^ m = (((x' : L) : G) ^ m)⁻¹ := by
        rw [hyeq, hcomm.mul_pow] at hym
        exact eq_inv_of_mul_eq_one_left hym
      have hcopNX : Nat.Coprime (Nat.card N) (Nat.card X₀) := by
        rw [hX₀card]; exact coprime_of_primes hNπ hLbc
      have hnmN : ((n' : L) : G) ^ m ∈ N := pow_mem hn m
      have hnmX : ((n' : L) : G) ^ m ∈ X₀ := hnm ▸ X₀.inv_mem (pow_mem hx' m)
      have hd1 : orderOf (((n' : L) : G) ^ m) ∣ Nat.card N := by
        rw [← Subgroup.orderOf_mk _ hnmN]; exact orderOf_dvd_natCard _
      have hd2 : orderOf (((n' : L) : G) ^ m) ∣ Nat.card X₀ := by
        rw [← Subgroup.orderOf_mk _ hnmX]; exact orderOf_dvd_natCard _
      have hnm1 : ((n' : L) : G) ^ m = 1 := by
        have := Nat.dvd_gcd hd1 hd2
        rw [hcopNX.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at this
        exact this
      have hoy : orderOf y = orderOf x :=
        orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
      have hn1 : ((n' : L) : G) = 1 := by
        rw [← orderOf_eq_one_iff]
        by_contra hne
        obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
        have h1 : p ∣ orderOf x := hoy ▸ hpd.trans (orderOf_dvd_of_pow_eq_one hnm1)
        have h2 : p ∣ Nat.card N := by
          refine hpd.trans ?_
          rw [← Subgroup.orderOf_mk _ hn]; exact orderOf_dvd_natCard _
        exact hX₀π' x hx p hp h1 (hNπ p hp h2)
      rw [hyeq, hn1, one_mul]
      exact hx'
    refine ⟨X₀, hX₀N, fun p hp hpd => hLbc p hp (hX₀card ▸ hpd), fun p hp hpd => ?_⟩
    have hidx : X₀.index = Nat.card N * Lb.index := by
      have h1 := X₀.card_mul_index
      have h2 := L.card_mul_index
      rw [← h1, hcardL, hLi, hX₀card] at h2
      apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Lb))
      linarith [h2]
    rw [hidx] at hpd
    rcases (Nat.Prime.dvd_mul hp).mp hpd with h | h
    · exact hNπ p hp h
    · exact hLbi p hp h
  · -- `N` is a π′-group: `L` itself is a normal Hall π′-subgroup
    refine ⟨L, hLN, fun p hp hpd => ?_, fun p hp hpd => hLbi p hp (hLi ▸ hpd)⟩
    rw [hcardL] at hpd
    rcases (Nat.Prime.dvd_mul hp).mp hpd with h | h
    · exact hNπ' p hp h
    · exact hLbc p hp h

/-- **Reduction to simple groups.** For a property `C` of groups inherited by subgroups and quotient groups,
if no nonabelian simple group with `C` and `HomP π` has a prime of `π` in its order, then every finite group with
`C` and `HomP π` has a normal Hall π′-subgroup. -/
theorem exists_isNormalPiPrimeHall [CFSGOutside.Corpus.ExistsIsSylowOfNormalizedOfCoprime.{0}]
    (C : (G : Type) → [Group G] → Prop)
    (hsub : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G), C G → C H)
    (hquot : ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G) [N.Normal], C G → C (G ⧸ N))
    (hsimple : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      C G → HomP π G → ∀ p : ℕ, p.Prime → p ∈ π → ¬ p ∣ Nat.card G)
    (G : Type) [Group G] [Finite G] (hC : C G) (hH : HomP π G) :
    ∃ K : Subgroup G, IsNormalPiPrimeHall π K := by
  classical
  induction hn : Nat.card G using Nat.strong_induction_on generalizing G with
  | _ n ih =>
  by_cases hall : ∀ p : ℕ, p.Prime → p ∈ π → ¬ p ∣ Nat.card G
  · exact ⟨⊤, isNormalPiPrimeHall_top hall⟩
  push Not at hall
  obtain ⟨p₀, hp₀, -, hp₀d⟩ := hall
  have hnt : Nontrivial G := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    by_contra h1
    have : Nat.card G = 1 := le_antisymm (not_lt.mp h1) Nat.card_pos
    rw [this] at hp₀d
    exact hp₀.ne_one (Nat.dvd_one.mp hp₀d)
  by_cases hsimp : IsSimpleGroup G
  · by_cases hcomm : ∀ a b : G, a * b = b * a
    · -- an abelian simple group has prime order
      letI : CommGroup G := { ‹Group G› with mul_comm := hcomm }
      have hpr : (Nat.card G).Prime := IsSimpleGroup.prime_card
      by_cases hπ : Nat.card G ∈ π
      · refine ⟨⊥, inferInstance, fun p hp hpd => ?_, fun p hp hpd => ?_⟩
        · rw [card_bot, Nat.dvd_one] at hpd; exact absurd hpd hp.ne_one
        · rw [index_bot] at hpd
          rwa [(Nat.prime_dvd_prime_iff_eq hp hpr).mp hpd]
      · refine ⟨⊤, isNormalPiPrimeHall_top fun p hp hpπ hpd => hπ ?_⟩
        rwa [← (Nat.prime_dvd_prime_iff_eq hp hpr).mp hpd]
    · push Not at hcomm
      exact ⟨⊤, isNormalPiPrimeHall_top (hsimple G hcomm hC hH)⟩
  -- `G` has a proper nontrivial normal subgroup `N`
  obtain ⟨N, hNn, hNb, hNt⟩ := exists_normal_ne_bot_ne_top hsimp
  have hcardN : Nat.card N < n := by
    rw [← hn]
    have h1 := N.card_mul_index
    have h2 : N.index ≠ 1 := fun h => hNt (Subgroup.index_eq_one.mp h)
    have h3 : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h4 : 0 < Nat.card N := Nat.card_pos
    nlinarith [Nat.two_le_iff N.index |>.mpr ⟨h3, h2⟩]
  obtain ⟨KN, hKN⟩ := ih _ hcardN N (hsub G N hC) (homP_subgroup hH N) rfl
  -- a normal subgroup `N₁ ≠ 1` that is a π-group or a π′-group
  obtain ⟨N₁, hN₁n, hN₁b, hN₁⟩ : ∃ N₁ : Subgroup G, N₁.Normal ∧ N₁ ≠ ⊥ ∧
      (IsPiGroup π N₁ ∨ ∀ p : ℕ, p.Prime → p ∣ Nat.card N₁ → p ∉ π) := by
    set K₀ : Subgroup G := KN.map N.subtype
    by_cases hK₀ : K₀ = ⊥
    · refine ⟨N, hNn, hNb, Or.inl fun p hp hpd => hKN.2.2 p hp ?_⟩
      have : KN = ⊥ := (map_eq_bot_iff_of_injective KN N.subtype_injective).mp hK₀
      rwa [this, index_bot]
    · refine ⟨K₀, ⟨fun x hx g => ?_⟩, hK₀, Or.inr fun p hp hpd => hKN.2.1 p hp ?_⟩
      · obtain ⟨x, hxK, rfl⟩ := hx
        have hgx : g * (x : G) * g⁻¹ ∈ N := hNn.conj_mem x x.2 g
        refine ⟨⟨_, hgx⟩, (hKN.mem_iff _).mpr ?_, rfl⟩
        intro p hp hpd
        have hox : orderOf (⟨_, hgx⟩ : N) = orderOf x := by
          rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe x]
          exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective _
        exact (hKN.mem_iff x).mp hxK p hp (hox ▸ hpd)
      · rwa [← Subgroup.card_map_of_injective N.subtype_injective]
  have hcardQ : Nat.card (G ⧸ N₁) < n := by
    rw [← hn, card_eq_card_quotient_mul_card_subgroup N₁]
    have h1 : 1 < Nat.card N₁ := by
      rw [Finite.one_lt_card_iff_nontrivial]
      exact (Subgroup.nontrivial_iff_ne_bot N₁).mpr hN₁b
    have h2 : 0 < Nat.card (G ⧸ N₁) := Nat.card_pos
    nlinarith
  obtain ⟨Lb, hLb⟩ := ih _ hcardQ (G ⧸ N₁) (hquot G N₁ hC) (homP_quotient hH N₁) rfl
  exact extension hH N₁ hN₁ hLb

end Induction

end CFSGOutside.Arad
