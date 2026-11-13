import Mathlib

/-!
# The group-theoretic core of Dolfi–Guralnick–Herzog–Praeger, Lemma 4.3

`Good p q G` collects three properties of a finite group `G`:
* (BT) the normalizer of every nontrivial `p`-subgroup has order prime to `q`;
* (cyc) every `q`-subgroup is cyclic;
* (aut) an element of order `p` normalizing a subgroup of order `q` centralizes it.
They pass to subgroups, and force every solvable subgroup to have order not divisible by `p * q`.
-/

namespace CFSGOutside.DolfiGuralnickHerzogPraeger

structure Good (p q : ℕ) (G : Type*) [Group G] : Prop where
  bt : ∀ U : Subgroup G, U ≠ ⊥ → IsPGroup p U → ¬ q ∣ Nat.card (Subgroup.normalizer (U : Set G))
  cyc : ∀ Q : Subgroup G, IsPGroup q Q → IsCyclic Q
  aut : ∀ (R : Subgroup G), Nat.card R = q → ∀ g ∈ Subgroup.normalizer (R : Set G),
    orderOf g = p → g ∈ Subgroup.centralizer (R : Set G)

theorem Good.subgroup {p q : ℕ} {G : Type*} [Group G] [Finite G] (h : Good p q G)
    (K : Subgroup G) : Good p q K where
  bt U hU hp := by
    intro hq
    refine h.bt (U.map K.subtype) ?_ (hp.map _) ?_
    · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective U K.subtype_injective]
    · refine hq.trans ?_
      have hle : (Subgroup.normalizer (U : Set K)).map K.subtype ≤
          Subgroup.normalizer ((U.map K.subtype : Subgroup G) : Set G) := by
        rintro _ ⟨x, hx, rfl⟩
        have hx' : x ∈ Subgroup.normalizer (U : Set K) := hx
        rw [Subgroup.mem_normalizer_iff] at hx' ⊢
        intro y
        constructor
        · intro hy
          obtain ⟨u, hu, rfl⟩ := hy
          exact ⟨x * u * x⁻¹, (hx' u).1 hu, rfl⟩
        · rintro ⟨w, hw, hw'⟩
          have hyK : y ∈ K := by
            have : y = (x⁻¹ * w * x : K) := by
              simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.subtype_apply] at hw' ⊢
              rw [hw']; group
            rw [this]; exact Subtype.property _
          refine ⟨⟨y, hyK⟩, ?_, rfl⟩
          show (⟨y, hyK⟩ : K) ∈ U
          rw [hx']
          have e : x * ⟨y, hyK⟩ * x⁻¹ = w := Subtype.ext (by simpa using hw'.symm)
          rw [e]; exact hw
      have := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_congr (Subgroup.equivMapOfInjective (Subgroup.normalizer (U : Set K)) K.subtype
        K.subtype_injective).toEquiv.symm] at this
  cyc Q hQ := by
    have := h.cyc (Q.map K.subtype) (hQ.map _)
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective Q K.subtype K.subtype_injective).symm.toMonoidHom
      (Subgroup.equivMapOfInjective Q K.subtype K.subtype_injective).symm.surjective
  aut R hR g hg ho := by
    have hcard : Nat.card (R.map K.subtype) = q := by
      rw [← hR]
      exact (Nat.card_congr
        (Subgroup.equivMapOfInjective R K.subtype K.subtype_injective).toEquiv).symm
    have hg' : (g : G) ∈ Subgroup.normalizer ((R.map K.subtype : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      have hg2 := (Subgroup.mem_normalizer_iff.1 hg)
      intro y
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨g * u * g⁻¹, (hg2 u).1 hu, rfl⟩
      · rintro ⟨w, hw, hw'⟩
        have hyK : y ∈ K := by
          have : y = (g⁻¹ * w * g : K) := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.subtype_apply] at hw' ⊢
            rw [hw']; group
          rw [this]; exact Subtype.property _
        refine ⟨⟨y, hyK⟩, ?_, rfl⟩
        show (⟨y, hyK⟩ : K) ∈ R
        rw [hg2]
        have e : g * ⟨y, hyK⟩ * g⁻¹ = w := Subtype.ext (by simpa using hw'.symm)
        rw [e]; exact hw
    have := h.aut _ hcard _ hg' (by rw [Subgroup.orderOf_coe]; exact ho)
    rw [Subgroup.mem_centralizer_iff] at this ⊢
    intro x hx
    have := this (x : G) ⟨x, hx, rfl⟩
    exact Subtype.ext this

lemma index_dvd_of_sup_eq_top {G : Type*} [Group G] [Finite G] (N K : Subgroup G) [K.Normal]
    (h : N ⊔ K = ⊤) : N.index ∣ Nat.card K := by
  have h1 := Subgroup.card_mul_index K
  have h2 := Subgroup.card_mul_index N
  have h3 : K.index = K.relIndex N := by
    rw [← Subgroup.relIndex_sup_right N K, h]; simp
  have h4 := Subgroup.relIndex_mul_card K N
  have hpos : 0 < K.relIndex N := Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card K N) Nat.card_pos
  refine ⟨Nat.card (K ⊓ N : Subgroup G), ?_⟩
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h3] at h1
  rw [← h4] at h2
  nlinarith

lemma Good.bt_zpowers {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (h : Good p q G) (g : G) (hg : orderOf g = p) :
    ¬ q ∣ Nat.card (Subgroup.normalizer (Subgroup.zpowers g : Set G)) := by
  have hp := Fact.out (p := p.Prime)
  refine h.bt _ ?_ (IsPGroup.of_card (n := 1) ?_)
  · intro h0
    have := Nat.card_zpowers g
    rw [h0, hg] at this
    simp at this
    exact hp.one_lt.ne' this.symm
  · rw [Nat.card_zpowers, hg, pow_one]

theorem Good.not_dvd {p q : ℕ} [Fact p.Prime] [Fact q.Prime] :
    ∀ (n : ℕ) (H : Type) [Group H] [Finite H], Nat.card H = n → Good p q H → IsSolvable H →
      ¬ (p ∣ Nat.card H ∧ q ∣ Nat.card H) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H _ _ hn hg hs ⟨hpH, hqH⟩
  have hp := Fact.out (p := p.Prime)
  have hq := Fact.out (p := q.Prime)
  obtain ⟨g, hg1⟩ := exists_prime_orderOf_dvd_card' p hpH
  by_cases hpq : p = q
  · subst hpq
    apply hg.bt_zpowers g hg1
    refine dvd_trans ?_ (Subgroup.card_dvd_of_le (Subgroup.le_normalizer))
    rw [Nat.card_zpowers, hg1]
  have hnt : Nontrivial H := by
    refine nontrivial_of_ne g 1 ?_
    rintro rfl
    simp at hg1
    exact hp.one_lt.ne' hg1.symm
  haveI : Group.IsSolvable H := hs
  set D : Subgroup H := commutator H with hD
  have hDlt : D < ⊤ := IsSolvable.commutator_lt_top_of_nontrivial H
  have hDcard : Nat.card D < n := by
    have h1 := Subgroup.card_mul_index D
    have h2 : D.index ≠ 1 := by
      rw [Ne, Subgroup.index_eq_one]; exact hDlt.ne
    have h3 : D.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h4 : 0 < Nat.card D := Nat.card_pos
    rw [← hn, ← h1]
    nlinarith [Nat.two_le_iff D.index |>.2 ⟨h3, h2⟩]
  have hDgood : Good p q D := hg.subgroup D
  have ihD := ih _ hDcard D rfl hDgood (inferInstance : Group.IsSolvable D)
  by_cases hqD : q ∣ Nat.card D
  · by_cases hpD : p ∣ Nat.card D
    · exact ihD ⟨hpD, hqD⟩
    -- Case B
    let Q : Sylow q D := default
    have hQne : Q.toSubgroup ≠ ⊥ := Sylow.ne_bot_of_dvd_card Q hqD
    set Q' : Subgroup H := Q.toSubgroup.map D.subtype with hQ'
    have hfrat := Sylow.normalizer_sup_eq_top Q
    have hidx := index_dvd_of_sup_eq_top _ D hfrat
    have hpN : p ∣ Nat.card (Subgroup.normalizer (Q' : Set H)) := by
      have h1 := Subgroup.card_mul_index (Subgroup.normalizer (Q' : Set H))
      have : p ∣ Nat.card H := hpH
      rw [← h1] at this
      rcases (Nat.Prime.dvd_mul hp).1 this with h | h
      · exact h
      · exact absurd (h.trans hidx) hpD
    obtain ⟨g, hgo⟩ := exists_prime_orderOf_dvd_card' p hpN
    have hgN : (g : H) ∈ Subgroup.normalizer (Q' : Set H) := g.2
    have hgo' : orderOf (g : H) = p := by rw [Subgroup.orderOf_coe]; exact hgo
    have hQ'p : IsPGroup q Q' := Q.isPGroup'.map _
    haveI : IsCyclic Q' := hg.cyc Q' hQ'p
    have hcardQ : Nat.card Q' = Nat.card Q.toSubgroup :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ D.subtype D.subtype_injective).toEquiv.symm
    have hqQ' : q ∣ Nat.card Q' := by
      rw [hcardQ]; exact Sylow.dvd_card_of_dvd_card Q hqD
    obtain ⟨z, hzo⟩ := exists_prime_orderOf_dvd_card' q hqQ'
    set z' : H := (z : H) with hz'
    have hz'o : orderOf z' = q := by rw [hz', Subgroup.orderOf_coe]; exact hzo
    have key : ∀ a ∈ Subgroup.normalizer (Q' : Set H), ∀ y ∈ Subgroup.zpowers z',
        a * y * a⁻¹ ∈ Subgroup.zpowers z' := by
      intro a ha y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      have hw : a * z' * a⁻¹ ∈ Q' := (Subgroup.mem_normalizer_iff.1 ha z').1 z.2
      let w : Q' := ⟨a * z' * a⁻¹, hw⟩
      have hwo : orderOf w = q := by
        rw [← hz'o, ← Subgroup.orderOf_coe]
        show orderOf (a * z' * a⁻¹) = _
        exact orderOf_injective (MulAut.conj a).toMonoidHom (MulEquiv.injective _) z'
      have hEq : Subgroup.zpowers w = Subgroup.zpowers z := by
        rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, hwo, hzo]
      have : w ∈ Subgroup.zpowers z := hEq ▸ Subgroup.mem_zpowers w
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 this
      have hm' : z' ^ m = a * z' * a⁻¹ := by
        have := congrArg Subtype.val hm
        simpa [hz', w] using this
      rw [← conj_zpow, ← hm']
      exact Subgroup.zpow_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers z') _) _
    set R := Subgroup.zpowers z' with hR
    have hRn : (g : H) ∈ Subgroup.normalizer (R : Set H) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx; exact key _ hgN x hx
      · intro hx
        have := key _ (inv_mem hgN) _ hx
        convert this using 1; group
    have hRcard : Nat.card R = q := by rw [hR, Nat.card_zpowers, hz'o]
    have hcent := hg.aut R hRcard _ hRn hgo'
    rw [Subgroup.mem_centralizer_iff] at hcent
    have hcomm : z' * g = g * z' := hcent z' (Subgroup.mem_zpowers z')
    have hzn : z' ∈ Subgroup.normalizer (Subgroup.zpowers (g : H) : Set H) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hc : ∀ x ∈ Subgroup.zpowers (g : H), z' * x * z'⁻¹ = x := by
        intro x hx
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        have : Commute z' (g : H) := hcomm
        exact (this.zpow_right k).mul_inv_cancel
      constructor
      · intro hx; rw [hc x hx]; exact hx
      · intro hx
        have h2 := hc _ hx
        have h5 : z' * x * z'⁻¹ = x := mul_left_cancel (mul_right_cancel h2)
        rw [h5] at hx; exact hx
    have hle : R ≤ Subgroup.normalizer (Subgroup.zpowers (g : H) : Set H) :=
      (Subgroup.zpowers_le).2 hzn
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hRcard] at hdvd
    exact hg.bt_zpowers _ hgo' hdvd
  · -- Case A
    let S : Sylow p H := default
    set K : Subgroup H := D ⊔ S.toSubgroup with hK
    have hKn : K.Normal := ⟨fun k hk x => by
      have e : x * k * x⁻¹ = (x * k * x⁻¹ * k⁻¹) * k := by group
      have hc : x * k * x⁻¹ * k⁻¹ ∈ D :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top k)
      rw [e]
      exact K.mul_mem ((le_sup_left : D ≤ K) hc) hk⟩
    have hKq : ¬ q ∣ Nat.card K := by
      intro hdvd
      have h1 := Subgroup.relIndex_mul_card D K
      have h2 : D ⊓ K = D := inf_eq_left.2 le_sup_left
      rw [h2] at h1
      have h3 : D.relIndex K = D.relIndex S.toSubgroup := Subgroup.relIndex_sup_left _ D
      have h4 := Subgroup.relIndex_dvd_card D S.toSubgroup
      obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
      rw [← h1] at hdvd
      rcases (Nat.Prime.dvd_mul hq).1 hdvd with h | h
      · have := h.trans (h3 ▸ h4)
        rw [hk] at this
        exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow this)).symm
      · exact hqD h
    have hfrat : Subgroup.normalizer (S.toSubgroup : Set H) ⊔ K = ⊤ :=
      Sylow.normalizer_sup_eq_top' S le_sup_right
    have hidx := index_dvd_of_sup_eq_top _ K hfrat
    have hqN : q ∣ Nat.card (Subgroup.normalizer (S.toSubgroup : Set H)) := by
      have h1 := Subgroup.card_mul_index (Subgroup.normalizer (S.toSubgroup : Set H))
      have : q ∣ Nat.card H := hqH
      rw [← h1] at this
      rcases (Nat.Prime.dvd_mul hq).1 this with h | h
      · exact h
      · exact absurd (h.trans hidx) hKq
    exact hg.bt S.toSubgroup (Sylow.ne_bot_of_dvd_card S hpH) S.isPGroup' hqN

/-- The abstract form of Lemma 4.3. -/
theorem not_isSolvable_closure {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {G : Type} [Group G]
    [Finite G] (h : Good p q G) (x y : G) (hx : orderOf x = p) (hy : orderOf y = q) :
    ¬ IsSolvable (Subgroup.closure {x, y}) := by
  intro hs
  set H : Subgroup G := Subgroup.closure {x, y}
  have hxH : x ∈ H := Subgroup.subset_closure (by simp)
  have hyH : y ∈ H := Subgroup.subset_closure (by simp)
  apply Good.not_dvd (Nat.card H) H rfl (h.subgroup H) hs
  constructor
  · rw [← hx, ← Subgroup.orderOf_mk x hxH]; exact orderOf_dvd_natCard _
  · rw [← hy, ← Subgroup.orderOf_mk y hyH]; exact orderOf_dvd_natCard _

end CFSGOutside.DolfiGuralnickHerzogPraeger
