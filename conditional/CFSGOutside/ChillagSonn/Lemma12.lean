import CFSGOutside.ChillagSonn.Metacyclic
import CFSGOutside.Corpus.FrattiniQuotientFacts

/-!
# Chillag–Sonn: Lemmas (1.1)(c) and (1.2)

A group of order `p³`, `p` odd, which is a product of two subgroups of exponent `p` has exponent `p`
(Lemma (1.1)(c)); in a metacyclic `p`-group `P₁ ⋊ P₂` with `P₁ ≠ 1` the complement `P₂` is cyclic, and for `p` odd
and `P₂ ≠ 1` so is `P₁` (Lemma (1.2)).
-/

namespace CFSGOutside.ChillagSonn

open CFSGOutside.Corpus Subgroup
open scoped commutatorElement

universe u

/-- If `c` is central and `y * x = c * x * y`, then `y ^ n * x = c ^ n * x * y ^ n`. -/
private theorem pow_mul_eq_of_central {G : Type*} [Group G] {x y c : G} (hc : ∀ z, Commute c z)
    (hyx : y * x = c * x * y) (n : ℕ) : y ^ n * x = c ^ n * x * y ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc y ^ (n + 1) * x = y ^ n * c * x * y := by rw [pow_succ, mul_assoc, hyx]; simp only [mul_assoc]
      _ = c * (y ^ n * x) * y := by rw [← (hc (y ^ n)).eq]; simp only [mul_assoc]
      _ = c ^ (n + 1) * x * y ^ (n + 1) := by rw [ih, pow_succ', pow_succ]; simp only [mul_assoc]

/-- If `c` is central and `y * x = c * x * y`, then `(x * y) ^ n = c ^ (n.choose 2) * x ^ n * y ^ n`. -/
private theorem mul_pow_of_central {G : Type*} [Group G] {x y c : G} (hc : ∀ z, Commute c z)
    (hyx : y * x = c * x * y) (n : ℕ) : (x * y) ^ n = c ^ (n.choose 2) * x ^ n * y ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hch : (n + 1).choose 2 = n.choose 2 + n := by rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
    calc (x * y) ^ (n + 1) = c ^ n.choose 2 * x ^ n * (y ^ n * x) * y := by
          rw [pow_succ, ih]; simp only [mul_assoc]
      _ = c ^ n.choose 2 * (x ^ n * c ^ n) * x * y ^ n * y := by
          rw [pow_mul_eq_of_central hc hyx]; simp only [mul_assoc]
      _ = c ^ n.choose 2 * c ^ n * (x ^ n * x) * (y ^ n * y) := by
          rw [← ((hc (x ^ n)).pow_left n).eq]; simp only [mul_assoc]
      _ = _ := by rw [← pow_add, ← pow_succ, ← pow_succ, hch]

/-- Lemma (1.1)(c): a group of order `p³`, `p` odd, which is a product of two subgroups of exponent `p`, has
exponent `p`. -/
theorem pow_eq_one_of_card_eq_cube {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hcard : Nat.card P = p ^ 3) (P₁ P₂ : Subgroup P) (hprod : ∀ x : P, ∃ a ∈ P₁, ∃ b ∈ P₂, x = a * b)
    (h₁ : ∀ x ∈ P₁, x ^ p = 1) (h₂ : ∀ x ∈ P₂, x ^ p = 1) : ∀ x : P, x ^ p = 1 := by
  have hp : p.Prime := Fact.out
  have hcomm : IsMulCommutative (P ⧸ center P) := by
    obtain ⟨k, hk, hZ⟩ := IsPGroup.card_center_eq_prime_pow hcard (by norm_num)
    have hdvd : Nat.card (P ⧸ center P) ∣ p ^ 2 := by
      refine Nat.dvd_of_mul_dvd_mul_right hp.pos ?_
      rw [← pow_succ, ← hcard, card_eq_card_quotient_mul_card_subgroup (center P), hZ]
      exact mul_dvd_mul_left _ (dvd_pow_self p hk.ne')
    obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    rcases Nat.lt_or_ge m 2 with h | h
    · have : IsCyclic (P ⧸ center P) :=
        isCyclic_of_card_dvd_prime (p := p) (hm' ▸ (pow_dvd_pow p (show m ≤ 1 by lia)).trans (pow_one p).dvd)
      infer_instance
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) (by rw [hm', le_antisymm hm h])
  intro x
  obtain ⟨a, ha, b, hb, rfl⟩ := hprod x
  have hc : ∀ z, Commute ⁅b, a⁆ z := by
    have : ⁅b, a⁆ ∈ center P := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact hcomm.is_comm.comm _ _
    exact fun z ↦ ((mem_center_iff.mp this) z).symm
  have hba : b * a = ⁅b, a⁆ * a * b := by simp [commutatorElement_def, mul_assoc]
  have hcp : ⁅b, a⁆ ^ p = 1 := by
    have := pow_mul_eq_of_central hc hba p
    rwa [h₂ b hb, one_mul, mul_one, right_eq_mul] at this
  obtain ⟨m, hm⟩ := hp.dvd_choose_self two_ne_zero (lt_of_le_of_ne hp.two_le (Ne.symm hp2))
  rw [mul_pow_of_central hc hba, h₁ a ha, h₂ b hb, hm, pow_mul, hcp]
  simp

/-- A finite group with cyclic Frattini quotient is cyclic. -/
theorem isCyclic_of_isCyclic_quotient_frattini {Q : Type*} [Group Q] [Finite Q]
    (h : IsCyclic (Q ⧸ frattini Q)) : IsCyclic Q := by
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp h
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  refine isCyclic_iff_exists_zpowers_eq_top.mpr ⟨x, frattini_nongenerating ?_⟩
  rw [← QuotientGroup.ker_mk' (frattini Q), ← comap_map_eq, MonoidHom.map_zpowers, QuotientGroup.mk'_apply, hg,
    comap_top]

/-- The Frattini quotient of a metacyclic `p`-group has order dividing `p²`. -/
theorem card_quotient_frattini_dvd [FrattiniElementaryQuotient.{u}] {Q : Type u} [Group Q] [Finite Q] {p : ℕ}
    [Fact p.Prime] (hQ : IsPGroup p Q) (hM : IsMetacyclic Q) : Nat.card (Q ⧸ frattini Q) ∣ p ^ 2 :=
  (hM.of_surjective _ (QuotientGroup.mk'_surjective _)).card_dvd_sq
    (FrattiniElementaryQuotient.frattini_elementary_quotient hQ).2.2.1

/-- The Frattini quotient of a noncyclic metacyclic `p`-group has order `p²`. -/
theorem card_quotient_frattini_eq [FrattiniElementaryQuotient.{u}] {Q : Type u} [Group Q] [Finite Q] {p : ℕ}
    [Fact p.Prime] (hQ : IsPGroup p Q) (hM : IsMetacyclic Q) (hc : ¬ IsCyclic Q) :
    Nat.card (Q ⧸ frattini Q) = p ^ 2 := by
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Fact.out).mp (card_quotient_frattini_dvd hQ hM)
  rcases Nat.lt_or_ge k 2 with h | h
  · exact (hc (isCyclic_of_isCyclic_quotient_frattini
      (isCyclic_of_card_dvd_prime (p := p) (hk' ▸ (pow_dvd_pow p (show k ≤ 1 by lia)).trans (pow_one p).dvd)))).elim
  · rw [hk', le_antisymm hk h]

/-- Lemma (1.2)(a): if a metacyclic `p`-group is a semidirect product `P₁ ⋊ P₂` with `P₁ ≠ 1`, then `P₂` is
cyclic. -/
theorem lemma_1_2_a [FrattiniElementaryQuotient.{0}] {P : Type} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) (hM : IsMetacyclic P) (P₁ P₂ : Subgroup P) [P₁.Normal] (hsup : P₁ ⊔ P₂ = ⊤)
    (hinf : P₁ ⊓ P₂ = ⊥) (h₁ : P₁ ≠ ⊥) : IsCyclic P₂ := by
  by_contra hc
  have hsurj := QuotientGroup.mk'_surjective P₁
  have hQc : ¬ IsCyclic (P ⧸ P₁) := fun h ↦ hc <| isCyclic_of_injective ((QuotientGroup.mk' P₁).comp P₂.subtype)
    ((injective_iff_map_eq_one _).mpr fun x hx ↦ by
      have : (x : P) ∈ P₁ ⊓ P₂ := ⟨(QuotientGroup.eq_one_iff _).mp hx, x.2⟩
      rw [hinf, mem_bot] at this
      exact Subtype.ext this)
  have h1 := card_quotient_frattini_eq (hP.to_quotient P₁) (hM.of_surjective _ hsurj) hQc
  have hle := frattini_le_comap_frattini_of_surjective hsurj
  have hΦ : frattini P = (frattini (P ⧸ P₁)).comap (QuotientGroup.mk' P₁) := by
    refine eq_of_index_dvd_index hle ?_
    rw [index_comap_of_surjective _ hsurj, index_eq_card, index_eq_card, h1]
    exact card_quotient_frattini_dvd hP hM
  have hP₁ : P₁ ≤ frattini P := by
    rw [hΦ]
    intro x hx
    rw [mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  have htop : P₂ = ⊤ := by
    refine frattini_nongenerating (eq_top_iff.mpr ?_)
    rw [← hsup, sup_comm]
    exact sup_le_sup_left hP₁ _
  exact h₁ (by rw [← inf_top_eq P₁, ← htop, hinf])

/-- Lemma (1.2)(b): for `p` odd and `P₂ ≠ 1`, also `P₁` is cyclic. -/
theorem lemma_1_2_b [FrattiniElementaryQuotient.{0}] {P : Type} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hP : IsPGroup p P) (hM : IsMetacyclic P) (P₁ P₂ : Subgroup P) [P₁.Normal]
    (hsup : P₁ ⊔ P₂ = ⊤) (hinf : P₁ ⊓ P₂ = ⊥) (h₂ : P₂ ≠ ⊥) : IsCyclic P₁ := by
  by_contra hc
  have hp : p.Prime := Fact.out
  have hP1 : IsPGroup p P₁ := hP.to_subgroup P₁
  have hcard1 := card_quotient_frattini_eq hP1 (hM.subgroup P₁) hc
  have hexp1 := (FrattiniElementaryQuotient.frattini_elementary_quotient hP1).2.2.1
  set F := (frattini P₁).map P₁.subtype
  have hFP : F ≤ P₁ := map_subtype_le _
  set π := QuotientGroup.mk' F
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective F
  set A := P₁.map π
  have hAn : A.Normal := Subgroup.Normal.map inferInstance π hπ
  -- `A ≅ P₁/Φ(P₁)` has order `p²` and exponent `p`
  have hA : Nat.card A = p ^ 2 := by
    have hker : (π.comp P₁.subtype).ker = frattini P₁ := by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', comap_map_eq_self_of_injective P₁.subtype_injective]
    have hrange : (π.comp P₁.subtype).range = A := by rw [MonoidHom.range_comp, range_subtype]
    rw [← hrange, ← hcard1]
    exact Nat.card_congr ((QuotientGroup.quotientKerEquivRange _).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)).toEquiv
  have hexpA : ∀ y ∈ A, y ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have h := hexp1 (⟨x, hx⟩ : P₁)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have := mem_map_of_mem P₁.subtype h
    rw [map_pow] at this
    exact this
  -- an element `g ∈ P₂` of order `p`, and `B = ⟨gF⟩`
  have hdvd : p ∣ Nat.card P₂ :=
    ((hP.to_subgroup P₂).card_eq_or_dvd).resolve_left (mt card_eq_one.mp h₂)
  obtain ⟨⟨g, hg⟩, hgo⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hgp : g ^ p = 1 := by
    have := pow_orderOf_eq_one (⟨g, hg⟩ : P₂)
    rw [hgo] at this
    simpa using congrArg Subtype.val this
  have hgP₁ : g ∉ P₁ := fun h ↦ by
    have : g ∈ P₁ ⊓ P₂ := ⟨h, hg⟩
    rw [hinf, mem_bot] at this
    subst this
    exact hp.one_lt.ne' (by rw [← hgo]; exact orderOf_eq_one_iff.mpr rfl)
  have hπg : π g ≠ 1 := fun h ↦ hgP₁ (hFP ((QuotientGroup.eq_one_iff g).mp h))
  set B := zpowers (π g)
  have hB : Nat.card B = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [← map_pow, hgp, map_one]) hπg]
  have hexpB : ∀ y ∈ B, y ^ p = 1 := fun y hy ↦ by
    simpa [hB] using congrArg Subtype.val (pow_card_eq_one' (G := B) (x := ⟨y, hy⟩))
  have hdisj : Disjoint A B := by
    rcases (Nat.dvd_prime hp).mp (hB ▸ card_dvd_of_le (inf_le_right : A ⊓ B ≤ B)) with h | h
    · exact disjoint_iff.mpr (card_eq_one.mp h)
    · have := eq_of_le_of_card_ge (inf_le_right : A ⊓ B ≤ B) (by rw [hB, h])
      have hm : π g ∈ A ⊓ B := by rw [this]; exact mem_zpowers _
      obtain ⟨a, ha, hag⟩ := hm.1
      have : a⁻¹ * g ∈ P₁ := hFP (QuotientGroup.eq.mp hag)
      exact (hgP₁ (by simpa using P₁.mul_mem ha this)).elim
  -- `S = AB` has order `p³`
  set S := A ⊔ B
  have hS : Nat.card S = p ^ 3 := by
    have := relIndex_mul_relIndex (⊥ : Subgroup (P ⧸ F)) A (B ⊔ A) bot_le le_sup_right
    rw [relIndex_bot_left, relIndex_bot_left, relIndex_sup_right, relIndex,
      subgroupOf_eq_bot.mpr hdisj, index_bot, hA, hB, sup_comm] at this
    rw [← this]
    ring
  have hexpS := pow_eq_one_of_card_eq_cube hp2 hS (A.subgroupOf S) (B.subgroupOf S)
    (fun x ↦ by
      obtain ⟨a, ha, b, hb, h⟩ := mem_sup_of_normal_left.mp x.2
      exact ⟨⟨a, mem_sup_left ha⟩, ha, ⟨b, mem_sup_right hb⟩, hb, Subtype.ext h.symm⟩)
    (fun x hx ↦ Subtype.ext (by simpa using hexpA _ hx)) (fun x hx ↦ Subtype.ext (by simpa using hexpB _ hx))
  have := ((hM.of_surjective π hπ).subgroup S).card_dvd_sq hexpS
  rw [hS, Nat.pow_dvd_pow_iff_le_right hp.one_lt] at this
  lia

end CFSGOutside.ChillagSonn
