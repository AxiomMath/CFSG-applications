import Mathlib

/-!
# Nonabelian groups of order `p³`

For a nonabelian group `Q` of order `p³`: the center has order `p`, commutators are central, and
the centralizer of a noncentral `x` is `⟨x⟩ Z(Q)`.
-/

namespace CFSGOutside.Gagola

open Subgroup
open scoped Pointwise

variable {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [hp : Fact p.Prime]

theorem pcube_card_center (hQ : Nat.card Q = p ^ 3) (hnab : ∃ a b : Q, a * b ≠ b * a) :
    Nat.card (center Q) = p := by
  have hpg : IsPGroup p Q := IsPGroup.of_card hQ
  have : Nontrivial Q := by
    obtain ⟨a, b, hab⟩ := hnab
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hab (Subsingleton.elim _ _)
  have hdvd : Nat.card (center Q) ∣ p ^ 3 := hQ ▸ card_subgroup_dvd_card _
  obtain ⟨a, ha, hca⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
  have hnt : Nontrivial (center Q) := hpg.center_nontrivial
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hca
    exact (Subgroup.nontrivial_iff_ne_bot _).mp hnt ((Subgroup.card_eq_one).mp hca)
  have hne : center Q ≠ ⊤ := by
    intro htop
    obtain ⟨x, y, hxy⟩ := hnab
    have hx : x ∈ center Q := htop ▸ mem_top x
    exact hxy (mem_center_iff.mp hx y).symm
  have ha3 : a ≠ 3 := by
    rintro rfl
    exact hne (Subgroup.eq_top_of_card_eq _ (hca.trans hQ.symm))
  have ha2 : a ≠ 2 := by
    rintro rfl
    have hq : Nat.card (Q ⧸ center Q) = p := by
      have h1 := (center Q).card_mul_index
      rw [index_eq_card, hca, hQ] at h1
      have hp2 : 0 < p ^ 2 := pow_pos hp.out.pos 2
      exact Nat.eq_of_mul_eq_mul_left hp2 (by rw [h1]; ring)
    haveI : IsCyclic (Q ⧸ center Q) := isCyclic_of_prime_card hq
    obtain ⟨x, y, hxy⟩ := hnab
    exact hxy (commutative_of_cyclic_center_quotient (QuotientGroup.mk' (center Q))
      (by rw [QuotientGroup.ker_mk']) x y)
  have : a = 1 := by omega
  rw [hca, this, pow_one]

theorem pcube_comm_mem_center (hQ : Nat.card Q = p ^ 3) (hnab : ∃ a b : Q, a * b ≠ b * a)
    (a b : Q) : a * b * a⁻¹ * b⁻¹ ∈ center Q := by
  have hq : Nat.card (Q ⧸ center Q) = p ^ 2 := by
    have h1 := (center Q).card_mul_index
    rw [index_eq_card, pcube_card_center hQ hnab, hQ] at h1
    exact Nat.eq_of_mul_eq_mul_left hp.out.pos (by rw [h1]; ring)
  have hc := (IsPGroup.isMulCommutative_of_card_eq_prime_sq hq).is_comm.comm
    ((b⁻¹ : Q) : Q ⧸ center Q) ((a⁻¹ : Q) : Q ⧸ center Q)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hc
  simpa [mul_assoc] using hc

theorem pcube_centralizer (hQ : Nat.card Q = p ^ 3) (hnab : ∃ a b : Q, a * b ≠ b * a) {x c : Q}
    (hx : x ∉ center Q) (hc : c ∈ center Q) (hc1 : c ≠ 1) {d : Q} (hd : d * x = x * d) :
    ∃ i j : ℕ, d = x ^ i * c ^ j := by
  have hZ := pcube_card_center hQ hnab
  -- `⟨c⟩ = Z(Q)`
  have hcZ : zpowers c = center Q := by
    have hle : zpowers c ≤ center Q := (zpowers_le).mpr hc
    have hdv : Nat.card (zpowers c) ∣ p := hZ ▸ card_dvd_of_le hle
    rcases (Nat.dvd_prime hp.out).mp hdv with h | h
    · exact absurd (zpowers_eq_bot.mp (card_eq_one.mp h)) hc1
    · exact eq_of_le_of_card_ge hle (by rw [h, hZ])
  set Cx := centralizer ({x} : Set Q)
  set S := zpowers x ⊔ zpowers c
  have hSC : S ≤ Cx := by
    refine sup_le ((zpowers_le).mpr (mem_centralizer_singleton_iff.mpr rfl)) ?_
    rw [hcZ]; exact center_le_centralizer _
  have hxS : x ∈ S := mem_sup_left (mem_zpowers x)
  -- orders
  have hpos : 0 < p := hp.out.pos
  have hCdvd : Nat.card Cx ∣ p ^ 3 := hQ ▸ card_subgroup_dvd_card _
  have hSdvd : Nat.card S ∣ p ^ 3 := hQ ▸ card_subgroup_dvd_card _
  have hSgt : p < Nat.card S := by
    have hlt : center Q < S := by
      refine lt_of_le_of_ne (hcZ ▸ le_sup_right) fun h => hx (h ▸ hxS)
    rw [← hZ]; exact card_lt_of_lt hlt
  have hCne : Cx ≠ ⊤ := by
    intro htop
    apply hx
    rw [mem_center_iff]
    intro g
    have : g ∈ Cx := htop ▸ mem_top g
    exact (mem_centralizer_singleton_iff.mp this)
  have hClt : Nat.card Cx < p ^ 3 := by
    rw [← hQ, ← Subgroup.card_top (G := Q)]
    exact card_lt_of_lt (lt_top_iff_ne_top.mpr hCne)
  have hSle : Nat.card S ≤ Nat.card Cx := card_le_of_le hSC
  obtain ⟨a, ha, hSa⟩ := (Nat.dvd_prime_pow hp.out).mp hSdvd
  obtain ⟨b, hb, hCb⟩ := (Nat.dvd_prime_pow hp.out).mp hCdvd
  have hb3 : b < 3 := by
    by_contra h; push Not at h
    have : b = 3 := by omega
    rw [hCb, this] at hClt; exact lt_irrefl _ hClt
  have ha2 : 2 ≤ a := by
    by_contra h; push Not at h
    interval_cases a
    · rw [hSa, pow_zero] at hSgt; exact absurd hSgt (by omega)
    · rw [hSa, pow_one] at hSgt; exact lt_irrefl _ hSgt
  have hab : a ≤ b := by
    rw [hSa, hCb] at hSle
    exact (Nat.pow_le_pow_iff_right hp.out.one_lt).mp hSle
  have hSeq : S = Cx := eq_of_le_of_card_ge hSC (by rw [hSa, hCb]; exact Nat.pow_le_pow_right hpos (by omega))
  have hdC : d ∈ Cx := mem_centralizer_singleton_iff.mpr hd
  rw [← hSeq] at hdC
  haveI : (zpowers c).Normal := by rw [hcZ]; infer_instance
  have hdC' : d ∈ ((zpowers x : Set Q) * (zpowers c : Set Q)) := by
    rw [← Subgroup.mul_normal]; exact hdC
  obtain ⟨y, hy, z, hz, rfl⟩ := hdC'
  obtain ⟨i, rfl⟩ := (mem_powers_iff_mem_zpowers.mpr hy : y ∈ Submonoid.powers x)
  obtain ⟨j, rfl⟩ := (mem_powers_iff_mem_zpowers.mpr hz : z ∈ Submonoid.powers c)
  exact ⟨i, j, rfl⟩

theorem pcube_center_eq_zpowers (hQ : Nat.card Q = p ^ 3) (hnab : ∃ a b : Q, a * b ≠ b * a)
    {c : Q} (hc : c ∈ center Q) (hc1 : c ≠ 1) : zpowers c = center Q := by
  have hZ := pcube_card_center hQ hnab
  have hle : zpowers c ≤ center Q := (zpowers_le).mpr hc
  have hdv : Nat.card (zpowers c) ∣ p := hZ ▸ card_dvd_of_le hle
  rcases (Nat.dvd_prime hp.out).mp hdv with h | h
  · exact absurd (zpowers_eq_bot.mp (card_eq_one.mp h)) hc1
  · exact eq_of_le_of_card_ge hle (by rw [h, hZ])

theorem pcube_orderOf_central (hQ : Nat.card Q = p ^ 3) (hnab : ∃ a b : Q, a * b ≠ b * a)
    {c : Q} (hc : c ∈ center Q) (hc1 : c ≠ 1) : orderOf c = p := by
  rw [← Nat.card_zpowers, pcube_center_eq_zpowers hQ hnab hc hc1, pcube_card_center hQ hnab]

theorem pcube_exists_pow_of_central (hQ : Nat.card Q = p ^ 3) (hnab : ∃ a b : Q, a * b ≠ b * a)
    {c : Q} (hc : c ∈ center Q) (hc1 : c ≠ 1) {x : Q} (hx : x ∈ center Q) : ∃ i : ℕ, x = c ^ i := by
  rw [← pcube_center_eq_zpowers hQ hnab hc hc1] at hx
  obtain ⟨i, rfl⟩ := (mem_powers_iff_mem_zpowers.mpr hx : x ∈ Submonoid.powers c)
  exact ⟨i, rfl⟩

end CFSGOutside.Gagola
