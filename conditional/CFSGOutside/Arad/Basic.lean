import CFSGOutside.Arad.Defs
import CFSGOutside.Corpus.ExistsIsSylowOfNormalizedOfCoprime

/-!
# Arad, Theorem B(iii): basic properties of homogeneity

The working form `HomP` of π-homogeneity, its inheritance by subgroups and quotient groups (Arad's Lemma 2.2,
which is Baer's Lemma 2.3), and the witnesses `Bad` that contradict it.
-/

namespace CFSGOutside.Arad

open Subgroup
open scoped Pointwise

section General

variable {G : Type*} [Group G]

theorem isPiGroup_of_isPGroup [Finite G] {π : Set ℕ} {r : ℕ} (hr : r.Prime) (hrπ : r ∈ π)
    {H : Subgroup G} (hH : IsPGroup r H) : IsPiGroup π H := by
  intro p hp hpd
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hH
  rw [hn] at hpd
  rwa [(Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hpd)]

instance normal_centralizer_subgroupOf_normalizer (H : Subgroup G) :
    ((centralizer (H : Set G)).subgroupOf (normalizer (H : Set G))).Normal := by
  rw [← normalizerMonoidHom_ker]
  exact MonoidHom.normal_ker _

/-- π-homogeneity implies its working form. -/
theorem homP_of_isPiHomogeneous [Finite G] {π : Set ℕ} (h : IsPiHomogeneous π G) : HomP π G := by
  intro r hr hrπ H hH hHr s hs hsπ x hx ⟨k, hk⟩
  set N := normalizer (H : Set G)
  set C := (centralizer (H : Set G)).subgroupOf N
  let y : N ⧸ C := ((⟨x, hx⟩ : N) : N ⧸ C)
  have hy : y ^ (s ^ k) = 1 := by
    change (((⟨x, hx⟩ : N) ^ (s ^ k) : N) : N ⧸ C) = 1
    rw [show (⟨x, hx⟩ : N) ^ (s ^ k) = 1 from Subtype.ext (by simpa using hk)]
    rfl
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hs).mp (orderOf_dvd_of_pow_eq_one hy)
  rcases j with _ | j
  · have : y = 1 := orderOf_eq_one_iff.mp (by simpa using hj)
    have hmem : (⟨x, hx⟩ : N) ∈ C := (QuotientGroup.eq_one_iff _).mp this
    exact hmem
  · have hsd : s ∣ Nat.card (N ⧸ C) := by
      refine dvd_trans ?_ (orderOf_dvd_natCard y)
      rw [hj]
      exact dvd_pow_self s (Nat.succ_ne_zero j)
    exact absurd (h H hH (isPiGroup_of_isPGroup hr hrπ hHr) s hs hsd) hsπ

theorem Bad.false {π : Set ℕ} {r s : ℕ} (h : HomP π G) (hr : r.Prime) (hrπ : r ∈ π) (hs : s.Prime)
    (hsπ : s ∉ π) (hb : Bad G r s) : False := by
  obtain ⟨H, hH, hHr, x, hx, hxc, hk⟩ := hb
  exact hxc (h r hr hrπ H hH hHr s hs hsπ x hx hk)

theorem map_mem_centralizer_iff {G' : Type*} [Group G'] {f : G →* G'} (hf : Function.Injective f)
    {H : Subgroup G} {x : G} : f x ∈ centralizer ((H.map f : Subgroup G') : Set G') ↔
      x ∈ centralizer (H : Set G) := by
  simp only [mem_centralizer_iff, SetLike.mem_coe, mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  refine forall₂_congr fun h _ => ?_
  rw [← map_mul, ← map_mul, hf.eq_iff]

theorem Bad.map {G' : Type*} [Group G'] {r s : ℕ} {f : G →* G'} (hf : Function.Injective f)
    (hb : Bad G r s) : Bad G' r s := by
  obtain ⟨H, hH, hHr, x, hx, hxc, k, hk⟩ := hb
  refine ⟨H.map f, ?_, hHr.map f, f x, le_normalizer_map f ⟨x, hx, rfl⟩,
    (map_mem_centralizer_iff hf).not.mpr hxc, k, by rw [← map_pow, hk, map_one]⟩
  rwa [Ne, map_eq_bot_iff_of_injective H hf]

theorem Bad.of_mulEquiv {G' : Type*} [Group G'] {r s : ℕ} (e : G ≃* G') (hb : Bad G' r s) :
    Bad G r s :=
  hb.map (f := e.symm.toMonoidHom) e.symm.injective

/-- `HomP` passes to subgroups (through an injective homomorphism). -/
theorem homP_of_injective {G' : Type*} [Group G'] {π : Set ℕ} {f : G' →* G}
    (hf : Function.Injective f) (h : HomP π G) : HomP π G' := by
  intro r hr hrπ H hH hHr s hs hsπ x hx ⟨k, hk⟩
  refine (map_mem_centralizer_iff hf).mp (h r hr hrπ (H.map f) ?_ (hHr.map f) s hs hsπ (f x)
    (le_normalizer_map f ⟨x, hx, rfl⟩) ⟨k, by rw [← map_pow, hk, map_one]⟩)
  rwa [Ne, map_eq_bot_iff_of_injective H hf]

theorem homP_subgroup {π : Set ℕ} (h : HomP π G) (A : Subgroup G) : HomP π A :=
  homP_of_injective A.subtype_injective h

/-- An involution inverting a nonidentity `r`-subgroup, `r` odd, is a witness `Bad G r 2`. -/
theorem bad_of_inverts {r : ℕ} (hr2 : r ≠ 2) [Fact r.Prime] {P : Subgroup G} (hP : P ≠ ⊥)
    (hPr : IsPGroup r P) {x : G} (hx2 : x ^ 2 = 1) (hinv : ∀ z ∈ P, x * z * x⁻¹ = z⁻¹) :
    Bad G r 2 := by
  refine ⟨P, hP, hPr, x, ?_, ?_, 1, by simpa using hx2⟩
  · rw [mem_normalizer_iff]
    intro h
    have hx : x⁻¹ = x := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hx2]
    refine ⟨fun hh => by rw [hinv h hh]; exact P.inv_mem hh, fun hh => ?_⟩
    have e : h = x * (x * h * x⁻¹) * x⁻¹ := by
      calc h = x⁻¹ * (x * h * x⁻¹) * x := by group
        _ = x * (x * h * x⁻¹) * x⁻¹ := by rw [hx]
    rw [e, hinv _ hh]
    exact P.inv_mem hh
  · intro hc
    obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hP
    have h1 : x * (z : G) * x⁻¹ = z := by
      rw [← (mem_centralizer_iff.mp hc) z z.2, mul_inv_cancel_right]
    rw [hinv z z.2] at h1
    have hz2 : (z : G) ^ 2 = 1 := by
      rw [pow_two]; nth_rewrite 1 [← h1]; exact inv_mul_cancel _
    obtain ⟨n, hn⟩ := hPr z
    have hzo : orderOf (z : G) ∣ Nat.gcd 2 (r ^ n) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hz2)
        (orderOf_dvd_of_pow_eq_one (by rw [← Subgroup.coe_pow, hn, Subgroup.coe_one]))
    have hcop : Nat.gcd 2 (r ^ n) = 1 :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two Fact.out).mpr (Ne.symm hr2))
    rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hzo
    exact hz1 (Subtype.ext hzo)

end General

section SPart

variable {G : Type*} [Group G]

theorem pow_pow_eq_one_of_coprime {G' : Type*} [Group G'] {y : G'} {s a m j : ℕ} (hs : s.Prime)
    (hm : ¬ s ∣ m) (hj : y ^ (s ^ j) = 1) (hy : y ^ (s ^ a * m) = 1) : y ^ (s ^ a) = 1 := by
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hs).mp (orderOf_dvd_of_pow_eq_one hj)
  have h1 : s ^ i ∣ s ^ a * m := hi ▸ orderOf_dvd_of_pow_eq_one hy
  have hcop : Nat.Coprime (s ^ i) m :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hs).mpr hm)
  exact orderOf_dvd_iff_pow_eq_one.mp (hi ▸ hcop.dvd_of_dvd_mul_right h1)

/-- The `s`-part of an element of finite order: a power `g ^ e` of `s`-power order such that `y ^ e = y` for
every `s`-element `y` with `y ^ orderOf g = 1`. -/
theorem exists_sPart (g : G) (hg : orderOf g ≠ 0) {s : ℕ} (hs : s.Prime) :
    ∃ e k : ℕ, (g ^ e) ^ (s ^ k) = 1 ∧
      ∀ {G' : Type*} [Group G'] (y : G') (j : ℕ), y ^ (s ^ j) = 1 → y ^ orderOf g = 1 → y ^ e = y := by
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hg s hs.ne_one
  have hcop : Nat.Coprime (s ^ a) m :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hs).mpr hm)
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · refine ⟨0, 0, by simp, fun y j hj hy => ?_⟩
    rw [hn] at hy
    have := pow_pow_eq_one_of_coprime hs hm hj hy
    simp only [pow_zero, pow_one] at this
    simp [this]
  · have hsa : 1 < s ^ a := Nat.one_lt_pow ha.ne' hs.one_lt
    haveI : NeZero (s ^ a) := ⟨by positivity⟩
    let u : ℕ := ((m : ZMod (s ^ a))⁻¹).val
    have hmu : (m * u) % (s ^ a) = 1 := by
      have : ((m * u : ℕ) : ZMod (s ^ a)) = 1 := by
        push_cast
        rw [ZMod.natCast_zmod_val, ZMod.coe_mul_inv_eq_one m (Nat.Coprime.symm hcop)]
      rw [← ZMod.val_natCast, this, ZMod.val_one'' hsa.ne']
    refine ⟨m * u, a, ?_, fun y j hj hy => ?_⟩
    · rw [← pow_mul, show m * u * s ^ a = (s ^ a * m) * u by ring, ← hn, pow_mul, pow_orderOf_eq_one,
        one_pow]
    · rw [hn] at hy
      have h1 := pow_pow_eq_one_of_coprime hs hm hj hy
      rw [← Nat.mod_add_div (m * u) (s ^ a), hmu, pow_add, pow_mul, h1, one_pow, mul_one, pow_one]

end SPart

section Quotient

variable {G : Type*} [Group G] [Finite G]

/-- `HomP` passes to quotient groups: Arad's Lemma 2.2 (Baer, Lemma 2.3) for the working form. The proof
lifts the acting `s`-element to an `s`-element normalizing a Sylow `r`-subgroup of the preimage (a Frattini
argument). -/
theorem homP_quotient {π : Set ℕ} (h : HomP π G) (N : Subgroup G) [N.Normal] : HomP π (G ⧸ N) := by
  classical
  intro r hr hrπ Hb hHb hHbr s hs hsπ xb hxb ⟨k, hk⟩
  haveI : Fact r.Prime := ⟨hr⟩
  set q := QuotientGroup.mk' N with hq
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective N
  set L : Subgroup G := Hb.comap q
  -- a Sylow `r`-subgroup `R` of `L` maps onto `Hb`
  obtain ⟨Q⟩ : Nonempty (Sylow r L) := inferInstance
  set R : Subgroup G := (Q : Subgroup L).map L.subtype with hRdef
  have hRL : R ≤ L := map_subtype_le _
  have hRr : IsPGroup r R := Q.isPGroup'.map L.subtype
  let φ : L →* Hb := (q.comp L.subtype).codRestrict Hb (fun l => l.2)
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨g, rfl⟩ := hqs y
    exact ⟨⟨g, hy⟩, rfl⟩
  have hRimg : R.map q = Hb := by
    let Qb : Sylow r Hb := Q.mapSurjective hφ
    have htop : (Qb : Subgroup Hb) = ⊤ := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hHbr
      apply eq_top_of_card_eq
      rw [Sylow.card_eq_multiplicity, hn, Nat.factorization_pow, Finsupp.smul_apply,
        Nat.Prime.factorization_self hr, smul_eq_mul, mul_one]
    apply le_antisymm
    · rw [map_le_iff_le_comap]; exact hRL
    · intro y hy
      have : (⟨y, hy⟩ : Hb) ∈ (Qb : Subgroup Hb) := htop ▸ mem_top _
      obtain ⟨l, hl, hly⟩ := (Subgroup.mem_map).mp this
      exact ⟨l, ⟨l, hl, rfl⟩, congrArg Subtype.val hly⟩
  -- lift `xb`
  obtain ⟨x, rfl⟩ := hqs xb
  have hxL : x ∈ normalizer (L : Set G) := by
    rw [mem_normalizer_iff]
    intro g
    have := (mem_normalizer_iff.mp hxb) (q g)
    simpa [L, map_mul, map_inv] using this
  -- `x R x⁻¹` is a Sylow subgroup of `L`, hence `L`-conjugate to `R`
  set R' : Subgroup G := MulAut.conj x • R
  have hR'L : R' ≤ L := by
    intro g hg
    rw [mem_pointwise_smul_iff_inv_smul_mem] at hg
    have h1 : x⁻¹ * g * x ∈ L := by simpa [MulAut.smul_def] using hRL hg
    have := (mem_normalizer_iff.mp hxL (x⁻¹ * g * x)).mp h1
    simpa [mul_assoc] using this
  have hcardR' : Nat.card R' = Nat.card R :=
    (Nat.card_congr (Subgroup.equivSMul (MulAut.conj x) R).toEquiv).symm
  have hcardRL : Nat.card (R.subgroupOf L) = Nat.card R :=
    Nat.card_congr (subgroupOfEquivOfLe hRL).toEquiv
  have hQR : (Q : Subgroup L) = R.subgroupOf L := by
    rw [hRdef, subgroupOf, comap_map_eq_self_of_injective L.subtype_injective]
  let Q' : Sylow r L := Sylow.ofCard (R'.subgroupOf L) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe hR'L).toEquiv, hcardR', ← hcardRL, ← hQR,
      Sylow.card_eq_multiplicity])
  obtain ⟨l, hl⟩ := MulAction.exists_smul_eq L Q Q'
  have hmapsmul : ∀ P : Subgroup L,
      (MulAut.conj l • P).map L.subtype = MulAut.conj (l : G) • P.map L.subtype := by
    intro P
    ext g
    rw [mem_pointwise_smul_iff_inv_smul_mem]
    simp only [mem_map, coe_subtype, MulAut.smul_def, map_inv, MulAut.conj_inv_apply]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [mem_pointwise_smul_iff_inv_smul_mem] at ha
      exact ⟨_, ha, by simp [MulAut.smul_def]⟩
    · rintro ⟨a, ha, hag⟩
      refine ⟨l * a * l⁻¹, ?_, ?_⟩
      · rw [mem_pointwise_smul_iff_inv_smul_mem]
        simpa [MulAut.smul_def, mul_assoc] using ha
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv, hag]
        group
  have hlR : MulAut.conj (l : G) • R = R' := by
    have h1 : ((l • Q : Sylow r L) : Subgroup L).map L.subtype =
        ((Q' : Sylow r L) : Subgroup L).map L.subtype := by rw [hl]
    rw [Sylow.coe_subgroup_smul, hmapsmul] at h1
    rw [show R = (Q : Subgroup L).map L.subtype from hRdef, h1]
    change (R'.subgroupOf L).map L.subtype = R'
    rw [subgroupOf_map_subtype, inf_of_le_left hR'L]
  -- write `l = n * ρ` with `n ∈ N`, `ρ ∈ R`
  obtain ⟨ρ, hρ, hρl⟩ : ∃ ρ ∈ R, q ρ = q l := by
    have : q l ∈ R.map q := hRimg ▸ l.2
    obtain ⟨ρ, hρ, h'⟩ := this
    exact ⟨ρ, hρ, h'⟩
  set n : G := (l : G) * ρ⁻¹ with hn
  have hnN : n ∈ N := by
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_mul, map_inv, hρl, mul_inv_cancel]
  -- `y₀ = n⁻¹ x` normalizes `R` and maps to `q x`
  set y₀ : G := n⁻¹ * x
  have hRρ : MulAut.conj ρ • R = R := by
    ext g
    rw [mem_pointwise_smul_iff_inv_smul_mem]
    simp only [MulAut.smul_def, map_inv, MulAut.conj_inv_apply]
    exact ⟨fun hg => by simpa [mul_assoc] using R.mul_mem (R.mul_mem hρ hg) (R.inv_mem hρ),
      fun hg => R.mul_mem (R.mul_mem (R.inv_mem hρ) hg) hρ⟩
  have hyR : MulAut.conj y₀ • R = R := by
    have hl' : (l : G) = n * ρ := by rw [hn, inv_mul_cancel_right]
    rw [show y₀ = n⁻¹ * x from rfl, map_mul, mul_smul, show MulAut.conj x • R = R' from rfl, ← hlR, hl',
      map_mul, mul_smul, hRρ, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have hy₀ : y₀ ∈ normalizer (R : Set G) := by
    rw [mem_normalizer_iff]
    intro g
    have key : y₀ * g * y₀⁻¹ ∈ R ↔ g ∈ R := by
      conv_lhs => rw [← hyR]
      rw [mem_pointwise_smul_iff_inv_smul_mem]
      simp [MulAut.smul_def, mul_assoc]
    exact key.symm
  have hqy₀ : q y₀ = q x := by
    have hqn : q n = 1 := (QuotientGroup.eq_one_iff n).mpr hnN
    rw [map_mul, map_inv, hqn, inv_one, one_mul]
  -- take the `s`-part of `y₀`
  have hfin : orderOf y₀ ≠ 0 := (orderOf_pos y₀).ne'
  obtain ⟨e, j, hej, he⟩ := exists_sPart y₀ hfin hs
  have hqe : q (y₀ ^ e) = q x := by
    rw [map_pow, hqy₀]
    refine he (q x) k hk ?_
    rw [← hqy₀, ← map_pow, pow_orderOf_eq_one, map_one]
  have hR : R ≠ ⊥ := by
    intro hR
    apply hHb
    rw [← hRimg, hR, Subgroup.map_bot]
  have hc := h r hr hrπ R hR hRr s hs hsπ (y₀ ^ e) (pow_mem hy₀ e) ⟨j, hej⟩
  -- so `q x` centralizes `q R = Hb`
  rw [mem_centralizer_iff]
  intro z hz
  rw [← hRimg] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rw [← hqe, ← map_mul, ← map_mul, (mem_centralizer_iff.mp hc) w hw]

end Quotient

end CFSGOutside.Arad
