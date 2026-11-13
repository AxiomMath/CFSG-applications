import CFSGOutside.GiuliettiKorchmaros.Thm61Basic

/-!
# Theorem 6.1: small centralizers
-/

namespace CFSGOutside.GiuliettiKorchmaros

variable {G : Type} [Group G] [Finite G]

theorem card_le_two_of_commute (hP : CyclicIndexTwo G) {Q R : Subgroup G} (hQ : IsPGroup 2 Q)
    (hR : IsPGroup 2 R) (hcomm : ∀ q ∈ Q, ∀ r ∈ R, q * r = r * q)
    (hQR : Nat.card (Q ⊓ R : Subgroup G) ≤ 2) (hQ8 : 8 ≤ Nat.card Q)
    (hexpQ : ∀ q ∈ Q, q ^ (Nat.card Q / 2) = 1) : Nat.card R ≤ 2 := by
  classical
  let φ : Q × R →* G := MonoidHom.noncommCoprod Q.subtype R.subtype
    (fun q r => (hcomm q q.2 r r.2 : _))
  have hφ : ∀ p : Q × R, φ p = (p.1 : G) * (p.2 : G) := fun p => rfl
  -- kernel
  have hker : Nat.card φ.ker ≤ 2 := by
    refine le_trans ?_ hQR
    have hinj : Function.Injective (fun x : φ.ker => (⟨(x.1.1 : G), x.1.1.2,
        by
          have h := x.2
          rw [MonoidHom.mem_ker, hφ] at h
          have : (x.1.1 : G) = ((x.1.2 : G))⁻¹ := eq_inv_of_mul_eq_one_left h
          rw [this]; exact R.inv_mem x.1.2.2⟩ : (Q ⊓ R : Subgroup G))) := by
      intro x y hxy
      have h1 : (x.1.1 : G) = y.1.1 := congrArg (fun z : (Q ⊓ R : Subgroup G) => (z : G)) hxy
      have hx := x.2; have hy := y.2
      rw [MonoidHom.mem_ker, hφ] at hx hy
      have h2 : (x.1.2 : G) = y.1.2 := by
        rw [eq_inv_of_mul_eq_one_right hx, eq_inv_of_mul_eq_one_right hy, h1]
      apply Subtype.ext
      exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
    exact Nat.card_le_card_of_injective _ hinj
  have hcardprod : Nat.card φ.ker * Nat.card φ.range = Nat.card Q * Nat.card R := by
    rw [Subgroup.card_ker_mul_card_range, Nat.card_prod]
  have hprod : IsPGroup 2 (Q × R) := by
    intro x
    obtain ⟨a, ha⟩ := hQ x.1
    obtain ⟨b, hb⟩ := hR x.2
    refine ⟨max a b, Prod.ext ?_ ?_⟩
    · simp only [Prod.pow_fst, Prod.fst_one]
      obtain ⟨c, hc⟩ : ∃ c, max a b = a + c := ⟨max a b - a, by omega⟩
      rw [hc, pow_add, pow_mul, ha]; simp
    · simp only [Prod.pow_snd, Prod.snd_one]
      obtain ⟨c, hc⟩ : ∃ c, max a b = b + c := ⟨max a b - b, by omega⟩
      rw [hc, pow_add, pow_mul, hb]; simp
  have hrange : IsPGroup 2 φ.range :=
    hprod.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨C, hCle, hCcyc, hCidx⟩ := hP φ.range hrange
  obtain ⟨g0, hg0⟩ := hCcyc.exists_generator
  have hordC : orderOf g0 = Nat.card C := orderOf_eq_card_of_forall_mem_zpowers hg0
  have hrel := Subgroup.relIndex_mul_card (H := C) (K := φ.range)
  rw [inf_eq_left.mpr hCle] at hrel
  have hrange_le : Nat.card φ.range ≤ 2 * orderOf (g0 : G) := by
    rw [Subgroup.orderOf_coe, hordC, ← hrel]
    nlinarith [Nat.zero_le (Nat.card C)]
  have hg0mem : (g0 : G) ∈ φ.range := hCle g0.2
  obtain ⟨p, hp⟩ := hg0mem
  -- powers of two
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card.mp hQ)
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card.mp hR)
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h, pow_zero] at ha; omega
    · exact h
  have hQhalf : Nat.card Q / 2 = 2 ^ (a - 1) := by
    rw [ha]; obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
    simp [pow_succ]
  -- bound on order
  have hbound : ∃ m, 0 < m ∧ (m = Nat.card Q / 2 ∨ m = Nat.card R) ∧ (g0 : G) ^ m = 1 := by
    have hpow : ∀ m, Nat.card Q / 2 ∣ m → Nat.card R ∣ m → (g0 : G) ^ m = 1 := by
      intro m h1 h2
      rw [← hp, hφ, Commute.mul_pow (hcomm _ p.1.2 _ p.2.2)]
      obtain ⟨u, hu⟩ := h1
      obtain ⟨v, hv⟩ := h2
      have e1 : (p.1 : G) ^ m = 1 := by rw [hu, pow_mul]; simp [hexpQ _ p.1.2]
      have e2 : (p.2 : G) ^ m = 1 := by
        rw [hv, pow_mul]
        have : (p.2 : G) ^ Nat.card R = 1 := by
          have := pow_card_eq_one' (G := R) (x := p.2)
          exact congrArg Subtype.val this
        rw [this]; simp
      rw [e1, e2, one_mul]
    by_cases hab : a - 1 ≤ b
    · refine ⟨Nat.card R, hRpos, Or.inr rfl, hpow _ ?_ dvd_rfl⟩
      rw [hQhalf, hb]; exact Nat.pow_dvd_pow 2 hab
    · refine ⟨Nat.card Q / 2, by rw [hQhalf]; positivity, Or.inl rfl, hpow _ dvd_rfl ?_⟩
      rw [hQhalf, hb]; exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨m, hm0, hm, hgm⟩ := hbound
  have hord : orderOf (g0 : G) ≤ m := orderOf_le_of_pow_eq_one hm0 hgm
  have hmain : Nat.card Q * Nat.card R ≤ 4 * m := by
    rw [← hcardprod]
    nlinarith [Nat.zero_le (Nat.card φ.range)]
  rcases hm with rfl | rfl
  · have : Nat.card Q * Nat.card R ≤ 2 * Nat.card Q := by
      have := Nat.mul_div_cancel' (show 2 ∣ Nat.card Q by rw [ha]; exact dvd_pow_self 2 (by omega))
      nlinarith
    nlinarith
  · nlinarith

theorem card_centralizer_le_two (hP : CyclicIndexTwo G) (hO : OddCoreFree G) (Y : Subgroup G) [Y.Normal]
    {Q : Subgroup G} (hQY : Q ≤ Y) (hQ : IsPGroup 2 Q) (hQ8 : 8 ≤ Nat.card Q)
    (hexpQ : ∀ q ∈ Q, q ^ (Nat.card Q / 2) = 1)
    (hYC : Nat.card (Y ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) ≤ 2) :
    Nat.card (Subgroup.centralizer (Y : Set G)) ≤ 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := Subgroup.centralizer (Y : Set G) with hCdef
  haveI : C.Normal := Subgroup.normal_centralizer
  have hOC : OddCoreFree C := Complement.oddCoreFree_of_normal hO C
  let R : Sylow 2 C := default
  let R' : Subgroup G := (R : Subgroup C).map C.subtype
  have hRcard : Nat.card R' = Nat.card (R : Subgroup C) :=
    Subgroup.card_map_of_injective C.subtype_injective
  have hR'p : IsPGroup 2 R' := R.isPGroup'.map C.subtype
  have hcomm : ∀ q ∈ Q, ∀ r ∈ R', q * r = r * q := by
    intro q hq r hr
    obtain ⟨c, _, rfl⟩ := hr
    have := c.2 q (hQY hq)
    exact this
  have hle : (Q ⊓ R') ≤ Y ⊓ C := by
    intro x hx
    refine ⟨hQY hx.1, ?_⟩
    obtain ⟨c, _, hc⟩ := hx.2
    rw [← hc]; exact c.2
  have hint : Nat.card (Q ⊓ R' : Subgroup G) ≤ 2 :=
    le_trans (Subgroup.card_le_of_le hle) hYC
  have hR2 : Nat.card (R : Subgroup C) ≤ 2 := by
    rw [← hRcard]; exact card_le_two_of_commute hP hQ hR'p hcomm hint hQ8 hexpQ
  have hcyc : IsCyclic (R : Subgroup C) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp R.isPGroup'
    have hn1 : n = 0 ∨ n = 1 := by
      by_contra hcon
      have : 2 ≤ n := by omega
      have : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) this
      omega
    rcases hn1 with rfl | rfl
    · haveI : Subsingleton (R : Subgroup C) := by
        rw [pow_zero] at hn; exact (Nat.card_eq_one_iff_unique.mp hn).1
      infer_instance
    · haveI : Fact (Nat.card (R : Subgroup C)).Prime := ⟨by rw [hn]; simpa using Nat.prime_two⟩
      exact isCyclic_of_prime_card (p := Nat.card (R : Subgroup C)) rfl
  have hCp : IsPGroup 2 C := Complement.isPGroup_of_cyclic_sylow hOC R hcyc
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hCp
  have hRC := R.card_eq_multiplicity
  rw [hn, Nat.Prime.factorization_pow Nat.prime_two] at hRC
  simp at hRC
  rw [hn, ← hRC]; exact hR2

theorem quaternion_pow_eq_one (k : ℕ) (hk : 1 ≤ k) (x : QuaternionGroup (2 ^ k)) :
    x ^ (2 ^ (k + 1)) = 1 := by
  have h := Monoid.pow_exponent_eq_one x
  rw [QuaternionGroup.exponent] at h
  have : 2 * lcm (2 ^ k) 2 = 2 ^ (k + 1) := by
    have : lcm (2 ^ k) 2 = 2 ^ k := lcm_eq_left_iff _ _ (by simp) |>.mpr
      (dvd_pow_self 2 (by omega))
    rw [this, pow_succ]; ring
  rwa [this] at h

end CFSGOutside.GiuliettiKorchmaros
