import CFSGOutside.HallPaige.Lie.RankOne

/-!
# `T n ⊆ UnUnU` from one torus identity

In a rank-one split group (`G = TU ⊔ UnTU` with unique expressions) where `n² = 1` inverts the
cyclic torus `T`, the set of torus parts `s` of the elements `ncn = a n s b` (`1 ≠ c ∈ U`) is
stable under multiplication by squares. Hence two such torus parts differing by a non-square
give all of `T`, and then `t n ∈ UnUnU` for every `t ∈ T`
(`CFSGOutside.HallPaige.rankOne_tn_mem_of_words`). The two torus parts are produced from the identities
`n = u₁ (n u₁ n⁻¹) u₁` and `h = u₀ v₀ v₀ v₁ u₂ v₁` (`vᵢ = n uᵢ n⁻¹`, `h ∈ T` a non-square), which
the corpus verifies for the small Ree groups over the prime field.
-/

namespace CFSGOutside.HallPaige

variable {G : Type*} [Group G]

/-- In a cyclic subgroup `T`, if `h ∈ T` is not a square, every `r ∈ T` is `s' m²` or `s' h m²`. -/
theorem exists_eq_mul_sq_of_isCyclic (T : Subgroup G) (hT : IsCyclic T) {h s' r : G}
    (hh : h ∈ T) (hns : ∀ m ∈ T, h ≠ m * m) (hs' : s' ∈ T) (hr : r ∈ T) :
    ∃ m ∈ T, r = s' * (m * m) ∨ r = s' * h * (m * m) := by
  obtain ⟨g, hg⟩ := hT.exists_generator
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨r, hr⟩)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨s', hs'⟩)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨h, hh⟩)
  have hi' : (g : G) ^ i = r := congrArg Subtype.val hi
  have hj' : (g : G) ^ j = s' := congrArg Subtype.val hj
  have hk' : (g : G) ^ k = h := congrArg Subtype.val hk
  have hgT : (g : G) ∈ T := g.2
  have hkodd : Odd k := by
    rcases Int.even_or_odd' k with ⟨l, hl | hl⟩
    · exfalso
      refine hns ((g : G) ^ l) (T.zpow_mem hgT l) ?_
      rw [← hk', hl, ← zpow_add, two_mul]
    · exact ⟨l, hl⟩
  rcases Int.even_or_odd' (i - j) with ⟨l, hl | hl⟩
  · refine ⟨(g : G) ^ l, T.zpow_mem hgT l, Or.inl ?_⟩
    rw [← hi', ← hj', ← zpow_add, ← zpow_add]
    congr 1; omega
  · obtain ⟨k', hkk⟩ := hkodd
    refine ⟨(g : G) ^ (l - k'), T.zpow_mem hgT _, Or.inr ?_⟩
    rw [← hi', ← hj', ← hk', ← zpow_add, ← zpow_add, ← zpow_add]
    congr 1; omega

variable {U T : Subgroup G} {hTU : ∀ t ∈ T, ∀ u ∈ U, t * u * t⁻¹ ∈ U}

/-- Uniqueness of the torus part in `U n T U`. -/
theorem torus_part_unique {n : G} (hn2 : n * n = 1) (hUT : ∀ u ∈ U, u ∈ T → u = 1)
    (hV : ∀ u ∈ U, n * u * n ∈ borelOf U T hTU → u = 1)
    {a b a' b' s s' : G} (ha : a ∈ U) (hb : b ∈ U) (ha' : a' ∈ U) (hb' : b' ∈ U) (hs : s ∈ T)
    (hs' : s' ∈ T) (h : a * n * s * b = a' * n * s' * b') : s = s' := by
  have hninv : n⁻¹ = n := inv_eq_of_mul_eq_one_right hn2
  have h1 : a'⁻¹ * a = 1 := by
    refine hV _ (U.mul_mem (U.inv_mem ha') ha) ⟨s' * s⁻¹, T.mul_mem hs' (T.inv_mem hs),
      s * (b' * b⁻¹) * s⁻¹, hTU s hs _ (U.mul_mem hb' (U.inv_mem hb)), ?_⟩
    calc n * (a'⁻¹ * a) * n = n⁻¹ * a'⁻¹ * (a * n * s * b) * b⁻¹ * s⁻¹ := by
          rw [hninv]; group
      _ = n⁻¹ * a'⁻¹ * (a' * n * s' * b') * b⁻¹ * s⁻¹ := by rw [h]
      _ = s' * s⁻¹ * (s * (b' * b⁻¹) * s⁻¹) := by group
  have haa : a = a' := by rw [inv_mul_eq_one] at h1; exact h1.symm
  subst haa
  have h2 : s'⁻¹ * s = b' * b⁻¹ := by
    have : s * b = s' * b' := by
      have := congrArg (fun x => (a * n)⁻¹ * x) h
      simpa [mul_assoc] using this
    calc s'⁻¹ * s = s'⁻¹ * (s * b) * b⁻¹ := by group
      _ = s'⁻¹ * (s' * b') * b⁻¹ := by rw [this]
      _ = b' * b⁻¹ := by group
  have h3 := hUT _ (h2 ▸ U.mul_mem hb' (U.inv_mem hb)) (T.mul_mem (T.inv_mem hs') hs)
  rw [inv_mul_eq_one] at h3
  exact h3.symm

/-- **`T n ⊆ UnUnU` from the prime-field words.** -/
theorem rankOne_tn_mem_of_words (n : G) (hn2 : n * n = 1)
    (hUT : ∀ u ∈ U, u ∈ T → u = 1) (hnB : n ∉ borelOf U T hTU)
    (hV : ∀ u ∈ U, n * u * n ∈ borelOf U T hTU → u = 1)
    (hcover : ∀ g : G, g ∈ borelOf U T hTU ∨ ∃ u ∈ U, ∃ t ∈ T, ∃ u' ∈ U, g = u * n * t * u')
    (hinvT : ∀ t ∈ T, n * t * n = t⁻¹) (hcyc : IsCyclic T)
    {u₀ u₁ u₂ h : G} (hu₀ : u₀ ∈ U) (hu₁ : u₁ ∈ U) (hu₂ : u₂ ∈ U) (hh : h ∈ T)
    (hns : ∀ m ∈ T, h ≠ m * m)
    (hA : n = u₁ * (n * u₁ * n⁻¹) * u₁)
    (hB : h = u₀ * (n * u₀ * n⁻¹) * (n * u₀ * n⁻¹) * (n * u₁ * n⁻¹) * u₂ * (n * u₁ * n⁻¹)) :
    ∀ t ∈ T, ∃ a ∈ U, ∃ b ∈ U, ∃ c ∈ U, t * n = a * n * b * n * c := by
  have hninv : n⁻¹ = n := inv_eq_of_mul_eq_one_right hn2
  have hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    intro x hx y hy
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hx⟩)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨y, hy⟩)
    have hi' : (g : G) ^ i = x := congrArg Subtype.val hi
    have hj' : (g : G) ^ j = y := congrArg Subtype.val hj
    rw [← hi', ← hj', ← zpow_add, ← zpow_add, add_comm]
  -- `P s`: `s` is the torus part of some `ncn`
  let P : G → Prop := fun s => ∃ c ∈ U, ∃ a ∈ U, ∃ b ∈ U, n * c * n = a * n * s * b
  -- from `P t⁻¹` to the goal
  have hgoal : ∀ t ∈ T, P t⁻¹ → ∃ a ∈ U, ∃ b ∈ U, ∃ c ∈ U, t * n = a * n * b * n * c := by
    rintro t ht ⟨c, hc, a, ha, b, hb, e⟩
    refine ⟨a⁻¹, U.inv_mem ha, c, hc, b⁻¹, U.inv_mem hb, ?_⟩
    have htn : t * n = n * t⁻¹ := by
      have := hinvT t ht
      calc t * n = n⁻¹ * (n * t * n) := by group
        _ = n * t⁻¹ := by rw [this, hninv]
    calc t * n = a⁻¹ * (a * n * t⁻¹ * b) * b⁻¹ := by rw [htn]; group
      _ = a⁻¹ * (n * c * n) * b⁻¹ := by rw [e]
      _ = a⁻¹ * n * c * n * b⁻¹ := by group
  -- stability under squares
  have hsq : ∀ s ∈ T, P s → ∀ m ∈ T, P (s * (m * m)) := by
    rintro s hs ⟨c, hc, a, ha, b, hb, e⟩ m hm
    have hmn : m⁻¹ * n = n * m := by
      have := hinvT m⁻¹ (T.inv_mem hm)
      rw [inv_inv] at this
      calc m⁻¹ * n = n⁻¹ * (n * m⁻¹ * n) := by group
        _ = n * m := by rw [this, hninv]
    have e3 : m⁻¹ * n * m⁻¹ = n := by
      calc m⁻¹ * n * m⁻¹ = n * m * m⁻¹ := by rw [hmn]
        _ = n := by group
    have e4 : m * n * m = n := by
      calc m * n * m = m * (n * m) := by group
        _ = m * (m⁻¹ * n) := by rw [hmn]
        _ = n := by group
    refine ⟨m * c * m⁻¹, hTU m hm c hc,
      m⁻¹ * a * m, by simpa using hTU _ (T.inv_mem hm) a ha,
      m⁻¹ * b * m, by simpa using hTU _ (T.inv_mem hm) b hb, ?_⟩
    have hsm : s * (m * m) = m * s * m := by rw [← mul_assoc, hcomm s hs m hm]
    have l1 : m⁻¹ * (n * c * n) * m = n * (m * c * m⁻¹) * n := by
      calc m⁻¹ * (n * c * n) * m = (m⁻¹ * n * m⁻¹) * (m * c * m⁻¹) * (m * n * m) := by group
        _ = n * (m * c * m⁻¹) * n := by rw [e3, e4]
    have l2 : m⁻¹ * (a * n * s * b) * m = m⁻¹ * a * m * n * (s * (m * m)) * (m⁻¹ * b * m) := by
      calc m⁻¹ * (a * n * s * b) * m =
            m⁻¹ * a * m * (m⁻¹ * n * m⁻¹) * (m * s * m) * (m⁻¹ * b * m) := by group
        _ = _ := by rw [e3, hsm]
    rw [← l1, e, l2]
  -- Bruhat form of `ncn`
  have hbru : ∀ c ∈ U, c ≠ 1 → ∃ a ∈ U, ∃ s ∈ T, ∃ b ∈ U, n * c * n = a * n * s * b := by
    intro c hc hc1
    rcases hcover (n * c * n) with hB' | h'
    · exact absurd (hV c hc hB') hc1
    · exact h'
  -- auxiliary identities
  have F2 : n * u₁ * n⁻¹ = u₁⁻¹ * n * u₁⁻¹ := by
    calc n * u₁ * n⁻¹ = u₁⁻¹ * (u₁ * (n * u₁ * n⁻¹) * u₁) * u₁⁻¹ := by group
      _ = u₁⁻¹ * n * u₁⁻¹ := by rw [← hA]
  have hu₁1 : u₁ ≠ 1 := by
    rintro rfl
    apply hnB
    have : n = 1 := by
      have h' := hA
      simp only [mul_one, one_mul, mul_inv_cancel] at h'
      exact h'
    rw [this]; exact (borelOf U T hTU).one_mem
  have F1 : h * n = n * h⁻¹ := by
    calc h * n = n⁻¹ * (n * h * n) := by group
      _ = n * h⁻¹ := by rw [hinvT h hh, hninv]
  have F3 : n * h⁻¹ * n = h := by rw [hinvT _ (T.inv_mem hh), inv_inv]
  set u' := h⁻¹ * u₁⁻¹ * h with hu'
  have hu'U : u' ∈ U := by simpa using hTU _ (T.inv_mem hh) _ (U.inv_mem hu₁)
  have hu'1 : u' ≠ 1 := by
    intro h1
    apply hu₁1
    have : u₁⁻¹ = 1 := by
      calc u₁⁻¹ = h * u' * h⁻¹ := by rw [hu']; group
        _ = 1 := by rw [h1]; group
    simpa using this
  set x := u₀ * u₀ * u₁ with hx
  have hxU : x ∈ U := U.mul_mem (U.mul_mem hu₀ hu₀) hu₁
  set y := u₂ * u₁⁻¹ with hy
  have hyU : y ∈ U := U.mul_mem hu₂ (U.inv_mem hu₁)
  have key : n * u' * n * h * u₁⁻¹ = u₀ * (n * x * n) * y := by
    have lhs : n * u' * n * h * u₁⁻¹ = h * u₁ * n⁻¹ := by
      calc n * u' * n * h * u₁⁻¹ = n * h⁻¹ * u₁⁻¹ * (h * n) * h * u₁⁻¹ := by rw [hu']; group
        _ = n * h⁻¹ * (u₁⁻¹ * n * u₁⁻¹) := by rw [F1]; group
        _ = n * h⁻¹ * (n * u₁ * n⁻¹) := by rw [F2]
        _ = (n * h⁻¹ * n) * u₁ * n⁻¹ := by group
        _ = h * u₁ * n⁻¹ := by rw [F3]
    have rhs : h * u₁ * n⁻¹ = u₀ * (n * x * n⁻¹) * y := by
      calc h * u₁ * n⁻¹ = u₀ * (n * x * n⁻¹) * u₂ * (n * u₁ * n⁻¹) * u₁ * n⁻¹ := by
            rw [hB, hx]; group
        _ = u₀ * (n * x * n⁻¹) * u₂ * (u₁⁻¹ * n * u₁⁻¹) * u₁ * n⁻¹ := by rw [F2]
        _ = u₀ * (n * x * n⁻¹) * y := by rw [hy]; group
    rw [lhs, rhs, hninv]
  obtain ⟨a', ha', s', hs', b', hb', e'⟩ := hbru u' hu'U hu'1
  have hLHS : n * u' * n * h * u₁⁻¹ = a' * n * (s' * h) * (h⁻¹ * b' * h * u₁⁻¹) := by
    rw [e']; group
  have hb'' : h⁻¹ * b' * h * u₁⁻¹ ∈ U :=
    U.mul_mem (by simpa using hTU _ (T.inv_mem hh) _ hb') (U.inv_mem hu₁)
  have hx1 : x ≠ 1 := by
    intro hx1
    apply hnB
    have h' := key
    rw [hLHS, hx1, mul_one, hn2, mul_one] at h'
    have : n = a'⁻¹ * (u₀ * y) * (h⁻¹ * b' * h * u₁⁻¹)⁻¹ * (s' * h)⁻¹ := by
      rw [← h']; group
    rw [this]
    have hU := le_borelOf_right U T hTU
    have hT := le_borelOf_left U T hTU
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hU (U.inv_mem ha'))
      (hU (U.mul_mem hu₀ hyU))) (hU (U.inv_mem hb''))) (hT (T.inv_mem (T.mul_mem hs' hh)))
  obtain ⟨a, ha, s₀, hs₀, b, hb, e⟩ := hbru x hxU hx1
  have hss : s' * h = s₀ := by
    refine torus_part_unique (hTU := hTU) hn2 hUT hV ha' hb'' (U.mul_mem hu₀ ha)
      (U.mul_mem hb hyU) (T.mul_mem hs' hh) hs₀ ?_
    rw [← hLHS, key, e]; group
  have hPs' : P s' := ⟨u', hu'U, a', ha', b', hb', e'⟩
  have hPs : P (s' * h) := ⟨x, hxU, a, ha, b, hb, by rw [hss]; exact e⟩
  intro t ht
  apply hgoal t ht
  obtain ⟨m, hm, hm' | hm'⟩ := exists_eq_mul_sq_of_isCyclic T hcyc hh hns hs' (T.inv_mem ht)
  · rw [hm']; exact hsq s' hs' hPs' m hm
  · rw [hm']; exact hsq (s' * h) (T.mul_mem hs' hh) hPs m hm

end CFSGOutside.HallPaige
