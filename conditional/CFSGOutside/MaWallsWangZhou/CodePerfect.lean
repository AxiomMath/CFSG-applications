import CFSGOutside.MaWallsWangZhou.Defs

/-!
# Subgroup perfect codes in Cayley graphs: Theorem 1.1 (Lemmas 3.1 and 3.2)

X. Ma, G. L. Walls, K. Wang, S. Zhou, *Subgroup perfect codes in Cayley graphs*, SIAM J. Discrete Math. 34
(2020) 1909-1921. A group has an element of order `4` iff it is not code-perfect; the proof builds an
inverse-closed right transversal of each subgroup by double cosets.
-/

namespace CFSGOutside.MaWallsWangZhou

open Classical

section Transversal

variable {G : Type*} [Group G] (H : Subgroup G)

/-- An inverse-closed right transversal containing `1` gives a perfect code. -/
theorem isPerfectCodeOf_of_transversal (T : Set G) (h1 : (1 : G) ∈ T)
    (hinv : ∀ t ∈ T, t⁻¹ ∈ T) (huniq : ∀ x : G, ∃! t, t ∈ T ∧ t * x⁻¹ ∈ H) :
    IsPerfectCodeOf (H : Set G) := by
  refine ⟨T \ {1}, ?_, fun h => h.2 rfl, ?_, ?_⟩
  · ext s
    simp only [Set.mem_inv, Set.mem_diff, Set.mem_singleton_iff, inv_eq_one]
    exact ⟨fun h => ⟨by simpa using hinv _ h.1, h.2⟩, fun h => ⟨hinv _ h.1, h.2⟩⟩
  · -- independence
    have hT1 : ∀ s ∈ T, s ∈ H → s = 1 := by
      intro s hs hsH
      obtain ⟨t, -, ht⟩ := huniq 1
      have e1 := ht s ⟨hs, by simpa using hsH⟩
      have e2 := ht 1 ⟨h1, by simp⟩
      rw [e1, e2]
    rintro u (hu : u ∈ H) v (hv : v ∈ H) ⟨-, h | h⟩
    · exact h.2 (hT1 _ h.1 (H.mul_mem hv (H.inv_mem hu)))
    · exact h.2 (hT1 _ h.1 (H.mul_mem hu (H.inv_mem hv)))
  · intro v (hv : v ∉ H)
    obtain ⟨t, ⟨htT, htH⟩, htu⟩ := huniq v⁻¹
    rw [inv_inv] at htH
    have ht1 : t ≠ 1 := by rintro rfl; exact hv (by simpa using htH)
    refine ⟨t * v, ⟨htH, ?_, Or.inl ?_⟩, ?_⟩
    · intro h
      apply ht1
      have : v * v⁻¹ = t * v * v⁻¹ := by rw [← h]
      simpa using this.symm
    · rw [mul_inv_cancel_right]
      exact ⟨htT, by simpa using ht1⟩
    · rintro u ⟨(huH : u ∈ H), -, hadj⟩
      have hs : u * v⁻¹ ∈ T \ {1} := by
        rcases hadj with h | h
        · exact h
        · refine ⟨?_, ?_⟩
          · simpa using hinv _ h.1
          · intro h'; exact h.2 (by simpa using (inv_eq_one.mpr h'))
      have := htu (u * v⁻¹) ⟨hs.1, by simpa using huH⟩
      calc u = u * v⁻¹ * v := by group
        _ = t * v := by rw [this]

/-- An element of order `4` makes `⟨g²⟩` a non-perfect code (Lemma 3.1, "only if"). -/
theorem not_isPerfectCodeOf_of_orderOf_eq_four {g : G} (hg : orderOf g = 4) :
    ¬ IsPerfectCodeOf ((Subgroup.zpowers (g ^ 2) : Subgroup G) : Set G) := by
  rintro ⟨S, hS, -, -, hcode⟩
  have hodd : ∀ m : ℤ, Odd m → g ^ m = g ∨ g ^ m = g⁻¹ := by
    intro m hm
    rw [← zpow_mod_orderOf, hg]
    have : m % ((4 : ℕ) : ℤ) = 1 ∨ m % ((4 : ℕ) : ℤ) = 3 := by
      obtain ⟨j, rfl⟩ := hm; push_cast; omega
    rcases this with h | h
    · left; rw [h, zpow_one]
    · right
      rw [h, eq_inv_iff_mul_eq_one]
      have : g ^ (3 : ℤ) * g = g ^ (4 : ℕ) := by
        rw [← zpow_natCast, ← zpow_add_one]; norm_num
      rw [this, ← hg, pow_orderOf_eq_one]
  have hSg : ∀ s, s⁻¹ ∈ S ↔ s ∈ S := fun s => by
    rw [← Set.mem_inv, hS]
  have hgS : ∀ s, (s = g ∨ s = g⁻¹) → (s ∈ S ↔ g ∈ S) := by
    rintro s (rfl | rfl)
    · rfl
    · exact hSg g
  have hg1 : g ≠ 1 := by rintro rfl; simp at hg
  have hg2 : g ^ 2 ≠ 1 := by
    intro h
    have := orderOf_le_of_pow_eq_one (by norm_num) h
    omega
  have hnot : g ∉ (Subgroup.zpowers (g ^ 2) : Set G) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← zpow_natCast, ← zpow_mul] at hk
    have h1 : g ^ ((2 : ℕ) * k - 1 : ℤ) = 1 := by rw [zpow_sub_one, hk, mul_inv_cancel]
    rw [← orderOf_dvd_iff_zpow_eq_one, hg] at h1
    push_cast at h1
    omega
  obtain ⟨u, ⟨huH, hadj⟩, hu⟩ := hcode g hnot
  -- any neighbour of `g` in `⟨g²⟩` forces `g ∈ S`
  have hmemS : g ∈ S := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp huH
    have e1 : (g ^ 2) ^ k * g⁻¹ = g ^ (2 * k - 1) := by
      rw [← zpow_natCast, ← zpow_mul, zpow_sub_one]; push_cast; ring_nf
    have e2 : g * ((g ^ 2) ^ k)⁻¹ = (g ^ (2 * k - 1))⁻¹ := by
      rw [← e1]; group
    have ho : Odd (2 * k - 1) := ⟨k - 1, by ring⟩
    rcases hadj.2 with h | h
    · rw [e1] at h; exact (hgS _ (hodd _ ho)).mp h
    · rw [e2, hSg] at h; exact (hgS _ (hodd _ ho)).mp h
  have hadj1 : (cayleyGraph S).Adj g 1 := ⟨hg1, Or.inr (by simpa using hmemS)⟩
  have hadj2 : (cayleyGraph S).Adj g (g ^ 2) := by
    refine ⟨fun h => hg1 ?_, Or.inl ?_⟩
    · have : g * g = g * 1 := by rw [mul_one, ← sq, ← h]
      exact mul_left_cancel this
    · have : g ^ 2 * g⁻¹ = g := by group
      rw [this]; exact hmemS
  have a := hu 1 ⟨Subgroup.one_mem _, hadj1⟩
  have b := hu (g ^ 2) ⟨Subgroup.mem_zpowers _, hadj2⟩
  exact hg2 (b.trans a.symm)

end Transversal


section Construction

variable {G : Type*} [Group G] [Fintype G] (H : Subgroup G)

/-- The double cosets `H x H`, as a setoid on `G`. -/
def dsetoid : Setoid G where
  r x y := ∃ a ∈ H, ∃ b ∈ H, y = a * x * b
  iseqv := ⟨fun _ => ⟨1, H.one_mem, 1, H.one_mem, by simp⟩,
    fun ⟨a, ha, b, hb, e⟩ => ⟨a⁻¹, H.inv_mem ha, b⁻¹, H.inv_mem hb, by rw [e]; group⟩,
    fun ⟨a, ha, b, hb, e⟩ ⟨c, hc, d, hd, f⟩ =>
      ⟨c * a, H.mul_mem hc ha, b * d, H.mul_mem hb hd, by rw [f, e]; group⟩⟩

/-- Right cosets `H x`. -/
abbrev RC := Quotient (QuotientGroup.rightRel H)

/-- Double cosets `H x H`. -/
abbrev DC := Quotient (dsetoid H)

variable {H}

/-- The right coset `H g`. -/
def mkR (g : G) : RC H := Quotient.mk _ g

lemma mkR_eq {a b : G} : mkR (H := H) a = mkR b ↔ b * a⁻¹ ∈ H :=
  ⟨fun h => QuotientGroup.rightRel_apply.mp (Quotient.exact h),
    fun h => Quotient.sound (QuotientGroup.rightRel_apply.mpr h)⟩

variable (H) in
/-- The double coset containing a right coset. -/
def cls : RC H → DC H :=
  Quotient.lift (fun g => (Quotient.mk (dsetoid H) g)) (fun a b hab =>
    Quotient.sound ⟨b * a⁻¹, QuotientGroup.rightRel_apply.mp hab, 1, H.one_mem, by group⟩)

variable (H) in
/-- `H x H ↦ H x⁻¹ H`. -/
def dinv : DC H → DC H :=
  Quotient.map (fun g => g⁻¹) (fun _ _ ⟨a, ha, b, hb, e⟩ =>
    ⟨b⁻¹, H.inv_mem hb, a⁻¹, H.inv_mem ha, by rw [e]; group⟩)

lemma cls_mkR (g : G) : cls H (mkR g) = Quotient.mk (dsetoid H) g := rfl

lemma dinv_mk (g : G) : dinv H (Quotient.mk (dsetoid H) g) = Quotient.mk (dsetoid H) g⁻¹ := rfl

lemma dinv_dinv (D : DC H) : dinv H (dinv H D) = D := by
  induction D using Quotient.inductionOn with
  | h g => rw [dinv_mk, dinv_mk, inv_inv]

/-- Any right coset in `D` is linked to any right coset in `D⁻¹`. -/
lemma exists_link (c d : RC H) (h : cls H d = dinv H (cls H c)) :
    ∃ g, mkR g = c ∧ mkR g⁻¹ = d := by
  induction c using Quotient.inductionOn with
  | h y =>
  induction d using Quotient.inductionOn with
  | h z =>
  obtain ⟨a, ha, b, hb, e⟩ := Quotient.exact h
  have e' : y⁻¹ = a * z * b := e
  have hz : z = a⁻¹ * y⁻¹ * b⁻¹ := by rw [e']; group
  refine ⟨b * y, ?_, ?_⟩
  · change mkR (b * y) = mkR y
    rw [mkR_eq]
    have : y * (b * y)⁻¹ = b⁻¹ := by group
    rw [this]; exact H.inv_mem hb
  · change mkR (b * y)⁻¹ = mkR z
    rw [mkR_eq, hz]
    have : a⁻¹ * y⁻¹ * b⁻¹ * (b * y)⁻¹⁻¹ = a⁻¹ := by group
    rw [this]; exact H.inv_mem ha

/-- If `G` has no element of order `4`, every right coset in a self-inverse double coset
contains an element `g` with `g² = 1`. -/
lemma exists_sq_eq_one (hno4 : ∀ g : G, orderOf g ≠ 4) (c : RC H)
    (h : cls H c = dinv H (cls H c)) : ∃ g, mkR g = c ∧ g * g = 1 := by
  obtain ⟨g, hg1, hg2⟩ := exists_link c c h
  have hgH : g ^ 2 ∈ H := by
    rw [← hg1, mkR_eq] at hg2
    rw [inv_inv] at hg2
    rw [sq]; exact hg2
  have hn0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have h4 : ¬ 4 ∣ orderOf g := fun h4 => hno4 _ (orderOf_pow_orderOf_div hn0 h4)
  rcases Nat.even_or_odd (orderOf g) with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- `orderOf g = 2m`, `m` odd
    have hmodd : m % 2 = 1 := by omega
    have hy : g ^ m * g ^ m = 1 := by rw [← pow_add, ← hm, pow_orderOf_eq_one]
    refine ⟨g ^ m, ?_, hy⟩
    rw [← hg1, mkR_eq, inv_eq_of_mul_eq_one_right hy, ← pow_succ']
    have : g ^ (m + 1) = (g ^ 2) ^ ((m + 1) / 2) := by
      rw [← pow_mul]; congr 1; omega
    rw [this]; exact H.pow_mem hgH _
  · refine ⟨1, ?_, by simp⟩
    rw [← hg1, mkR_eq, inv_one, mul_one]
    have : g = (g ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = orderOf g + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    rw [this]; exact H.pow_mem hgH _

lemma card_fiber (c : RC H) :
    (Finset.univ.filter fun g : G => mkR g = c).card = Fintype.card H := by
  induction c using Quotient.inductionOn with
  | h r =>
  rw [← Finset.card_univ (α := H)]
  have hmem : ∀ g : G, mkR (H := H) g = mkR r ↔ g * r⁻¹ ∈ H := fun g => by
    rw [mkR_eq]
    constructor
    · intro h; simpa using H.inv_mem h
    · intro h; simpa using H.inv_mem h
  refine Finset.card_nbij' (fun g => if hg : g * r⁻¹ ∈ H then (⟨g * r⁻¹, hg⟩ : H) else 1)
    (fun h => (h : G) * r) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro h _
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    show mkR _ = mkR r
    rw [hmem, mul_inv_cancel_right]; exact h.2
  · intro g hg
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hg
    dsimp only
    rw [dif_pos ((hmem g).mp hg)]
    simp
  · intro h _
    have : (h : G) * r * r⁻¹ ∈ H := by rw [mul_inv_cancel_right]; exact h.2
    simp only [dif_pos this]
    ext; simp

lemma card_elems (D : DC H) :
    (Finset.univ.filter fun g : G => (Quotient.mk (dsetoid H) g) = D).card =
      (Finset.univ.filter fun c : RC H => cls H c = D).card * Fintype.card H := by
  rw [Finset.card_eq_sum_card_fiberwise (f := mkR) (t := Finset.univ.filter fun c => cls H c = D)]
  · rw [Finset.sum_congr rfl (g := fun _ => Fintype.card H), Finset.sum_const, smul_eq_mul]
    intro c hc
    rw [← card_fiber c, Finset.filter_filter]
    congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    constructor
    · exact fun h => h.2
    · intro h; refine ⟨?_, h⟩; rw [← cls_mkR, h, hc]
  · intro g hg
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hg ⊢
    exact hg

lemma card_cls_dinv (D : DC H) :
    Fintype.card {c : RC H // cls H c = D} = Fintype.card {c : RC H // cls H c = dinv H D} := by
  rw [Fintype.card_subtype, Fintype.card_subtype]
  have hpos : 0 < Fintype.card H := Fintype.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [← card_elems, ← card_elems]
  refine Finset.card_nbij' (fun g => g⁻¹) (fun g => g⁻¹) ?_ ?_ (fun g _ => inv_inv g)
    (fun g _ => inv_inv g)
  · intro g hg
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hg ⊢
    rw [← dinv_mk, hg]
  · intro g hg
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hg ⊢
    rw [← dinv_dinv D, ← hg, dinv_mk]

variable (H) in
/-- A bijection between the right cosets of `D` and those of `D⁻¹`. -/
noncomputable def pairEquiv (D : DC H) :
    {c : RC H // cls H c = D} ≃ {c : RC H // cls H c = dinv H D} :=
  Fintype.equivOfCardEq (card_cls_dinv D)

/-- The partner coset of `c` (in `D⁻¹`). -/
noncomputable def partner (c : RC H) : RC H := (pairEquiv H (cls H c) ⟨c, rfl⟩).1

lemma cls_partner (c : RC H) : cls H (partner c) = dinv H (cls H c) :=
  (pairEquiv H (cls H c) ⟨c, rfl⟩).2

lemma partner_eq (c : RC H) (D : DC H) (h : cls H c = D) :
    partner c = (pairEquiv H D ⟨c, h⟩).1 := by subst h; rfl

lemma partner_inj {c d : RC H} (hcd : cls H c = cls H d) (h : partner c = partner d) : c = d := by
  rw [partner_eq c (cls H d) hcd] at h
  have := (pairEquiv H (cls H d)).injective (Subtype.ext h)
  exact congrArg Subtype.val this

lemma partner_surj (d : RC H) : ∃ c, cls H c = dinv H (cls H d) ∧ partner c = d := by
  set D := dinv H (cls H d)
  have hd : cls H d = dinv H D := (dinv_dinv _).symm
  set x := (pairEquiv H D).symm ⟨d, hd⟩
  refine ⟨x.1, x.2, ?_⟩
  rw [partner_eq x.1 D x.2]
  have : (⟨x.1, x.2⟩ : {c : RC H // cls H c = D}) = x := rfl
  rw [this, Equiv.apply_symm_apply]

/-- The inverse of `partner`. -/
noncomputable def partnerInv (d : RC H) : RC H := Classical.choose (partner_surj d)

lemma partnerInv_spec (d : RC H) :
    cls H (partnerInv d) = dinv H (cls H d) ∧ partner (partnerInv d) = d :=
  Classical.choose_spec (partner_surj d)

/-- An element of `c` whose inverse lies in the partner coset. -/
noncomputable def prim (c : RC H) : G :=
  Classical.choose (exists_link c (partner c) (cls_partner c))

lemma prim_spec (c : RC H) : mkR (prim c) = c ∧ mkR (prim c)⁻¹ = partner c :=
  Classical.choose_spec (exists_link c (partner c) (cls_partner c))

/-- Index of double cosets (to orient the pairs `{D, D⁻¹}`). -/
noncomputable def ι (D : DC H) : ℕ := (Fintype.equivFin (DC H) D : ℕ)

lemma ι_inj {D E : DC H} (h : ι D = ι E) : D = E :=
  (Fintype.equivFin (DC H)).injective (Fin.ext h)

variable (hno4 : ∀ g : G, orderOf g ≠ 4)
include hno4

/-- In a self-inverse double coset: an element of `c` with square `1`. -/
noncomputable def selfpick (c : RC H) (h : cls H c = dinv H (cls H c)) : G :=
  Classical.choose (exists_sq_eq_one hno4 c h)

lemma selfpick_spec (c : RC H) (h : cls H c = dinv H (cls H c)) :
    mkR (selfpick hno4 c h) = c ∧ selfpick hno4 c h * selfpick hno4 c h = 1 :=
  Classical.choose_spec (exists_sq_eq_one hno4 c h)

/-- The representative chosen for the right coset `c`. -/
noncomputable def τ (c : RC H) : G :=
  if c = mkR 1 then 1
  else if h : cls H c = dinv H (cls H c) then selfpick hno4 c h
  else if ι (cls H c) < ι (dinv H (cls H c)) then prim c
  else (prim (partnerInv c))⁻¹

omit hno4 in
lemma cls_one_self : cls H (mkR (1 : G)) = dinv H (cls H (mkR 1)) := by
  rw [cls_mkR, dinv_mk, inv_one]

lemma mkR_τ (c : RC H) : mkR (τ hno4 c) = c := by
  unfold τ
  split_ifs with h1 h2 h3
  · exact h1.symm
  · exact (selfpick_spec hno4 c h2).1
  · exact (prim_spec c).1
  · rw [(prim_spec _).2, (partnerInv_spec c).2]

lemma τ_inv (c : RC H) : τ hno4 (mkR (H := H) (τ hno4 c)⁻¹) = (τ hno4 c)⁻¹ := by
  by_cases h1 : c = mkR 1
  · have : τ hno4 c = 1 := by unfold τ; rw [if_pos h1]
    rw [this, inv_one]; unfold τ; rw [if_pos rfl]
  by_cases h2 : cls H c = dinv H (cls H c)
  · have hτ : τ hno4 c = selfpick hno4 c h2 := by unfold τ; rw [if_neg h1, dif_pos h2]
    obtain ⟨hs1, hs2⟩ := selfpick_spec hno4 c h2
    have hinv : (selfpick hno4 c h2)⁻¹ = selfpick hno4 c h2 := inv_eq_of_mul_eq_one_right hs2
    rw [hτ, hinv, hs1, hτ]
  have hne : ι (cls H c) ≠ ι (dinv H (cls H c)) := fun h => h2 (ι_inj h)
  by_cases h3 : ι (cls H c) < ι (dinv H (cls H c))
  · -- primary
    have hτ : τ hno4 c = prim c := by unfold τ; rw [if_neg h1, dif_neg h2, if_pos h3]
    rw [hτ, (prim_spec c).2]
    set d := partner c
    have hd : cls H d = dinv H (cls H c) := cls_partner c
    have hd2 : ¬ cls H d = dinv H (cls H d) := by
      rw [hd, dinv_dinv]; exact fun h => h2 h.symm
    have hd1 : d ≠ mkR 1 := fun h => hd2 (h ▸ cls_one_self)
    have hd3 : ¬ ι (cls H d) < ι (dinv H (cls H d)) := by rw [hd, dinv_dinv]; omega
    have hpi : partnerInv d = c := by
      obtain ⟨e1, e2⟩ := partnerInv_spec d
      refine partner_inj ?_ e2
      rw [e1, hd, dinv_dinv]
    unfold τ
    rw [if_neg hd1, dif_neg hd2, if_neg hd3, hpi]
  · -- secondary
    have hτ : τ hno4 c = (prim (partnerInv c))⁻¹ := by
      unfold τ; rw [if_neg h1, dif_neg h2, if_neg h3]
    rw [hτ, inv_inv, (prim_spec _).1]
    set x := partnerInv c
    obtain ⟨hx, hxp⟩ := partnerInv_spec c
    have hx2 : ¬ cls H x = dinv H (cls H x) := by
      rw [hx, dinv_dinv]; exact fun h => h2 h.symm
    have hx1 : x ≠ mkR 1 := fun h => hx2 (h ▸ cls_one_self)
    have hx3 : ι (cls H x) < ι (dinv H (cls H x)) := by rw [hx, dinv_dinv]; omega
    unfold τ
    rw [if_neg hx1, dif_neg hx2, if_pos hx3]

omit hno4 in
/-- **Lemma 3.2.** If `G` has no element of order `4`, every subgroup has an inverse-closed right
transversal containing `1`. -/
theorem exists_transversal (hno4 : ∀ g : G, orderOf g ≠ 4) :
    ∃ T : Set G, (1 : G) ∈ T ∧ (∀ t ∈ T, t⁻¹ ∈ T) ∧ ∀ x : G, ∃! t, t ∈ T ∧ t * x⁻¹ ∈ H := by
  refine ⟨Set.range (τ (H := H) hno4), ⟨mkR 1, ?_⟩, ?_, ?_⟩
  · unfold τ; rw [if_pos rfl]
  · rintro _ ⟨c, rfl⟩
    exact ⟨_, τ_inv hno4 c⟩
  · intro x
    refine ⟨τ hno4 (mkR x), ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
    · have := mkR_τ (H := H) hno4 (mkR x)
      rw [mkR_eq] at this
      simpa using H.inv_mem this
    · rintro _ ⟨⟨c, rfl⟩, hc⟩
      have : mkR (H := H) (τ hno4 c) = mkR x := by
        rw [mkR_eq]; simpa using H.inv_mem hc
      rw [mkR_τ] at this
      rw [this]

end Construction

end CFSGOutside.MaWallsWangZhou
