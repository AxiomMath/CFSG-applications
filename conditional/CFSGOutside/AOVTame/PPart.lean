import CFSGOutside.AOVTame.SatGroup
import CFSGOutside.AOVTame.Surj

/-!
# AOV tameness: group-theoretic lemmas for the decomposition of `Aut_typ^I(L(A × B))`

* `p`-parts and `p'`-parts of elements;
* a normal subgroup of `N` containing a Sylow subgroup of `N` and all `p'`-elements of `N` is `N`;
* fully normalized conjugates, and conjugating normalizers into normalizers;
* overgroups of centric subgroups are centric; proper subgroups of a `p`-group grow under
  normalizers.
-/

namespace AndersenOliverVentura.Tame

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

/-- Every element is a product of a `p`-element and a `p'`-element, both powers of it. -/
lemma exists_ppart (g : G) : ∃ g₁ ∈ zpowers g, ∃ g₂ ∈ zpowers g, g = g₁ * g₂ ∧
    (∃ k : ℕ, g₁ ^ (p ^ k) = 1) ∧ ∃ m : ℕ, ¬ p ∣ m ∧ g₂ ^ m = 1 := by
  have hn : orderOf g ≠ 0 := (orderOf_pos g).ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.out.ne_one
  have hcop : Nat.Coprime (p ^ k) m :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm)
  have hbez := Nat.gcd_eq_gcd_ab (p ^ k) m
  rw [hcop.gcd_eq_one] at hbez
  set x := Nat.gcdA (p ^ k) m
  set y := Nat.gcdB (p ^ k) m
  refine ⟨g ^ ((m : ℤ) * y), ⟨_, rfl⟩, g ^ (((p ^ k : ℕ) : ℤ) * x), ⟨_, rfl⟩, ?_, ⟨k, ?_⟩, m, hm, ?_⟩
  · rw [← zpow_add]
    conv_lhs => rw [← zpow_one g]
    congr 1
    push_cast at hbez ⊢
    linarith
  · rw [← zpow_natCast, ← zpow_mul]
    have : (m : ℤ) * y * ((p ^ k : ℕ) : ℤ) = (orderOf g : ℤ) * y := by
      rw [hkm]; push_cast; ring
    rw [this, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  · rw [← zpow_natCast, ← zpow_mul]
    have : ((p ^ k : ℕ) : ℤ) * x * (m : ℤ) = (orderOf g : ℤ) * x := by
      rw [hkm]; push_cast; ring
    rw [this, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]

/-- A subgroup `U ≤ N`, normal in `N`, containing a Sylow `p`-subgroup of `N` and all
`p'`-elements of `N`, is all of `N`. -/
lemma le_of_sylow_pprime {N U Q : Subgroup G} (hUN : U ≤ N) (hU : (U.subgroupOf N).Normal)
    (hQU : Q ≤ U) (hQ : IsSylowIn p Q N)
    (hp' : ∀ g ∈ N, ∀ m : ℕ, ¬ p ∣ m → g ^ m = 1 → g ∈ U) : N ≤ U := by
  intro g hg
  obtain ⟨g₁, hg₁, g₂, hg₂, hgg, ⟨k, hk⟩, m, hm, hm'⟩ := exists_ppart (p := p) g
  have hzN : zpowers g ≤ N := (zpowers_le).2 hg
  rw [hgg]
  refine mul_mem ?_ (hp' _ (hzN hg₂) m hm hm')
  have hR : IsPGroup p (zpowers g₁) := by
    rintro ⟨_, j, rfl⟩
    refine ⟨k, Subtype.ext ?_⟩
    change (g₁ ^ j) ^ (p ^ k) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  have hRN : zpowers g₁ ≤ N := (zpowers_le).2 (hzN hg₁)
  have hNN : (N.subgroupOf N).Normal := by rw [subgroupOf_self]; exact normal_top
  obtain ⟨n, hn, hnr⟩ := exists_conj_le_of_le_sup_rel (M := N) (N := N) le_rfl hQ.1 hRN
    hNN hQ.2.1 hR hQ.2.2 (hRN.trans le_sup_right)
  have h1 : n⁻¹ * g₁ * n ∈ U := hQU (hnr g₁ (mem_zpowers g₁))
  have h2 := hU.conj_mem ⟨_, hUN h1⟩ h1 ⟨n, hn⟩
  have h3 : n * (n⁻¹ * g₁ * n) * n⁻¹ ∈ U := h2
  have h4 : n * (n⁻¹ * g₁ * n) * n⁻¹ = g₁ := by group
  rwa [h4] at h3

/-- Every `p`-subgroup `P ≤ T` has a fully normalized conjugate in `T`. -/
lemma exists_fullyNormalized (T : Sylow p G) {P : Subgroup G} (hP : P ≤ T) :
    ∃ a : G, conjSub a P ≤ T ∧
      IsSylowIn p (normalizer (conjSub a P : Set G) ⊓ T) (normalizer (conjSub a P : Set G)) := by
  let f : G → ℕ := fun g => Nat.card (normalizer (conjSub g P : Set G) ⊓ (T : Subgroup G) : Subgroup G)
  have hne : ({g : G | conjSub g P ≤ T} : Set G).Nonempty := ⟨1, by
    intro x hx; rw [mem_conjSub] at hx; simpa using hP hx⟩
  obtain ⟨a, ha, hmax⟩ := Set.exists_max_image _ f (Set.toFinite _) hne
  refine ⟨a, ha, isSylowIn_normalizer T ha fun g hg => ?_⟩
  rw [conjSub_conjSub] at hg ⊢
  exact hmax _ hg

/-- If `x P x⁻¹ = P*` with `P*` fully normalized, some `y` with `y P y⁻¹ = P*` also conjugates
`N_T(P)` into `N_T(P*)`. -/
lemma exists_adjust (T : Sylow p G) {P P' : Subgroup G} (hP : P ≤ T) {x : G}
    (hx : conjSub x P = P')
    (hfn : IsSylowIn p (normalizer (P' : Set G) ⊓ T) (normalizer (P' : Set G))) :
    ∃ y : G, conjSub y P = P' ∧
      conjSub y (normalizer (P : Set G) ⊓ T) ≤ normalizer (P' : Set G) ⊓ T := by
  set R := conjSub x (normalizer (P : Set G) ⊓ T)
  have hRN : R ≤ normalizer (P' : Set G) := by
    rw [← hx]; exact conjSub_le_normalizer inf_le_left
  have hR : IsPGroup p R := ((T.isPGroup'.to_le inf_le_right).map _)
  obtain ⟨n, hn, hnr⟩ := exists_conj_le_of_le_sup_rel (M := normalizer (P' : Set G))
    (N := normalizer (P' : Set G)) le_rfl hfn.1 hRN (by rw [subgroupOf_self]; infer_instance)
    hfn.2.1 hR hfn.2.2 (hRN.trans le_sup_right)
  refine ⟨n⁻¹ * x, ?_, ?_⟩
  · rw [← conjSub_conjSub, hx]
    ext z
    rw [mem_conjSub, inv_inv]
    have := (mem_normalizer_iff.1 hn) z
    constructor
    · intro h
      have h' := (mem_normalizer_iff.1 (inv_mem hn) (n * z * n⁻¹)).1 h
      simpa [mul_assoc] using h'
    · intro h; exact (this).1 h
  · rw [← conjSub_conjSub]
    rintro _ ⟨r, hr, rfl⟩
    have := hnr r hr
    simpa [MulAut.conj_apply, mul_assoc] using this

/-- Overgroups (inside `S`) of centric subgroups are centric. -/
lemma isCentric_mono {S P R : Subgroup G} (hP : IsCentric S P) (hPR : P ≤ R) (hRS : R ≤ S) :
    IsCentric S R := by
  refine ⟨hRS, fun g hg => le_antisymm (fun c hc => ?_) (fun c hc => ?_)⟩
  · obtain ⟨hcC, hcS⟩ := mem_inf.1 hc
    have hgP : conjSub g P ≤ S := (conjSub_mono hPR).trans hg
    have h1 : c ∈ centralizer (conjSub g P : Set G) ⊓ S :=
      mem_inf.2 ⟨centralizer_le (conjSub_mono hPR) hcC, hcS⟩
    rw [hP.2 g hgP] at h1
    exact mem_inf.2 ⟨conjSub_mono hPR (mem_inf.1 h1).1, hcC⟩
  · obtain ⟨h1, h2⟩ := mem_inf.1 hc
    exact mem_inf.2 ⟨h2, hg h1⟩

/-- A proper subgroup of a finite `p`-group grows under its normalizer. -/
lemma card_lt_normalizer_inf (T : Sylow p G) {P : Subgroup G} (hP : P ≤ T) (hne : P ≠ T) :
    Nat.card P < Nat.card (normalizer (P : Set G) ⊓ T : Subgroup G) := by
  have hnil : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  have hlt : P.subgroupOf T < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hne (le_antisymm hP fun x hx => ?_)
    have : (⟨x, hx⟩ : (T : Subgroup G)) ∈ P.subgroupOf T := h ▸ mem_top _
    exact this
  have h2 := normalizerCondition_of_isNilpotent (G := (T : Subgroup G)) _ hlt
  obtain ⟨y, hyN, hyP⟩ := SetLike.exists_of_lt h2
  have hcardP : Nat.card P = Nat.card (P.subgroupOf T) :=
    Nat.card_congr (subgroupOfEquivOfLe hP).toEquiv.symm
  rw [hcardP]
  have hle : P.subgroupOf T ≤ (normalizer (P : Set G) ⊓ T : Subgroup G).subgroupOf T := by
    intro z hz
    refine ⟨?_, z.2⟩
    show (z : G) ∈ normalizer (P : Set G)
    rw [mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      exact P.mul_mem (P.mul_mem hz hw) (P.inv_mem hz)
    · intro hw
      have := P.mul_mem (P.mul_mem (P.inv_mem hz) hw) hz
      simpa [mul_assoc] using this
  have hyN' : y ∈ (normalizer (P : Set G) ⊓ T : Subgroup G).subgroupOf T := by
    refine ⟨?_, y.2⟩
    show (y : G) ∈ normalizer (P : Set G)
    rw [mem_normalizer_iff]
    intro w
    have := (mem_normalizer_iff.1 hyN)
    constructor
    · intro hw
      by_cases hwT : w ∈ (T : Subgroup G)
      · have := (this ⟨w, hwT⟩).1 hw
        exact this
      · exact absurd (hP hw) hwT
    · intro hw
      have hwT : w ∈ (T : Subgroup G) := by
        have := (T : Subgroup G).mul_mem (T.mul_mem (T.inv_mem y.2) (hP hw)) y.2
        simpa [mul_assoc] using this
      have := (this ⟨w, hwT⟩).2 hw
      exact this
  calc Nat.card (P.subgroupOf T) < Nat.card ((normalizer (P : Set G) ⊓ T : Subgroup G).subgroupOf T) :=
        Subgroup.card_lt_of_lt (lt_of_le_of_ne hle fun h => hyP (h ▸ hyN'))
    _ = Nat.card (normalizer (P : Set G) ⊓ T : Subgroup G) :=
        Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv

end AndersenOliverVentura.Tame
