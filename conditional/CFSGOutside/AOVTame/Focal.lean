import CFSGOutside.AOVTame.FullFusion

/-!
# AOV tameness: a reduced fusion system has no normal subgroup of `p`-power index

If a reduced `F` is realized by `E : S → G` with `E(S) ∈ Syl_p(G)`, and `G₀ ⊴ G` has `p`-power index,
then `F_{S₀}(G₀)` (`S₀ = E⁻¹(G₀)`) is a saturated normal subsystem of `p`-power index in `F`
(AOV Definition 1.21(a)), so it is all of `F`: `E(S) ≤ G₀`. Applied to the preimage of the odd part
of `G/[G, G]`, this gives `E(S) ≤ [G, G]` (i.e. `foc(F) = S`, AOV Theorem 1.22(a)).
-/

namespace AndersenOliverVentura.Tame

open Subgroup

variable {S : Type*} [Group S] [Finite S] {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
  {F : FusionSystem S} {T : Sylow p G} {E : S →* G}

/-- `S₀ = E⁻¹(G₀)`. -/
abbrev Sp (E : S →* G) (G₀ : Subgroup G) : Subgroup S := G₀.comap E

/-- `E` restricted to `S₀` and corestricted to `G₀`. -/
def Ep (E : S →* G) (G₀ : Subgroup G) : Sp E G₀ →* G₀ :=
  (E.comp (Sp E G₀).subtype).codRestrict G₀ (fun x => x.2)

lemma Ep_inj (hE : Function.Injective E) (G₀ : Subgroup G) : Function.Injective (Ep E G₀) :=
  fun x y h => Subtype.ext (hE (congrArg Subtype.val h))

@[simp] lemma coe_Ep (G₀ : Subgroup G) (x : Sp E G₀) : (Ep E G₀ x : G) = E x := rfl

/-- `F_{S₀}(G₀)`. -/
def Fp (hE : Function.Injective E) (G₀ : Subgroup G) : FusionSystem (Sp E G₀) :=
  ofHom (Ep E G₀) (Ep_inj hE G₀)

section
variable (hE : Function.Injective E) (hr : E.range = T) (hR : RealizedBy F E)
  (G₀ : Subgroup G) [hG₀ : G₀.Normal]
include hE hr hR

omit hG₀ in
lemma Fp_isSubsystem : F.IsSubsystem (Fp hE G₀) := by
  rintro P Q φ ⟨g₀, hg₀⟩
  obtain ⟨ψ, hψ, hψe⟩ := hR.exists_mem hE (P := P.map (Sp E G₀).subtype)
    (Q := Q.map (Sp E G₀).subtype) (g₀ : G) (by
      rintro ⟨_, x, hx, rfl⟩
      have h := congrArg Subtype.val (hg₀ ⟨x, hx⟩)
      simp only [coe_Ep, coe_mul, coe_inv] at h
      exact ⟨((φ ⟨x, hx⟩ : Sp E G₀) : S), mem_map_of_mem _ (φ ⟨x, hx⟩).2, h⟩)
  refine ⟨ψ, hψ, fun x => hE ?_⟩
  rw [hψe]
  have h := congrArg Subtype.val (hg₀ x)
  simp only [coe_Ep, coe_mul, coe_inv] at h
  exact h.symm

omit hR in
include hG₀ in
lemma not_dvd_relIndex_p : ¬ p ∣ (T : Subgroup G).relIndex G₀ := by
  rw [← relIndex_sup_normal]
  exact fun h2 => T.not_dvd_index (h2.trans (relIndex_dvd_index_of_le le_sup_left))

omit hR in
include hG₀ in
/-- The Sylow subgroup `T ∩ G₀` of `G₀`. -/
noncomputable def Tp : Sylow p G₀ :=
  IsPGroup.toSylow (P := (T : Subgroup G).subgroupOf G₀) (T.isPGroup'.comap_subtype)
    (not_dvd_relIndex_p hE hr G₀)

omit hR in
lemma range_Ep : (Ep E G₀).range = (Tp hE hr G₀ : Subgroup G₀) := by
  ext ⟨y, hy⟩
  change _ ↔ y ∈ (T : Subgroup G)
  constructor
  · rintro ⟨x, e⟩
    have := congrArg Subtype.val e
    simp only [coe_Ep] at this
    rw [← this, ← hr]; exact ⟨x, rfl⟩
  · intro h
    rw [← hr] at h
    obtain ⟨x, rfl⟩ := h
    exact ⟨⟨x, hy⟩, rfl⟩

lemma Fp_saturated : (Fp hE G₀).Saturated p :=
  saturated (T := Tp hE hr G₀) (Ep_inj hE G₀) (range_Ep hE hr G₀) (realizedBy_ofHom _ _)

lemma Fp_stronglyClosed : F.StronglyClosed (Sp E G₀) := by
  rintro x hx y ⟨Q, R, φ, hxQ, hφ, rfl⟩
  obtain ⟨g, hg⟩ := (hR Q R φ).1 hφ
  show E _ ∈ G₀
  rw [hg ⟨x, hxQ⟩]
  exact hG₀.conj_mem _ hx g

lemma Fp_frattini (P Q : Subgroup (Sp E G₀))
    (φ : P.map (Sp E G₀).subtype →* Q.map (Sp E G₀).subtype)
    (hφ : φ ∈ F.hom (P.map (Sp E G₀).subtype) (Q.map (Sp E G₀).subtype)) :
    ∃ α ∈ F.hom (Sp E G₀) (Sp E G₀), ∃ φ₀ ∈ (Fp hE G₀).hom (P.map α) Q, ∀ x : P,
      (φ ⟨(x : Sp E G₀), mem_map_of_mem _ x.2⟩ : S) =
        ((φ₀ ⟨α x, mem_map_of_mem _ x.2⟩ : Sp E G₀) : S) := by
  obtain ⟨g, hg⟩ := (hR _ _ φ).1 hφ
  have htop := Sylow.normalizer_sup_eq_top (Tp hE hr G₀)
  have hgt : g ∈ (⊤ : Subgroup G) := mem_top g
  rw [← htop, ← SetLike.mem_coe, mul_normal] at hgt
  obtain ⟨n, hn, g₀, hg₀, rfl⟩ := hgt
  have hTp : ((Tp hE hr G₀ : Subgroup G₀).map G₀.subtype) = (T : Subgroup G) ⊓ G₀ := by
    change ((T : Subgroup G).subgroupOf G₀).map G₀.subtype = _
    rw [subgroupOf_map_subtype]
  rw [hTp] at hn
  have hnS : ∀ x : Sp E G₀, n * E x * n⁻¹ ∈ ((T : Subgroup G) ⊓ G₀ : Subgroup G) := fun x =>
    (mem_normalizer_iff.1 hn (E x)).1 (mem_inf.2 ⟨mem_T hE hr hR x, x.2⟩)
  obtain ⟨α, hα, hαe⟩ := hR.exists_mem hE (P := Sp E G₀) (Q := Sp E G₀) n (fun x => by
    have h1 := hnS x
    have : n * E x * n⁻¹ ∈ E.range := hr ▸ (mem_inf.1 h1).1
    obtain ⟨y, hy⟩ := this
    refine ⟨y, ?_, hy⟩
    show E y ∈ G₀
    rw [hy]; exact (mem_inf.1 h1).2)
  have hh : n * g₀ * n⁻¹ ∈ G₀ := hG₀.conj_mem g₀ hg₀ n
  obtain ⟨φ₀, hφ₀, hφ₀e⟩ := (realizedBy_ofHom _ (Ep_inj hE G₀)).exists_mem
    (Ep_inj hE G₀) (P := P.map α) (Q := Q) ⟨n * g₀ * n⁻¹, hh⟩ (by
      rintro ⟨_, x, hx, rfl⟩
      have h1 := hg ⟨x, mem_map_of_mem _ hx⟩
      obtain ⟨z, hz, ez⟩ := (φ ⟨x, mem_map_of_mem _ hx⟩).2
      refine ⟨z, hz, Subtype.ext ?_⟩
      simp only [coe_Ep, coe_mul, coe_inv]
      rw [hαe x]
      have : E (z : S) = n * g₀ * E (x : S) * (n * g₀)⁻¹ := by
        rw [← h1]; exact congrArg E ez
      rw [this]; group)
  refine ⟨α, hα, φ₀, hφ₀, fun x => hE ?_⟩
  have h1 := hg ⟨x, mem_map_of_mem _ x.2⟩
  have h2 := congrArg Subtype.val (hφ₀e ⟨α x, mem_map_of_mem _ x.2⟩)
  simp only [coe_Ep, coe_mul, coe_inv] at h2
  rw [h1, h2, hαe x]
  group

lemma Fp_conj (P Q : Subgroup (Sp E G₀)) (φ : P →* Q) (hφ : φ ∈ (Fp hE G₀).hom P Q)
    (β : (Sp E G₀) →* (Sp E G₀)) (hβ : β ∈ F.hom (Sp E G₀) (Sp E G₀)) :
    ∃ ψ ∈ (Fp hE G₀).hom (P.map β) (Q.map β), ∀ x : P,
      ((ψ ⟨β x, mem_map_of_mem _ x.2⟩ : Sp E G₀) : S) = (β (φ x) : S) := by
  obtain ⟨m, hm⟩ := (hR _ _ β).1 hβ
  obtain ⟨g₀, hg₀⟩ := hφ
  have hh : m * (g₀ : G) * m⁻¹ ∈ G₀ := hG₀.conj_mem _ g₀.2 m
  obtain ⟨ψ, hψ, hψe⟩ := (realizedBy_ofHom _ (Ep_inj hE G₀)).exists_mem
    (Ep_inj hE G₀) (P := P.map β) (Q := Q.map β) ⟨m * g₀ * m⁻¹, hh⟩ (by
      rintro ⟨_, x, hx, rfl⟩
      refine ⟨β (φ ⟨x, hx⟩), mem_map_of_mem _ (φ ⟨x, hx⟩).2, Subtype.ext ?_⟩
      have h1 := congrArg Subtype.val (hg₀ ⟨x, hx⟩)
      simp only [coe_Ep, coe_mul, coe_inv] at h1 ⊢
      rw [hm, hm, h1]; group)
  refine ⟨ψ, hψ, fun x => hE ?_⟩
  have h1 := congrArg Subtype.val (hψe ⟨β x, mem_map_of_mem _ x.2⟩)
  have h2 := congrArg Subtype.val (hg₀ x)
  simp only [coe_Ep, coe_mul, coe_inv] at h1 h2
  rw [h1, hm, hm, h2]; group

/-- Elements of `O^p(Aut_F(P))` are induced by `N_{G₀}(E P)`. -/
lemma oP_autF_rho (hidx : ∃ k : ℕ, G₀.index = p ^ k) (P₁ : Subgroup S) {α : F.autF P₁}
    (hα : α ∈ FusionSystem.oP p (F.autF P₁)) :
    ∃ n : normalizer ((P₁.map E : Subgroup G) : Set G), (n : G) ∈ G₀ ∧ rho hE P₁ n = α := by
  let N := normalizer ((P₁.map E : Subgroup G) : Set G)
  let ρ := rho hE P₁
  let A₀ := (G₀.subgroupOf N).map ρ
  let B := A₀.subgroupOf (F.autF P₁)
  have hBn : B.Normal := ⟨by
    intro b hb c
    rw [mem_subgroupOf] at hb ⊢
    obtain ⟨n, hn, e⟩ := hb
    have hc : (c : MulAut P₁) ∈ ρ.range := by rw [rho_range hE hr hR]; exact c.2
    obtain ⟨m, em⟩ := hc
    refine ⟨m * n * m⁻¹, ?_, ?_⟩
    · have hn' : (n : G) ∈ G₀ := hn
      show ((m * n * m⁻¹ : N) : G) ∈ G₀
      simp only [coe_mul, coe_inv]
      exact hG₀.conj_mem _ hn' _
    · simp only [map_mul, map_inv, em, e, coe_mul, coe_inv]⟩
  have hBidx : ∃ j : ℕ, B.index = p ^ j := by
    obtain ⟨k, hk⟩ := hidx
    have h1 : B.index ∣ G₀.index := by
      change A₀.relIndex (F.autF P₁) ∣ _
      rw [← rho_range hE hr hR]
      exact (relIndex_map_range_dvd ρ _).trans (relIndex_dvd_index_of_normal (H := G₀) (K := N))
    rw [hk] at h1
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 h1
    exact ⟨j, hj⟩
  have hαB : α ∈ B := by
    rw [FusionSystem.oP, mem_sInf] at hα
    exact hα B ⟨hBn, hBidx⟩
  rw [mem_subgroupOf] at hαB
  obtain ⟨n, hn, e⟩ := hαB
  exact ⟨n, hn, e⟩

lemma Fp_index (hidx : ∃ k : ℕ, G₀.index = p ^ k) : F.HasPPowerIndex p (Fp hE G₀) := by
  refine ⟨?_, fun P α hα => ?_⟩
  · rw [FusionSystem.hyp, closure_le]
    rintro y ⟨P, α, hα, s, rfl⟩
    obtain ⟨n, hn, e⟩ := oP_autF_rho hE hr hR G₀ hidx P hα
    have h1 := E_rho hE P n s
    rw [e] at h1
    show E ((s : S)⁻¹ * ((α : MulAut P) s : S)) ∈ G₀
    rw [map_mul, map_inv, h1]
    have : (E s)⁻¹ * ((n : G) * E s * (n : G)⁻¹) = ((E s)⁻¹ * n * E s) * (n : G)⁻¹ := by group
    rw [this]
    refine mul_mem ?_ (inv_mem hn)
    have := hG₀.conj_mem _ hn (E s)⁻¹
    simpa using this
  · let P₁ := P.map (Sp E G₀).subtype
    obtain ⟨n, hn, e⟩ := oP_autF_rho hE hr hR G₀ hidx P₁ hα
    obtain ⟨α₀, hα₀, hα₀e⟩ := (realizedBy_ofHom _ (Ep_inj hE G₀)).exists_mem
      (Ep_inj hE G₀) (P := P) (Q := P) ⟨n, hn⟩ (by
        intro x
        have h1 := E_rho hE P₁ n ⟨x, mem_map_of_mem _ x.2⟩
        rw [e] at h1
        obtain ⟨z, hz, ez⟩ := ((α : MulAut P₁) ⟨x, mem_map_of_mem _ x.2⟩).2
        refine ⟨z, hz, Subtype.ext ?_⟩
        simp only [coe_Ep, coe_mul, coe_inv]
        rw [← h1]
        exact congrArg E ez)
    refine ⟨α₀, hα₀, fun x => hE ?_⟩
    have h1 := congrArg Subtype.val (hα₀e x)
    simp only [coe_Ep, coe_mul, coe_inv] at h1
    rw [h1]
    have h2 := E_rho hE P₁ n ⟨x, mem_map_of_mem _ x.2⟩
    rw [e] at h2
    exact h2.symm

/-- **A reduced `F` has no proper normal subgroup of `p`-power index**: `E(S) ≤ G₀`. -/
theorem le_of_ppower_index (hred : F.Reduced p) (hidx : ∃ k : ℕ, G₀.index = p ^ k) :
    (T : Subgroup G) ≤ G₀ := by
  have hns : F.IsNormalSubsystem p (Fp hE G₀) :=
    ⟨Fp_isSubsystem hE hr hR G₀, Fp_saturated hE hr hR G₀, Fp_stronglyClosed hE hr hR G₀,
      Fp_frattini hE hr hR G₀, Fp_conj hE hr hR G₀⟩
  obtain ⟨htop, -⟩ := hred.2.2.1 _ (Fp hE G₀) hns (Fp_index hE hr hR G₀ hidx)
  intro t ht
  rw [← hr] at ht
  obtain ⟨x, rfl⟩ := ht
  have : x ∈ Sp E G₀ := htop ▸ mem_top x
  exact this

end

section Foc
variable (hE : Function.Injective E) (hr : E.range = T) (hR : RealizedBy F E)
include hE hr hR

/-- **`foc(F) = S`**: for a reduced `F` realized by `G`, `E(S) ≤ [G, G]`. -/
theorem le_commutator (hred : F.Reduced p) : (T : Subgroup G) ≤ commutator G := by
  set A := Abelianization G
  have hn : Nat.card A ≠ 0 := Nat.card_pos.ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p (Fact.out : p.Prime).ne_one
  let K : Subgroup A := (powMonoidHom m : A →* A).ker
  let G₀ : Subgroup G := K.comap Abelianization.of
  haveI : G₀.Normal := Subgroup.Normal.comap inferInstance _
  have hidx : ∃ j : ℕ, G₀.index = p ^ j := by
    rw [index_comap_of_surjective _ (QuotientGroup.mk_surjective)]
    have hpg : IsPGroup p (A ⧸ K) := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      show (x ^ p ^ k) ^ m = 1
      rw [← pow_mul, ← hkm, pow_card_eq_one']
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hpg
    exact ⟨j, by rw [index]; exact hj⟩
  have hTG₀ := le_of_ppower_index hE hr hR G₀ hred hidx
  intro t ht
  have h1 : (Abelianization.of t) ^ m = 1 := hTG₀ ht
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 T.isPGroup') ⟨t, ht⟩
  rw [orderOf_mk] at hj
  have h2 : (Abelianization.of t) ^ (p ^ j) = 1 := by
    rw [← map_pow, ← hj, pow_orderOf_eq_one, map_one]
  have hcop : Nat.Coprime (p ^ j) m :=
    Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 hm)
  have h3 : orderOf (Abelianization.of t) ∣ Nat.gcd (p ^ j) m :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h1)
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
  rw [← Abelianization.ker_of]
  exact h3

end Foc

end AndersenOliverVentura.Tame
