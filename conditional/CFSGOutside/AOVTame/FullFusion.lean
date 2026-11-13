import CFSGOutside.AOVTame.Saturation
import CFSGOutside.AOVTame.OfHom

/-!
# AOV tameness: a reduced fusion system is realized by any normal subgroup of index prime to `p`

If a reduced `F` is realized by `E : S → G` with `E(S) ∈ Syl_p(G)`, and `G₀ ⊴ G` contains `E(S)`
and has index prime to `p`, then `F_{E(S)}(G₀)` is a saturated normal subsystem of `F` of index
prime to `p`, so it is all of `F`: every morphism of `F` is conjugation by an element of `G₀`.
-/

namespace AndersenOliverVentura.Tame

open Subgroup

variable {S : Type*} [Group S] [Finite S] {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
  {F : FusionSystem S} {T : Sylow p G} {E : S →* G}

section
variable (hE : Function.Injective E) (hr : E.range = T) (hR : RealizedBy F E)
  {G₀ : Subgroup G} [hG₀ : G₀.Normal] (hTG₀ : (T : Subgroup G) ≤ G₀)
include hE hr hR hTG₀

/-- `E` restricted to `S₀ = S` and corestricted to `G₀`. -/
def E₀ : (⊤ : Subgroup S) →* G₀ :=
  (E.comp (⊤ : Subgroup S).subtype).codRestrict G₀ (fun x => hTG₀ (mem_T hE hr hR x))

omit hG₀ in
lemma E₀_inj : Function.Injective (E₀ hE hr hR hTG₀) := fun x y h =>
  Subtype.ext (hE (congrArg Subtype.val h))

omit hG₀ in
@[simp] lemma coe_E₀ (x : (⊤ : Subgroup S)) : (E₀ hE hr hR hTG₀ x : G) = E x := rfl

/-- The subsystem `F_S(G₀)` over `S₀ = S`. -/
def F₀ : FusionSystem (⊤ : Subgroup S) := ofHom (E₀ hE hr hR hTG₀) (E₀_inj hE hr hR hTG₀)

omit hG₀ in
lemma F₀_isSubsystem : F.IsSubsystem (F₀ hE hr hR hTG₀) := by
  rintro P Q φ ⟨g₀, hg₀⟩
  obtain ⟨ψ, hψ, hψe⟩ := hR.exists_mem hE (P := P.map (⊤ : Subgroup S).subtype)
    (Q := Q.map (⊤ : Subgroup S).subtype) (g₀ : G) (by
      rintro ⟨_, x, hx, rfl⟩
      have h := congrArg Subtype.val (hg₀ ⟨x, hx⟩)
      simp only [coe_E₀, coe_mul, coe_inv] at h
      exact ⟨((φ ⟨x, hx⟩ : (⊤ : Subgroup S)) : S), mem_map_of_mem _ (φ ⟨x, hx⟩).2, h⟩)
  refine ⟨ψ, hψ, fun x => hE ?_⟩
  rw [hψe]
  have h := congrArg Subtype.val (hg₀ x)
  simp only [coe_E₀, coe_mul, coe_inv] at h
  exact h.symm

omit hG₀ in
lemma F₀_saturated : (F₀ hE hr hR hTG₀).Saturated p := by
  refine saturated (T := T.subtype hTG₀) (E₀_inj hE hr hR hTG₀) ?_ (realizedBy_ofHom _ _)
  rw [Sylow.coe_subtype]
  ext ⟨y, hy⟩
  constructor
  · rintro ⟨x, e⟩
    rw [mem_subgroupOf]
    have := congrArg Subtype.val e
    simp only [coe_E₀] at this
    exact this ▸ mem_T hE hr hR x
  · intro h
    rw [mem_subgroupOf] at h
    obtain ⟨x, e⟩ : y ∈ E.range := hr ▸ h
    exact ⟨⟨x, mem_top x⟩, Subtype.ext e⟩

lemma F₀_frattini (P Q : Subgroup (⊤ : Subgroup S))
    (φ : P.map (⊤ : Subgroup S).subtype →* Q.map (⊤ : Subgroup S).subtype)
    (hφ : φ ∈ F.hom (P.map (⊤ : Subgroup S).subtype) (Q.map (⊤ : Subgroup S).subtype)) :
    ∃ α ∈ F.hom (⊤ : Subgroup S) ⊤, ∃ φ₀ ∈ (F₀ hE hr hR hTG₀).hom (P.map α) Q, ∀ x : P,
      (φ ⟨(x : (⊤ : Subgroup S)), mem_map_of_mem _ x.2⟩ : S) =
        ((φ₀ ⟨α x, mem_map_of_mem _ x.2⟩ : (⊤ : Subgroup S)) : S) := by
  obtain ⟨g, hg⟩ := (hR _ _ φ).1 hφ
  have htop := Sylow.normalizer_sup_eq_top' T hTG₀
  have hgt : g ∈ (⊤ : Subgroup G) := mem_top g
  rw [← htop, ← SetLike.mem_coe, mul_normal] at hgt
  obtain ⟨n, hn, g₀, hg₀, rfl⟩ := hgt
  have hnT : ∀ x : S, n * E x * n⁻¹ ∈ (T : Subgroup G) := fun x =>
    (mem_normalizer_iff.1 hn (E x)).1 (mem_T hE hr hR x)
  obtain ⟨α, hα, hαe⟩ := hR.exists_mem hE (P := ⊤) (Q := ⊤) n (fun x => by
    have : n * E x * n⁻¹ ∈ E.range := hr ▸ hnT x
    obtain ⟨y, hy⟩ := this
    exact ⟨y, mem_top y, hy⟩)
  have hh : n * g₀ * n⁻¹ ∈ G₀ := hG₀.conj_mem g₀ hg₀ n
  obtain ⟨φ₀, hφ₀, hφ₀e⟩ := (realizedBy_ofHom _ (E₀_inj hE hr hR hTG₀)).exists_mem
    (E₀_inj hE hr hR hTG₀) (P := P.map α) (Q := Q) ⟨n * g₀ * n⁻¹, hh⟩ (by
      rintro ⟨_, x, hx, rfl⟩
      have h1 := hg ⟨x, mem_map_of_mem _ hx⟩
      obtain ⟨z, hz, ez⟩ := (φ ⟨x, mem_map_of_mem _ hx⟩).2
      refine ⟨z, hz, Subtype.ext ?_⟩
      simp only [coe_E₀, coe_mul, coe_inv]
      rw [hαe x]
      have : E (z : S) = n * g₀ * E (x : S) * (n * g₀)⁻¹ := by
        rw [← h1]; exact congrArg E ez
      rw [this]; group)
  refine ⟨α, hα, φ₀, hφ₀, fun x => hE ?_⟩
  have h1 := hg ⟨x, mem_map_of_mem _ x.2⟩
  have h2 := congrArg Subtype.val (hφ₀e ⟨α x, mem_map_of_mem _ x.2⟩)
  simp only [coe_E₀, coe_mul, coe_inv] at h2
  rw [h1, h2, hαe x]
  group

lemma F₀_conj (P Q : Subgroup (⊤ : Subgroup S)) (φ : P →* Q) (hφ : φ ∈ (F₀ hE hr hR hTG₀).hom P Q)
    (β : (⊤ : Subgroup S) →* (⊤ : Subgroup S)) (hβ : β ∈ F.hom (⊤ : Subgroup S) ⊤) :
    ∃ ψ ∈ (F₀ hE hr hR hTG₀).hom (P.map β) (Q.map β), ∀ x : P,
      ((ψ ⟨β x, mem_map_of_mem _ x.2⟩ : (⊤ : Subgroup S)) : S) = (β (φ x) : S) := by
  obtain ⟨m, hm⟩ := (hR _ _ β).1 hβ
  obtain ⟨g₀, hg₀⟩ := hφ
  have hh : m * (g₀ : G) * m⁻¹ ∈ G₀ := hG₀.conj_mem _ g₀.2 m
  obtain ⟨ψ, hψ, hψe⟩ := (realizedBy_ofHom _ (E₀_inj hE hr hR hTG₀)).exists_mem
    (E₀_inj hE hr hR hTG₀) (P := P.map β) (Q := Q.map β) ⟨m * g₀ * m⁻¹, hh⟩ (by
      rintro ⟨_, x, hx, rfl⟩
      refine ⟨β (φ ⟨x, hx⟩), mem_map_of_mem _ (φ ⟨x, hx⟩).2, Subtype.ext ?_⟩
      have h1 := congrArg Subtype.val (hg₀ ⟨x, hx⟩)
      simp only [coe_E₀, coe_mul, coe_inv] at h1 ⊢
      rw [hm, hm, h1]; group)
  refine ⟨ψ, hψ, fun x => hE ?_⟩
  have h1 := congrArg Subtype.val (hψe ⟨β x, mem_map_of_mem _ x.2⟩)
  have h2 := congrArg Subtype.val (hg₀ x)
  simp only [coe_E₀, coe_mul, coe_inv] at h1 h2
  rw [h1, hm, hm, h2]; group

lemma F₀_index (hidx : ¬ p ∣ G₀.index) : F.HasIndexPrimeTo p (F₀ hE hr hR hTG₀) := by
  refine ⟨rfl, fun P α hα => ?_⟩
  let P₁ := P.map (⊤ : Subgroup S).subtype
  let N := normalizer ((P₁.map E : Subgroup G) : Set G)
  let ρ := rho hE P₁
  let A₀ := (G₀.subgroupOf N).map ρ
  have hA₀ : A₀ ≤ F.autF P₁ := by rw [← rho_range hE hr hR]; exact map_le_range _ _
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
  have hBidx : Nat.Coprime B.index p := by
    have h1 : B.index ∣ G₀.index := by
      change A₀.relIndex (F.autF P₁) ∣ _
      rw [← rho_range hE hr hR]
      exact (relIndex_map_range_dvd ρ _).trans (relIndex_dvd_index_of_normal (H := G₀) (K := N))
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)]
    exact fun h => hidx (h.trans h1)
  have hαB : α ∈ B := by
    rw [FusionSystem.oP', mem_sInf] at hα
    exact hα B ⟨hBn, hBidx⟩
  rw [mem_subgroupOf] at hαB
  obtain ⟨n, hn, e⟩ := hαB
  have hn' : (n : G) ∈ G₀ := hn
  obtain ⟨α₀, hα₀, hα₀e⟩ := (realizedBy_ofHom _ (E₀_inj hE hr hR hTG₀)).exists_mem
    (E₀_inj hE hr hR hTG₀) (P := P) (Q := P) ⟨n, hn'⟩ (by
      intro x
      have h1 := E_rho hE P₁ n ⟨x, mem_map_of_mem _ x.2⟩
      rw [e] at h1
      obtain ⟨z, hz, ez⟩ := ((α : MulAut P₁) ⟨x, mem_map_of_mem _ x.2⟩).2
      refine ⟨z, hz, Subtype.ext ?_⟩
      simp only [coe_E₀, coe_mul, coe_inv]
      rw [← h1]
      exact congrArg E ez)
  refine ⟨α₀, hα₀, fun x => hE ?_⟩
  have h1 := congrArg Subtype.val (hα₀e x)
  simp only [coe_E₀, coe_mul, coe_inv] at h1
  rw [h1]
  have h2 := E_rho hE P₁ n ⟨x, mem_map_of_mem _ x.2⟩
  rw [e] at h2
  exact h2.symm

/-- Every morphism of a reduced `F` realized by `G` is conjugation by an element of `G₀`. -/
theorem realized_by_normal (hred : F.Reduced p) (hidx : ¬ p ∣ G₀.index) (P Q : Subgroup S)
    (φ : P →* Q) (hφ : φ ∈ F.hom P Q) : ∃ g ∈ G₀, ∀ x : P, E (φ x) = g * E x * g⁻¹ := by
  have hns : F.IsNormalSubsystem p (F₀ hE hr hR hTG₀) :=
    ⟨F₀_isSubsystem hE hr hR hTG₀, F₀_saturated hE hr hR hTG₀, fun _ _ y _ => mem_top y,
      F₀_frattini hE hr hR hTG₀, F₀_conj hE hr hR hTG₀⟩
  obtain ⟨-, hw⟩ := hred.2.2.2 ⊤ (F₀ hE hr hR hTG₀) hns (F₀_index hE hr hR hTG₀ hidx)
  let P' := P.comap (⊤ : Subgroup S).subtype
  let Q' := Q.comap (⊤ : Subgroup S).subtype
  have hP' : P'.map (⊤ : Subgroup S).subtype ≤ P := map_comap_le _ _
  have hQ' : ∀ q ∈ Q, q ∈ Q'.map (⊤ : Subgroup S).subtype := fun q hq => ⟨⟨q, mem_top q⟩, hq, rfl⟩
  let φ' : P'.map (⊤ : Subgroup S).subtype →* Q'.map (⊤ : Subgroup S).subtype :=
    ((Q.subtype.comp φ).comp (inclusion hP')).codRestrict _ (fun x => hQ' _ (φ _).2)
  have hφ' : φ' ∈ F.hom _ _ := F.mem_of_eq_on hφ hP' φ' (fun x => rfl)
  obtain ⟨φ₀, ⟨g₀, hg₀⟩, hφ₀⟩ := hw P' Q' φ' hφ'
  refine ⟨g₀, g₀.2, fun x => ?_⟩
  let x' : P' := ⟨⟨x, mem_top _⟩, x.2⟩
  have h1 := hφ₀ x'
  have h2 := congrArg Subtype.val (hg₀ x')
  simp only [coe_E₀, coe_mul, coe_inv] at h2
  have h3 : (φ' ⟨(x' : (⊤ : Subgroup S)), mem_map_of_mem _ x'.2⟩ : S) = φ x := rfl
  rw [← h3, ← h1, h2]

end

end AndersenOliverVentura.Tame
