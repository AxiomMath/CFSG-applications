import CFSGOutside.AOVTame.Linking
import CFSGOutside.AOVTame.Burnside

/-!
# AOV tameness: centralizers of centric subgroups

For `S ∈ Syl_p(G)` and `P ≤ S` centric, `Z(P)` is a central Sylow `p`-subgroup of `C_G(P)`, so
`C_G(P) = O^p(C_G(P)) · Z(P)` with `O^p(C_G(P))` of order prime to `p`.
-/

namespace AndersenOliverVentura.Tame

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

lemma conjSub_le_iff {g : G} {P S : Subgroup G} :
    conjSub g P ≤ S ↔ ∀ x ∈ P, g * x * g⁻¹ ∈ S :=
  ⟨fun h x hx => h ⟨x, hx, rfl⟩, fun h _ ⟨x, hx, e⟩ => e ▸ h x hx⟩

/-- `Z(P) = P ∩ C_G(P)` is a Sylow `p`-subgroup of `C_G(P)` when `P` is centric. -/
lemma isSylow_center_of_centric (S : Sylow p G) {P : Subgroup G} (hP : IsCentric (S : Subgroup G) P) :
    ∀ R : Subgroup (centralizer (P : Set G)), IsPGroup p R →
      ((P ⊓ centralizer (P : Set G)).subgroupOf (centralizer (P : Set G))) ≤ R →
      R = (P ⊓ centralizer (P : Set G)).subgroupOf (centralizer (P : Set G)) := by
  intro R hR hle
  apply le_antisymm _ hle
  set R' : Subgroup G := R.map (centralizer (P : Set G)).subtype
  have hR' : IsPGroup p R' := hR.map _
  have hPp : IsPGroup p P := S.isPGroup'.to_le hP.1
  have hRP : R' ≤ centralizer (P : Set G) := map_subtype_le R
  have hpg : IsPGroup p (P ⊔ R' : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hPp hR' (fun x hx => by
      rw [mem_normalizer_iff]
      intro y
      have key : ∀ w ∈ centralizer (P : Set G), x * w * x⁻¹ = w := fun w hw => by
        have h := mem_centralizer_iff.1 hw x hx
        calc x * w * x⁻¹ = (x * w) * x⁻¹ := rfl
          _ = (w * x) * x⁻¹ := by rw [h]
          _ = w := by group
      constructor
      · intro hy; rw [key y (hRP hy)]; exact hy
      · intro hy
        have h := mem_centralizer_iff.1 (hRP hy) x hx
        have : x * y * x⁻¹ = y := by
          calc x * y * x⁻¹ = x⁻¹ * (x * (x * y * x⁻¹)) := by group
            _ = x⁻¹ * ((x * y * x⁻¹) * x) := by rw [h]
            _ = y := by group
        rwa [this] at hy)
  obtain ⟨S', hS'⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S' S
  have hconj : ∀ x ∈ (S' : Subgroup G), g * x * g⁻¹ ∈ (S : Subgroup G) := by
    intro x hx
    rw [← hg, Sylow.coe_subgroup_smul]
    exact ⟨x, hx, rfl⟩
  have hgP : conjSub g P ≤ S := conjSub_le_iff.2 fun x hx => hconj x (hS' (mem_sup_left hx))
  have hc := hP.2 g hgP
  intro r hr
  show (r : G) ∈ P ⊓ centralizer (P : Set G)
  have hrR : (r : G) ∈ R' := ⟨r, hr, rfl⟩
  have hcen : g * r * g⁻¹ ∈ centralizer (conjSub g P : Set G) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have := mem_centralizer_iff.1 r.2 x hx
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
    calc g * x * g⁻¹ * (g * r * g⁻¹) = g * (x * r) * g⁻¹ := by group
      _ = g * (r * x) * g⁻¹ := by rw [this]
      _ = g * r * g⁻¹ * (g * x * g⁻¹) := by group
  have h1 : g * r * g⁻¹ ∈ centralizer (conjSub g P : Set G) ⊓ (S : Subgroup G) :=
    mem_inf.2 ⟨hcen, hconj _ (hS' (mem_sup_right hrR))⟩
  rw [hc] at h1
  refine ⟨?_, r.2⟩
  have := mem_conjSub.1 h1.1
  simpa [mul_assoc] using this

/-- For centric `P`: `C_G(P) = O^p(C_G(P)) · Z(P)` and `p ∤ |O^p(C_G(P))|`. -/
lemma centralizer_decomp (S : Sylow p G) {P : Subgroup G} (hP : IsCentric (S : Subgroup G) P) :
    (∀ c ∈ centralizer (P : Set G), ∃ k ∈ opCent p P, ∃ z ∈ P ⊓ centralizer (P : Set G), c = k * z) ∧
      ¬ p ∣ Nat.card (opCent p P) := by
  set C := centralizer (P : Set G)
  let Z : Sylow p C :=
    { toSubgroup := (P ⊓ C).subgroupOf C
      isPGroup' := (S.isPGroup'.to_le (inf_le_left.trans hP.1)).comap_subtype
      is_maximal' := fun {R} hR hle => isSylow_center_of_centric S hP R hR hle }
  have hZ : (Z : Subgroup C) ≤ center C := by
    intro z hz
    rw [mem_center_iff]
    intro c
    apply Subtype.ext
    have h1 := mem_centralizer_iff.1 c.2 _ (mem_subgroupOf.1 hz).1
    simpa using h1.symm
  obtain ⟨h1, h2⟩ := oP_complement Z hZ
  refine ⟨fun c hc => ?_, ?_⟩
  · obtain ⟨k, hk, z, hz, e⟩ := h1 ⟨c, hc⟩
    refine ⟨k, ⟨k, hk, rfl⟩, z, mem_subgroupOf.1 hz, ?_⟩
    have := congrArg Subtype.val e
    simpa using this
  · have : Nat.card (opCent p P) = Nat.card (FusionSystem.oP p C) :=
      Nat.card_congr (equivMapOfInjective _ _ C.subtype_injective).toEquiv.symm
    rw [this]; exact h2

/-- A `p`-element of `O^p(C_G(R))`, for `R` centric, is trivial. -/
lemma eq_one_of_mem_opCent {G : Type*} [Group G] [Finite G] (S : Sylow p G) {R : Subgroup G}
    (hR : IsCentric (S : Subgroup G) R) {x : G} (hx : x ∈ opCent p R) (hxS : x ∈ (S : Subgroup G)) :
    x = 1 := by
  have hcop := (centralizer_decomp S hR).2
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.1 S.isPGroup') ⟨x, hxS⟩
  rw [orderOf_mk] at hn
  have hd : orderOf x ∣ Nat.card (opCent p R) := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : opCent p R)
    rwa [orderOf_mk] at this
  rcases n with _ | n
  · rw [pow_zero, orderOf_eq_one_iff] at hn; exact hn
  · exact absurd ((dvd_pow_self p n.succ_ne_zero).trans (hn ▸ hd)) hcop

end AndersenOliverVentura.Tame
