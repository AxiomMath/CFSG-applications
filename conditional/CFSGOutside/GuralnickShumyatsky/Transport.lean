import CFSGOutside.GuralnickShumyatsky.Coprime

/-!
# Transport of the setting along injective homomorphisms and to subgroups
-/

namespace CFSGOutside.GuralnickShumyatsky

open Subgroup

variable {X : Type*} [Group X] {Z : Type*} [Group Z]

theorem map_cen_of_injective (f : X →* Z) (hf : Function.Injective f) (H : Subgroup X) (a : X) :
    (cen H a).map f = cen (H.map f) (f a) := by
  ext z
  simp only [cen, mem_map, mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨x, ⟨hxH, hxc⟩, rfl⟩
    exact ⟨⟨x, hxH, rfl⟩, by rw [← map_mul, ← map_mul, hxc]⟩
  · rintro ⟨⟨x, hxH, rfl⟩, hc⟩
    refine ⟨x, ⟨hxH, ?_⟩, rfl⟩
    apply hf
    simpa only [map_mul] using hc

theorem map_gens_of_injective (f : X →* Z) (hf : Function.Injective f) (P G A : Subgroup X) :
    (gens P G A).map f = gens (P.map f) (G.map f) (A.map f) := by
  simp only [gens, Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
    have hfa : f a ≠ 1 := fun h => ha1 (hf (h.trans (map_one f).symm))
    rw [map_inf_eq _ _ f hf, map_commutator, map_cen_of_injective f hf]
    exact le_iSup_of_le (f a) (le_iSup_of_le ⟨a, ha, rfl⟩ (le_iSup_of_le hfa le_rfl))
  · refine iSup_le fun z => iSup_le fun hz => iSup_le fun hz1 => ?_
    obtain ⟨a, ha, rfl⟩ := hz
    have ha1 : a ≠ 1 := fun h => hz1 (by rw [h, map_one])
    rw [← map_cen_of_injective f hf, ← map_commutator, ← map_inf_eq _ _ f hf]
    exact le_iSup_of_le a (le_iSup_of_le ha (le_iSup_of_le ha1 le_rfl))

theorem CopAct.map {q : ℕ} {G A : Subgroup X} (h : CopAct q G A) (f : X →* Z)
    (hf : Function.Injective f) : CopAct q (G.map f) (A.map f) where
  prime := h.prime
  norm := (map_mono h.norm).trans (le_normalizer_map f)
  coprime := by rw [card_map_of_injective hf]; exact h.coprime
  comm := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, h.comm a ha b hb]
  exp := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, h.exp a ha, map_one]

theorem card_subgroupOf_of_le {H K : Subgroup X} (h : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H :=
  Nat.card_congr (subgroupOfEquivOfLe h).toEquiv

theorem CopAct.subgroupOf {q : ℕ} {G A K : Subgroup X} (h : CopAct q G A) (hGK : G ≤ K)
    (hAK : A ≤ K) : CopAct q (G.subgroupOf K) (A.subgroupOf K) where
  prime := h.prime
  norm := by
    rw [← subgroupOf_normalizer_eq hGK]
    exact subgroupOf_mono K h.norm
  coprime := by rw [card_subgroupOf_of_le hGK]; exact h.coprime
  comm := by
    intro a ha b hb
    exact Subtype.ext (h.comm a (mem_subgroupOf.mp ha) b (mem_subgroupOf.mp hb))
  exp := by
    intro a ha
    exact Subtype.ext (by simpa using h.exp a (mem_subgroupOf.mp ha))

theorem isSylowOf_subgroupOf [Finite X] {p : ℕ} [Fact p.Prime] {P G K : Subgroup X}
    (h : IsSylowOf p P G) (hGK : G ≤ K) : IsSylowOf p (P.subgroupOf K) (G.subgroupOf K) := by
  rw [isSylowOf_iff] at h ⊢
  obtain ⟨hPG, hPp, hidx⟩ := h
  refine ⟨subgroupOf_mono K hPG, hPp.comap_subtype, ?_⟩
  rwa [relIndex_subgroupOf hGK]

theorem le_normalizer_subgroupOf {A P K : Subgroup X} (hAP : A ≤ normalizer (P : Set X))
    (hPK : P ≤ K) : A.subgroupOf K ≤ normalizer ((P.subgroupOf K : Subgroup K) : Set K) := by
  rw [← subgroupOf_normalizer_eq hPK]
  exact subgroupOf_mono K hAP

end CFSGOutside.GuralnickShumyatsky
