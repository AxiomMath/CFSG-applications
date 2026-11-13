import Mathlib
import CFSGOutside.Corpus.Defs.GoldschmidtOddCore

/-!
# Andersen–Oliver–Ventura: finite group lemmas

A Frattini-type lifting lemma for conjugations modulo a normal subgroup, and basic properties of
the odd core `O(G)`.
-/

namespace AndersenOliverVentura

open Subgroup CFSGOutside.Corpus

variable {G : Type*} [Group G]

/-- `[QN : Q] = [N : Q ∩ N]` for `N` normal. -/
lemma relIndex_sup_normal [Finite G] (Q N : Subgroup G) [N.Normal] :
    Q.relIndex (Q ⊔ N) = Q.relIndex N := by
  have h1 := relIndex_mul_relIndex (⊥ : Subgroup G) Q (Q ⊔ N) bot_le le_sup_left
  have h2 := relIndex_mul_relIndex (⊥ : Subgroup G) N (Q ⊔ N) bot_le le_sup_right
  have h3 := relIndex_mul_relIndex (⊥ : Subgroup G) (N ⊓ Q) Q bot_le inf_le_right
  have h4 := relIndex_mul_relIndex (⊥ : Subgroup G) (Q ⊓ N) N bot_le inf_le_right
  rw [relIndex_sup_right] at h2
  rw [inf_relIndex_right] at h3 h4
  simp only [relIndex_bot_left] at h1 h2 h3 h4
  rw [inf_comm] at h3
  have hc : 0 < Nat.card (Q ⊓ N : Subgroup G) := Nat.card_pos
  have ha : 0 < N.relIndex Q := Nat.pos_of_ne_zero fun h => by
    rw [h, mul_zero] at h3; exact (Nat.card_pos (α := Q)).ne' h3.symm
  rw [← h4] at h2
  have : Nat.card (Q ⊓ N : Subgroup G) * N.relIndex Q * Q.relIndex (Q ⊔ N) =
      Nat.card (Q ⊓ N : Subgroup G) * N.relIndex Q * Q.relIndex N := by
    rw [h3, h1, ← h2, ← h3]; ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hc ha) this

/-- If `R` and `Q` are `p`-subgroups with `R ≤ QN`, `N ⊴ G` and `p ∤ [N : Q ∩ N]`, then some
`n ∈ N` conjugates `R` into `Q`. -/
lemma exists_conj_le_of_le_sup [Finite G] {p : ℕ} [Fact p.Prime] {N : Subgroup G} [N.Normal]
    {Q R : Subgroup G} (hQ : IsPGroup p Q) (hR : IsPGroup p R) (hidx : ¬ p ∣ Q.relIndex N)
    (hRQ : R ≤ Q ⊔ N) : ∃ n ∈ N, ∀ r ∈ R, n⁻¹ * r * n ∈ Q := by
  set K := Q ⊔ N with hK
  have hidxK : ¬ p ∣ (Q.subgroupOf K).index := by
    change ¬ p ∣ Q.relIndex K
    rw [hK, relIndex_sup_normal]; exact hidx
  let P₀ : Sylow p K := (hQ.comap_subtype (K := K)).toSylow hidxK
  obtain ⟨P₁, hP₁⟩ := (hR.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K P₀ P₁
  have hkmem : ((k : G)) ∈ ((N ⊔ Q : Subgroup G) : Set G) := by rw [sup_comm]; exact k.2
  rw [normal_mul] at hkmem
  obtain ⟨n, hn, q, hq, hnq⟩ := hkmem
  refine ⟨n, hn, fun r hr => ?_⟩
  have h1 : (⟨r, hRQ hr⟩ : K) ∈ (P₁ : Subgroup K) := hP₁ (mem_subgroupOf.2 hr)
  rw [← hk, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at h1
  have h2 : (k : G)⁻¹ * r * k ∈ Q := by
    have := mem_subgroupOf.1 (show _ ∈ Q.subgroupOf K from h1)
    simpa [MulAut.smul_def] using this
  rw [← hnq] at h2
  have h3 : n⁻¹ * r * n = q * ((n * q)⁻¹ * r * (n * q)) * q⁻¹ := by group
  rw [h3]
  exact mul_mem (mul_mem hq h2) (inv_mem hq)

/-- A conjugation that carries the `p`-subgroup `R` into `Q` modulo `N` agrees modulo `N` with one
that carries `R` into `Q`, when `p ∤ [N : Q ∩ N]`. -/
lemma exists_lift [Finite G] {p : ℕ} [Fact p.Prime] (N : Subgroup G) [N.Normal]
    {Q R : Subgroup G} (hQ : IsPGroup p Q) (hR : IsPGroup p R) (hidx : ¬ p ∣ Q.relIndex N)
    (g : G) (h : ∀ r ∈ R, ∃ q ∈ Q, (QuotientGroup.mk (g * r * g⁻¹) : G ⧸ N) = QuotientGroup.mk q) :
    ∃ g' : G, (QuotientGroup.mk g' : G ⧸ N) = QuotientGroup.mk g ∧ ∀ r ∈ R, g' * r * g'⁻¹ ∈ Q := by
  let R' := R.map (MulAut.conj g).toMonoidHom
  have hR' : IsPGroup p R' := hR.map _
  have hle : R' ≤ Q ⊔ N := by
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨q, hq, hqe⟩ := h r hr
    have hn : q⁻¹ * (g * r * g⁻¹) ∈ N := QuotientGroup.eq.1 hqe.symm
    have : (MulAut.conj g).toMonoidHom r = q * (q⁻¹ * (g * r * g⁻¹)) := by simp
    rw [this]; exact mul_mem_sup hq hn
  obtain ⟨n, hn, hnR⟩ := exists_conj_le_of_le_sup hQ hR' hidx hle
  refine ⟨n⁻¹ * g, ?_, fun r hr => ?_⟩
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, (QuotientGroup.eq_one_iff n).2 hn, inv_one,
      one_mul]
  · have := hnR _ ⟨r, hr, rfl⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply] at this
    convert this using 1; group

lemma odd_card_goldschmidtOddCore [Finite G] : Odd (Nat.card (goldschmidtOddCore G)) := by
  let s : Set (Subgroup G) := {N | N.Normal ∧ Odd (Nat.card N)}
  have hs : SupClosed s := by
    rintro M ⟨hM, hMo⟩ N ⟨hN, hNo⟩
    refine ⟨Subgroup.sup_normal M N, ?_⟩
    have h := relIndex_mul_relIndex (⊥ : Subgroup G) N (M ⊔ N) bot_le le_sup_right
    rw [relIndex_sup_right] at h
    simp only [relIndex_bot_left] at h
    rw [← h]
    exact Nat.odd_mul.2 ⟨hNo, Odd.of_dvd_nat hMo (relIndex_dvd_card _ _)⟩
  have hbot : (⊥ : Subgroup G) ∈ s := ⟨inferInstance, by simp⟩
  exact (hs.sSup_mem (Set.toFinite s) hbot le_rfl).2

lemma inf_goldschmidtOddCore_eq_bot [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P) :
    P ⊓ goldschmidtOddCore G = ⊥ := by
  apply inf_eq_bot_of_coprime
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 odd_card_goldschmidtOddCore)

lemma goldschmidtOddCore_quotient_eq_bot [Finite G] :
    goldschmidtOddCore (G ⧸ goldschmidtOddCore G) = ⊥ := by
  rw [eq_bot_iff]
  apply sSup_le
  rintro M ⟨hMn, hMo⟩
  let L : Subgroup G := M.comap (QuotientGroup.mk' (goldschmidtOddCore G))
  have hL : L.Normal := hMn.comap _
  have hcard : Nat.card L = Nat.card (goldschmidtOddCore G) * Nat.card M :=
    QuotientGroup.card_preimage_mk (goldschmidtOddCore G) (M : Set (G ⧸ goldschmidtOddCore G))
  have hLo : Odd (Nat.card L) := by rw [hcard]; exact Nat.odd_mul.2 ⟨odd_card_goldschmidtOddCore, hMo⟩
  have hLle : L ≤ goldschmidtOddCore G := le_sSup ⟨hL, hLo⟩
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  rw [mem_bot, QuotientGroup.eq_one_iff]
  exact hLle hy

end AndersenOliverVentura
