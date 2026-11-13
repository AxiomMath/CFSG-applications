import CFSGOutside.AndersenOliverVentura.Basic
import CFSGOutside.AndersenOliverVentura.GroupLemmas

/-!
# Andersen–Oliver–Ventura: realizing over `G/O(G)`

If `E : S → G` realizes `F` with `E(S)` a Sylow 2-subgroup, then so does `S → G/O(G)`
(the realizability part of the reduction to `O_{2'}(G) = 1` that the proof of AOV Theorem 3.8
makes via Lemma 2.19).
-/

namespace AndersenOliverVentura

open Subgroup CFSGOutside.Corpus

universe u

variable {S : Type u} [Group S]

lemma realizedBy_quotient_oddCore {F : FusionSystem S} (hS : IsPGroup 2 S)
    {G : Type} [Group G] [Finite G] (T : Sylow 2 G) {E : S →* G} (hE : Function.Injective E)
    (hrange : E.range = T) (hR : RealizedBy F E) :
    ∃ T' : Sylow 2 (G ⧸ goldschmidtOddCore G),
      Function.Injective ((QuotientGroup.mk' (goldschmidtOddCore G)).comp E) ∧
      ((QuotientGroup.mk' (goldschmidtOddCore G)).comp E).range = T' ∧
      RealizedBy F ((QuotientGroup.mk' (goldschmidtOddCore G)).comp E) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := goldschmidtOddCore G
  set π := QuotientGroup.mk' N
  have hT : (T : Subgroup G) ⊓ N = ⊥ := inf_goldschmidtOddCore_eq_bot T.isPGroup'
  have hEN : ∀ x, π (E x) = 1 → E x = 1 := by
    intro x hx
    have h1 : E x ∈ N := (QuotientGroup.eq_one_iff _).1 hx
    have h2 : E x ∈ (T : Subgroup G) := by rw [← hrange]; exact ⟨x, rfl⟩
    have : E x ∈ (T : Subgroup G) ⊓ N := ⟨h2, h1⟩
    rwa [hT, mem_bot] at this
  have hinj : Function.Injective (π.comp E) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact (injective_iff_map_eq_one E).1 hE x (hEN x hx)
  refine ⟨T.mapSurjective (QuotientGroup.mk'_surjective N), hinj, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hrange, Sylow.coe_mapSurjective]
  · intro P Q φ
    constructor
    · intro hφ
      obtain ⟨g, hg⟩ := (hR P Q φ).1 hφ
      exact ⟨π g, fun x => by simp only [MonoidHom.comp_apply, hg, map_mul, map_inv]⟩
    · rintro ⟨gbar, hg⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N gbar
      have hQ : IsPGroup 2 (Q.map E) := (hS.to_subgroup Q).map E
      have hP : IsPGroup 2 (P.map E) := (hS.to_subgroup P).map E
      have hidx : ¬ 2 ∣ (Q.map E).relIndex N := by
        have hb : Q.map E ⊓ N = ⊥ := by
          apply eq_bot_iff.2
          intro y hy
          have : y ∈ (T : Subgroup G) ⊓ N := ⟨by
            obtain ⟨x, -, rfl⟩ := hy.1; rw [← hrange]; exact ⟨x, rfl⟩, hy.2⟩
          rwa [hT] at this
        rw [← inf_relIndex_right, hb, relIndex_bot_left]
        exact (odd_card_goldschmidtOddCore (G := G)).not_two_dvd_nat
      obtain ⟨g', hg', hconj⟩ := exists_lift N hQ hP hidx g (by
        rintro _ ⟨x, hx, rfl⟩
        refine ⟨E (φ ⟨x, hx⟩), mem_map_of_mem _ (φ ⟨x, hx⟩).2, ?_⟩
        have := hg ⟨x, hx⟩
        simp only [MonoidHom.comp_apply] at this
        show π (g * E x * g⁻¹) = π (E _)
        rw [this]; simp only [map_mul, map_inv]; rfl)
      obtain ⟨φ', hφ', hφ'e⟩ := hR.exists_mem hE g' (fun x => hconj _ (mem_map_of_mem _ x.2))
      have heq : φ' = φ := by
        apply MonoidHom.ext; intro x; apply Subtype.ext
        apply hinj
        simp only [MonoidHom.comp_apply]
        rw [hφ'e]
        have := hg x
        simp only [MonoidHom.comp_apply] at this
        rw [this]
        show (π (g' * E x * g'⁻¹)) = π g * π (E x) * (π g)⁻¹
        simp only [map_mul, map_inv]
        rw [show π g' = π g from hg']
      rw [← heq]; exact hφ'
