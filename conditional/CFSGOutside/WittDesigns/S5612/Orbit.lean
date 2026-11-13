import Mathlib
import CFSGOutside.Corpus.SubgroupCardClassificationOfCardLeEighty
import CFSGOutside.WittDesigns.S5612.Search
import CFSGOutside.WittDesigns.AutS5612.Main

/-!
# Counting the Steiner systems that contain a fixed hexad

The stabilizer of a block in `Aut S(5,6,12) = M12` has order `95040 / 132 = 720`, so the orbit of the
hexad system under the stabilizer of a 6-set (of order `6! 6! = 518400`) has `720` elements.  The
exhaustive search shows that at most `720` Steiner systems contain the hexad, hence all of them
lie in that orbit.
-/

namespace CFSGOutside.WittDesigns.Witt5612

open Pointwise Equiv Equiv.Perm MulAction

open CFSGOutside.Corpus

variable [SubgroupCardClassificationOfCardLeEighty]

theorem orb_mul (G : Type*) {X : Type*} [Group G] [MulAction G X] (x : X) :
    (orbit G x).ncard * Nat.card (stabilizer G x) = Nat.card G := by
  rw [mul_comm, ← MulAction.index_stabilizer]
  exact Subgroup.card_mul_index _

theorem exists_perm_smul_eq {A A' : Finset (Fin 12)} (h : A.card = A'.card) :
    ∃ σ : Perm (Fin 12), σ • A = A' := by
  classical
  let e := Finset.equivOfCardEq h
  refine ⟨Equiv.extendSubtype (p := (· ∈ A)) (q := (· ∈ A')) e, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_smul_finset.1 hy
    exact Equiv.extendSubtype_mem e x hx
  · rw [Finset.card_smul_finset, h]

theorem smul_steiner {𝒮 : Finset (Finset (Fin 12))} (h : IsSteiner56 𝒮) (σ : Perm (Fin 12)) :
    IsSteiner56 (σ • 𝒮) := by
  refine ⟨?_, ?_⟩
  · intro B hB
    obtain ⟨C, hC, rfl⟩ := Finset.mem_smul_finset.1 hB
    rw [Finset.card_smul_finset]
    exact h.1 C hC
  · intro s hs
    have hs0 : (σ⁻¹ • s).card = 5 := by rw [Finset.card_smul_finset]; exact hs
    obtain ⟨B, ⟨hB, hsB⟩, hu⟩ := h.2 _ hs0
    refine ⟨σ • B, ⟨Finset.smul_mem_smul_finset hB, ?_⟩, ?_⟩
    · have := (Finset.smul_finset_subset_smul_finset_iff (a := σ)).2 hsB
      rwa [smul_inv_smul] at this
    · rintro B' ⟨hB', hsB'⟩
      obtain ⟨C, hC, rfl⟩ := Finset.mem_smul_finset.1 hB'
      have : σ⁻¹ • s ⊆ C := by
        have := (Finset.smul_finset_subset_smul_finset_iff (a := σ⁻¹)).2 hsB'
        rwa [inv_smul_smul] at this
      rw [hu C ⟨hC, this⟩]

theorem aut_trans {B B' : Finset (Fin 12)} (hB : B ∈ hexads) (hB' : B' ∈ hexads) :
    ∃ g ∈ autHexads, g • B = B' := by
  obtain ⟨-, h5, -⟩ := aut_hexads_sharply_five_transitive
  obtain ⟨s, hsB, hsc⟩ := Finset.exists_subset_card_eq
    (show 5 ≤ B.card by rw [hexads_card_six B hB]; norm_num)
  obtain ⟨s', hsB', hsc'⟩ := Finset.exists_subset_card_eq
    (show 5 ≤ B'.card by rw [hexads_card_six B' hB']; norm_num)
  obtain ⟨g, hg⟩ := MulAction.isMultiplyPretransitive_iff.1 h5
    (s.orderEmbOfFin hsc).toEmbedding (s'.orderEmbOfFin hsc').toEmbedding
  have hgs : g.1 • s = s' := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_smul_finset.1 hy
      have hx' : x ∈ Set.range (s.orderEmbOfFin hsc) := by
        rw [Finset.range_orderEmbOfFin]; exact hx
      obtain ⟨i, rfl⟩ := hx'
      have := DFunLike.congr_fun hg i
      have h2 : g.1 ((s.orderEmbOfFin hsc) i) = (s'.orderEmbOfFin hsc') i := this
      show g.1 _ ∈ s'
      rw [h2]
      exact Finset.orderEmbOfFin_mem _ _ _
    · rw [Finset.card_smul_finset]; omega
  have hgmem : g.1 • B ∈ hexads := by
    have h1 : g.1 • hexads = hexads := g.2
    rw [← h1]; exact Finset.smul_mem_smul_finset hB
  have hsub : s' ⊆ g.1 • B := by
    rw [← hgs]; exact (Finset.smul_finset_subset_smul_finset_iff (a := g.1)).2 hsB
  obtain ⟨_, _, hu⟩ := hexads_steiner.2 s' hsc'
  exact ⟨g.1, g.2, (hu _ ⟨hgmem, hsub⟩).trans (hu _ ⟨hB', hsB'⟩).symm⟩

def blockZero : Finset (Fin 12) := maskSet 123

theorem blockZero_mem : blockZero ∈ hexads := mem_hexads.2 ⟨123, by decide +kernel, rfl⟩

theorem hexads_card : hexads.card = 132 := by
  unfold hexads; decide +kernel

theorem card_orbit_aut : (orbit autHexads blockZero).ncard = 132 := by
  have : orbit autHexads blockZero = (hexads : Set (Finset (Fin 12))) := by
    ext B
    rw [mem_orbit_iff]
    constructor
    · rintro ⟨g, rfl⟩
      have h1 : g.1 • hexads = hexads := g.2
      show g.1 • blockZero ∈ hexads
      rw [← h1]; exact Finset.smul_mem_smul_finset blockZero_mem
    · intro hB
      obtain ⟨g, hg, rfl⟩ := aut_trans blockZero_mem hB
      exact ⟨⟨g, hg⟩, rfl⟩
  rw [this, Set.ncard_coe_finset, hexads_card]

theorem card_stab_aut : Nat.card (stabilizer autHexads blockZero) = 720 := by
  have := orb_mul autHexads blockZero
  rw [card_orbit_aut, card_autHexads] at this
  omega

theorem card_stab_set : Nat.card (stabilizer (Perm (Fin 12)) blockZero) = 518400 := by
  have h := orb_mul (Perm (Fin 12)) blockZero
  have hcard : blockZero.card = 6 := hexads_card_six _ blockZero_mem
  have horb : orbit (Perm (Fin 12)) blockZero =
      ((Finset.univ.powersetCard 6 : Finset (Finset (Fin 12))) : Set (Finset (Fin 12))) := by
    ext A
    rw [mem_orbit_iff]
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    constructor
    · rintro ⟨σ, rfl⟩
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_smul_finset, hcard]
    · rintro ⟨-, hA⟩
      exact exists_perm_smul_eq (by rw [hcard, hA])
  have hp : Nat.card (Perm (Fin 12)) = 479001600 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; decide
  have h6 : Nat.choose 12 6 = 924 := by decide
  rw [horb, Set.ncard_coe_finset, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
    hp, h6] at h
  omega

end CFSGOutside.WittDesigns.Witt5612
