import Mathlib
import CFSGOutside.WittDesigns.S5824.Design

/-!
Counting in a Steiner system `S(4,7,23)`: block numbers through `i` points and the parity of the
intersection of two blocks (always odd, in fact 1 or 3).
-/

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSGOutside.WittDesigns.Witt4723

open CFSGOutside.WittDesigns.Witt5824 (sum_card_filter_insert card_filter_succ)

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- A Steiner system `S(4,7,23)`: 23 points, blocks of size 7, every 4 points in exactly one block. -/
def IsSteiner4 (𝓑 : Finset (Finset Ω)) : Prop :=
  Fintype.card Ω = 23 ∧ (∀ B ∈ 𝓑, B.card = 7) ∧
    ∀ T : Finset Ω, T.card = 4 → ∃! B, B ∈ 𝓑 ∧ T ⊆ B

/-- The number of blocks through `i` points. -/
def lamNum : ℕ → ℕ
  | 0 => 253
  | 1 => 77
  | 2 => 21
  | 3 => 5
  | 4 => 1
  | _ => 0

section Design

variable {𝓑 : Finset (Finset Ω)} (h : IsSteiner4 𝓑)
include h

theorem card_filter_lam : ∀ {j : ℕ}, j ≤ 4 → ∀ {S : Finset Ω}, S.card = j →
    (𝓑.filter (S ⊆ ·)).card = lamNum j := by
  intro j
  induction' hj : 4 - j with d ih generalizing j
  · intro hj4 S hS
    have : j = 4 := by omega
    subst this
    obtain ⟨B, ⟨hB, hSB⟩, hu⟩ := h.2.2 S hS
    show _ = 1
    rw [Finset.card_eq_one]
    refine ⟨B, ?_⟩
    ext B'
    simp only [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun ⟨a, b⟩ => hu B' ⟨a, b⟩, fun e => e ▸ ⟨hB, hSB⟩⟩
  · intro hj4 S hS
    have hc : ∀ S' : Finset Ω, S'.card = j + 1 → (𝓑.filter (S' ⊆ ·)).card = lamNum (j + 1) :=
      fun S' hS' => ih (by omega) (by omega) hS'
    have := card_filter_succ h.2.1 h.1 hc hS
    interval_cases j <;> simp only [lamNum] at this ⊢ <;> omega

theorem sum_choose_inter {B : Finset Ω} (hB : B ∈ 𝓑) {j : ℕ} (hj : j ≤ 4) :
    ∑ B' ∈ 𝓑.erase B, (B ∩ B').card.choose j = Nat.choose 7 j * (lamNum j - 1) := by
  calc ∑ B' ∈ 𝓑.erase B, (B ∩ B').card.choose j
      = ∑ B' ∈ 𝓑.erase B, ((B.powersetCard j).filter (· ⊆ B')).card := by
        refine Finset.sum_congr rfl fun B' _ => ?_
        rw [← Finset.card_powersetCard]
        congr 1
        ext S
        simp only [Finset.mem_powersetCard, Finset.subset_inter_iff, Finset.mem_filter]
        tauto
    _ = ∑ B' ∈ 𝓑.erase B, ∑ S ∈ B.powersetCard j, if S ⊆ B' then 1 else 0 := by
        refine Finset.sum_congr rfl fun B' _ => ?_
        rw [Finset.card_filter]
    _ = ∑ S ∈ B.powersetCard j, ∑ B' ∈ 𝓑.erase B, if S ⊆ B' then 1 else 0 := Finset.sum_comm
    _ = ∑ S ∈ B.powersetCard j, (lamNum j - 1) := by
        refine Finset.sum_congr rfl fun S hS => ?_
        obtain ⟨hSB, hSc⟩ := Finset.mem_powersetCard.1 hS
        rw [← Finset.card_filter]
        have : (𝓑.erase B).filter (S ⊆ ·) = (𝓑.filter (S ⊆ ·)).erase B := by
          ext B'
          simp only [Finset.mem_filter, Finset.mem_erase]
          tauto
        rw [this, Finset.card_erase_of_mem (by simp [hB, hSB]), card_filter_lam h hj hSc]
    _ = Nat.choose 7 j * (lamNum j - 1) := by
        simp [Finset.sum_const, Finset.card_powersetCard, h.2.1 B hB]

theorem card_inter_lt {B B' : Finset Ω} (hB : B ∈ 𝓑) (hB' : B' ∈ 𝓑) (hne : B ≠ B') :
    (B ∩ B').card < 7 := by
  have h1 : (B ∩ B').card ≤ 7 := (Finset.card_le_card Finset.inter_subset_left).trans_eq (h.2.1 B hB)
  by_contra hlt
  have h2 : (B ∩ B').card = 7 := by omega
  have e1 : B ∩ B' = B := Finset.eq_of_subset_of_card_le Finset.inter_subset_left
    (by rw [h2, h.2.1 B hB])
  have e2 : B ∩ B' = B' := Finset.eq_of_subset_of_card_le Finset.inter_subset_right
    (by rw [h2, h.2.1 B' hB'])
  exact hne (e1.symm.trans e2)

/-- Two distinct blocks of an `S(4,7,23)` meet in an odd number of points. -/
theorem odd_card_inter {B B' : Finset Ω} (hB : B ∈ 𝓑) (hB' : B' ∈ 𝓑) (hne : B ≠ B') :
    Odd (B ∩ B').card := by
  set n : ℕ → ℕ := fun i => ((𝓑.erase B).filter (fun B' => (B ∩ B').card = i)).card with hn
  have hfib : ∀ f : ℕ → ℕ, ∑ B' ∈ 𝓑.erase B, f (B ∩ B').card = ∑ i ∈ Finset.range 7, n i * f i := by
    intro f
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun B' => (B ∩ B').card) (t := Finset.range 7)
      (fun B' hB'' => by
        rw [Finset.mem_range]
        have := Finset.mem_erase.1 hB''
        exact card_inter_lt h hB this.2 (Ne.symm this.1))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => f i) (fun B' hB'' => by rw [(Finset.mem_filter.1 hB'').2]),
      Finset.sum_const, smul_eq_mul]
  have e : ∀ j ≤ 4, ∑ i ∈ Finset.range 7, n i * i.choose j = Nat.choose 7 j * (lamNum j - 1) :=
    fun j hj => by rw [← hfib (fun i => i.choose j)]; exact sum_choose_inter h hB hj
  have e0 := e 0 (by norm_num)
  have e1 := e 1 (by norm_num)
  have e2 := e 2 (by norm_num)
  have e3 := e 3 (by norm_num)
  have e4 := e 4 (by norm_num)
  simp [Finset.sum_range_succ, Nat.choose, lamNum] at e0 e1 e2 e3 e4
  have hmem : B' ∈ (𝓑.erase B).filter (fun B'' => (B ∩ B'').card = (B ∩ B').card) :=
    Finset.mem_filter.2 ⟨Finset.mem_erase.2 ⟨Ne.symm hne, hB'⟩, rfl⟩
  have hpos : 0 < n (B ∩ B').card := Finset.card_pos.2 ⟨B', hmem⟩
  have hlt := card_inter_lt h hB hB' hne
  generalize (B ∩ B').card = t at hpos hlt
  interval_cases t <;> simp [Nat.odd_iff] <;> omega

end Design

end CFSGOutside.WittDesigns.Witt4723
