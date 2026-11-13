import Mathlib

/-!
Counting in a Steiner system `S(5,8,24)`: block numbers through `i` points and the intersection
numbers of two blocks (always even).
-/

namespace CFSGOutside.WittDesigns.Witt5824

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- A Steiner system `S(5,8,24)`: 24 points, blocks of size 8, every 5 points in exactly one block. -/
def IsSteiner5 (𝓑 : Finset (Finset Ω)) : Prop :=
  Fintype.card Ω = 24 ∧ (∀ B ∈ 𝓑, B.card = 8) ∧
    ∀ T : Finset Ω, T.card = 5 → ∃! B, B ∈ 𝓑 ∧ T ⊆ B

/-- Double counting the blocks through `S` and through `S ∪ {x}`. -/
theorem sum_card_filter_insert {𝓑 : Finset (Finset Ω)} {k : ℕ} (hk : ∀ B ∈ 𝓑, B.card = k)
    (S : Finset Ω) :
    ∑ x ∈ Finset.univ \ S, (𝓑.filter (insert x S ⊆ ·)).card =
      (𝓑.filter (S ⊆ ·)).card * (k - S.card) := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun B hB => ?_
  by_cases hS : S ⊆ B
  · have : ∀ x ∈ Finset.univ \ S, (if insert x S ⊆ B then 1 else 0) = if x ∈ B then 1 else 0 := by
      intro x _
      simp [Finset.insert_subset_iff, hS]
    rw [Finset.sum_congr rfl this, ← Finset.card_filter, if_pos hS, one_mul, ← hk B hB,
      ← Finset.card_sdiff_of_subset hS]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    tauto
  · have : ∀ x ∈ Finset.univ \ S, (if insert x S ⊆ B then 1 else 0) = 0 := by
      intro x _
      rw [if_neg]
      exact fun h => hS ((Finset.subset_insert x S).trans h)
    rw [Finset.sum_congr rfl this, if_neg hS]
    simp

theorem card_filter_succ {𝓑 : Finset (Finset Ω)} {k v i c : ℕ} (hk : ∀ B ∈ 𝓑, B.card = k)
    (hv : Fintype.card Ω = v)
    (hc : ∀ S : Finset Ω, S.card = i + 1 → (𝓑.filter (S ⊆ ·)).card = c)
    {S : Finset Ω} (hS : S.card = i) :
    (𝓑.filter (S ⊆ ·)).card * (k - i) = (v - i) * c := by
  rw [← hS, ← sum_card_filter_insert hk S]
  rw [Finset.sum_congr rfl (g := fun _ => c)]
  · rw [Finset.sum_const, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      hv, hS, smul_eq_mul]
  · intro x hx
    apply hc
    rw [Finset.card_insert_of_notMem (Finset.mem_sdiff.1 hx).2, hS]

/-- The number of blocks through `i` points. -/
def lamNum : ℕ → ℕ
  | 0 => 759
  | 1 => 253
  | 2 => 77
  | 3 => 21
  | 4 => 5
  | 5 => 1
  | _ => 0

section Design

variable {𝓑 : Finset (Finset Ω)} (h : IsSteiner5 𝓑)
include h

theorem card_filter_lam : ∀ {j : ℕ}, j ≤ 5 → ∀ {S : Finset Ω}, S.card = j →
    (𝓑.filter (S ⊆ ·)).card = lamNum j := by
  intro j
  induction' hj : 5 - j with d ih generalizing j
  · intro hj5 S hS
    have : j = 5 := by omega
    subst this
    obtain ⟨B, ⟨hB, hSB⟩, hu⟩ := h.2.2 S hS
    show _ = 1
    rw [Finset.card_eq_one]
    refine ⟨B, ?_⟩
    ext B'
    simp only [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun ⟨a, b⟩ => hu B' ⟨a, b⟩, fun e => e ▸ ⟨hB, hSB⟩⟩
  · intro hj5 S hS
    have hc : ∀ S' : Finset Ω, S'.card = j + 1 → (𝓑.filter (S' ⊆ ·)).card = lamNum (j + 1) :=
      fun S' hS' => ih (by omega) (by omega) hS'
    have := card_filter_succ h.2.1 h.1 hc hS
    interval_cases j <;> simp only [lamNum] at this ⊢ <;> omega

theorem card_blocks : 𝓑.card = 759 := by
  have := card_filter_lam h (j := 0) (by norm_num) (S := ∅) rfl
  simpa [lamNum] using this

/-- Moments of the intersection sizes with a fixed block. -/
theorem sum_choose_inter {B : Finset Ω} (hB : B ∈ 𝓑) {j : ℕ} (hj : j ≤ 5) :
    ∑ B' ∈ 𝓑.erase B, (B ∩ B').card.choose j = Nat.choose 8 j * (lamNum j - 1) := by
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
    _ = Nat.choose 8 j * (lamNum j - 1) := by
        simp [Finset.sum_const, Finset.card_powersetCard, h.2.1 B hB]

theorem card_inter_lt {B B' : Finset Ω} (hB : B ∈ 𝓑) (hB' : B' ∈ 𝓑) (hne : B ≠ B') :
    (B ∩ B').card < 8 := by
  have h1 : (B ∩ B').card ≤ 8 := (Finset.card_le_card Finset.inter_subset_left).trans_eq (h.2.1 B hB)
  by_contra hlt
  have h2 : (B ∩ B').card = 8 := by omega
  have e1 : B ∩ B' = B := Finset.eq_of_subset_of_card_le Finset.inter_subset_left
    (by rw [h2, h.2.1 B hB])
  have e2 : B ∩ B' = B' := Finset.eq_of_subset_of_card_le Finset.inter_subset_right
    (by rw [h2, h.2.1 B' hB'])
  exact hne (e1.symm.trans e2)

/-- Two distinct blocks of an `S(5,8,24)` meet in an even number of points. -/
theorem even_card_inter {B B' : Finset Ω} (hB : B ∈ 𝓑) (hB' : B' ∈ 𝓑) (hne : B ≠ B') :
    Even (B ∩ B').card := by
  set n : ℕ → ℕ := fun i => ((𝓑.erase B).filter (fun B' => (B ∩ B').card = i)).card with hn
  have hfib : ∀ f : ℕ → ℕ, ∑ B' ∈ 𝓑.erase B, f (B ∩ B').card = ∑ i ∈ Finset.range 8, n i * f i := by
    intro f
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun B' => (B ∩ B').card) (t := Finset.range 8)
      (fun B' hB'' => by
        rw [Finset.mem_range]
        have := Finset.mem_erase.1 hB''
        exact card_inter_lt h hB this.2 (Ne.symm this.1))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => f i) (fun B' hB'' => by rw [(Finset.mem_filter.1 hB'').2]),
      Finset.sum_const, smul_eq_mul]
  have e : ∀ j ≤ 5, ∑ i ∈ Finset.range 8, n i * i.choose j = Nat.choose 8 j * (lamNum j - 1) :=
    fun j hj => by rw [← hfib (fun i => i.choose j)]; exact sum_choose_inter h hB hj
  have e1 := e 1 (by norm_num)
  have e2 := e 2 (by norm_num)
  have e3 := e 3 (by norm_num)
  have e4 := e 4 (by norm_num)
  have e5 := e 5 (by norm_num)
  simp [Finset.sum_range_succ, Nat.choose, lamNum] at e1 e2 e3 e4 e5
  have hmem : B' ∈ (𝓑.erase B).filter (fun B'' => (B ∩ B'').card = (B ∩ B').card) :=
    Finset.mem_filter.2 ⟨Finset.mem_erase.2 ⟨Ne.symm hne, hB'⟩, rfl⟩
  have hpos : 0 < n (B ∩ B').card := Finset.card_pos.2 ⟨B', hmem⟩
  have hlt := card_inter_lt h hB hB' hne
  generalize (B ∩ B').card = t at hpos hlt
  interval_cases t <;> simp [Nat.even_iff] <;> omega

end Design

end CFSGOutside.WittDesigns.Witt5824
