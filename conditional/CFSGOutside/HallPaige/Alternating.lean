import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.GroupAction.Quotient
import CFSGOutside.HallPaige.Statements
import CFSGOutside.HallPaige.Defs

/-!
# Complete mappings of alternating groups

We show that every alternating group `alternatingGroup (Fin n)` has a complete mapping, assuming
Wilcox's coset criterion `CFSGOutside.HallPaige.CosetStatement` (Hall–Paige 1955, Theorem 3).

The inductive step uses the following *two-transitive criterion*: if `G` acts two-transitively
on a finite set `α` with at least three points and the stabilizer `H` of a point `a₀` has a
complete mapping, then so does `G`. Identifying `G ⧸ H` with `α`, it suffices to find bijections
`x y z : α ≃ α` such that for each `ω` there are `a, b ∈ G` with `a • a₀ = x ω`, `b • a₀ = y ω`
and `(a * b) • a₀ = z ω`. We take `x = y = id` and `z = π` a permutation whose only fixed point
is `a₀`: for `ω = a₀` take `a = b = 1`; for `ω ≠ a₀` take `b` with `b • a₀ = ω` and, by
two-transitivity, `a` with `a • a₀ = ω` and `a • ω = π ω` (note `ω ≠ π ω`).
-/

namespace CFSGOutside.HallPaige

open MulAction Equiv

universe u

/-- A permutation of a finite type with at least two elements that has no fixed point. -/
theorem exists_perm_forall_ne {β : Type*} [Fintype β] (hβ : 2 ≤ Fintype.card β) :
    ∃ σ : Perm β, ∀ x, σ x ≠ x := by
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card β = m + 2 := ⟨Fintype.card β - 2, by omega⟩
  let e : β ≃ Fin (m + 2) := Fintype.equivFinOfCardEq hm
  refine ⟨e.trans ((finRotate (m + 2)).trans e.symm), fun x hx => ?_⟩
  have h1 : finRotate (m + 2) (e x) = e x := by
    simpa [Equiv.symm_apply_eq] using hx
  have h2 : e x ∈ (finRotate (m + 2)).support := by simp [support_finRotate]
  exact (Perm.mem_support.mp h2) h1

/-- A permutation of a finite type with at least three elements whose only fixed point is `a₀`. -/
theorem exists_perm_fixed_iff {α : Type*} [Fintype α] [DecidableEq α] (hα : 3 ≤ Fintype.card α)
    (a₀ : α) : ∃ π : Perm α, ∀ ω, π ω = ω ↔ ω = a₀ := by
  have hcard : 2 ≤ Fintype.card {x // x ≠ a₀} := by
    have := Fintype.card_subtype_compl (fun x => x = a₀)
    simp only [Fintype.card_unique] at this
    rw [this]; omega
  obtain ⟨σ, hσ⟩ := exists_perm_forall_ne hcard
  refine ⟨Perm.ofSubtype σ, fun ω => ⟨fun h => ?_, ?_⟩⟩
  · by_contra hω
    rw [Perm.ofSubtype_apply_of_mem σ hω] at h
    exact hσ ⟨ω, hω⟩ (Subtype.ext h)
  · rintro rfl
    exact Perm.ofSubtype_apply_of_not_mem σ (by simp)

/-- **Two-transitive criterion.** If `G` acts two-transitively on a finite type `α` with at least
three points and the stabilizer of a point has a complete mapping, then `G` has a complete mapping
(assuming Wilcox's coset criterion). -/
theorem hasCompleteMapping_of_isMultiplyPretransitive (hcos : CosetStatement.{u})
    {G α : Type u} [Group G] [Finite G] [MulAction G α] [Fintype α] [DecidableEq α]
    [h2 : IsMultiplyPretransitive G α 2] (hα : 3 ≤ Fintype.card α) (a₀ : α)
    (hH : HasCompleteMapping (stabilizer G a₀)) : HasCompleteMapping G := by
  have : IsPretransitive G α := isPretransitive_of_is_two_pretransitive
  have h2' : ∀ {a b c d : α}, a ≠ b → c ≠ d → ∃ g : G, g • a = c ∧ g • b = d :=
    is_two_pretransitive_iff.mp h2
  let e : α ≃ G ⧸ stabilizer G a₀ :=
    (Equiv.subtypeUnivEquiv (fun ω => mem_orbit_iff.mpr (exists_smul_eq G a₀ ω))).symm.trans
      (orbitEquivQuotientStabilizer G a₀)
  have he : ∀ (g : G) (ω : α), (g : G ⧸ stabilizer G a₀) = e ω ↔ g • a₀ = ω := by
    intro g ω
    rw [← Equiv.symm_apply_eq]
    simp [e, orbitEquivQuotientStabilizer_symm_apply]
  obtain ⟨π, hπ⟩ := exists_perm_fixed_iff hα a₀
  refine hcos (stabilizer G a₀) hH e e (π.trans e) fun ω => ?_
  simp only [Equiv.trans_apply, he]
  by_cases hω : ω = a₀
  · subst hω
    exact ⟨1, 1, by simp, by simp, by simp [(hπ _).mpr rfl]⟩
  · obtain ⟨b, hb⟩ := exists_smul_eq G a₀ ω
    obtain ⟨a, ha₁, ha₂⟩ := h2' (Ne.symm hω) (fun h => hω ((hπ ω).mp h.symm))
    exact ⟨a, b, ha₁, hb, by rw [mul_smul, hb, ha₂]⟩

/-- The stabilizer of a point `a₀` in `alternatingGroup α` is isomorphic to the alternating group
on the complement of `a₀`. -/
noncomputable def stabilizerAlternatingGroupEquiv {α : Type*} [Fintype α] [DecidableEq α]
    (a₀ : α) : alternatingGroup {x // x ≠ a₀} ≃* stabilizer (alternatingGroup α) a₀ := by
  let φ : alternatingGroup {x // x ≠ a₀} →* alternatingGroup α :=
    (Perm.ofSubtype.comp (alternatingGroup {x // x ≠ a₀}).subtype).codRestrict _ fun g => by
      simp [Perm.mem_alternatingGroup, Perm.sign_ofSubtype, (Perm.mem_alternatingGroup.mp g.2)]
  have hφ : Function.Injective φ := by
    intro g h hgh
    exact Subtype.ext (Perm.ofSubtype_injective (congrArg Subtype.val hgh))
  have hrange : φ.range = stabilizer (alternatingGroup α) a₀ := by
    ext g
    constructor
    · rintro ⟨s, rfl⟩
      rw [mem_stabilizer_iff, Subgroup.smul_def]
      exact Perm.ofSubtype_apply_of_not_mem (s : Perm {x // x ≠ a₀}) (by simp)
    · intro hg
      rw [mem_stabilizer_iff, Subgroup.smul_def] at hg
      change (g : Perm α) a₀ = a₀ at hg
      have h₁ : ∀ x, (g : Perm α) x ≠ a₀ ↔ x ≠ a₀ := by
        intro x
        rw [not_iff_not, ← hg, (g : Perm α).injective.eq_iff, hg]
      have h₂ : ∀ x, (g : Perm α) x ≠ x → x ≠ a₀ := by
        rintro x hx rfl
        exact hx hg
      refine ⟨⟨(g : Perm α).subtypePerm h₁, ?_⟩, ?_⟩
      · rw [Perm.mem_alternatingGroup, Perm.sign_subtypePerm _ _ h₂]
        exact Perm.mem_alternatingGroup.mp g.2
      · exact Subtype.ext (Perm.ofSubtype_subtypePerm h₁ h₂)
  exact (MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hrange)

/-- Alternating groups of degree at most `3` have odd order. -/
theorem odd_card_alternatingGroup {α : Type*} [Fintype α] [DecidableEq α]
    (hα : Fintype.card α ≤ 3) : Odd (Nat.card (alternatingGroup α)) := by
  rw [Nat.card_eq_fintype_card]
  rcases Nat.lt_or_ge (Fintype.card α) 2 with h | h
  · have : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    rw [Fintype.card_unique]
    exact odd_one
  · have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have h2 := two_mul_card_alternatingGroup (α := α)
    rw [Fintype.card_perm] at h2
    interval_cases hc : Fintype.card α
    · rw [show (2 : ℕ).factorial = 2 from rfl] at h2
      exact ⟨0, by omega⟩
    · rw [show (3 : ℕ).factorial = 6 from rfl] at h2
      exact ⟨1, by omega⟩

/-- Alternating groups have complete mappings, assuming Wilcox's coset criterion. -/
theorem hasCompleteMapping_alternatingGroup_of_cosetStatement' (hcos : CosetStatement.{0}) :
    ∀ (n : ℕ) (α : Type) [Fintype α] [DecidableEq α], Fintype.card α = n →
      HasCompleteMapping (alternatingGroup α) := by
  intro n
  induction n with
  | zero =>
    intro α _ _ hα
    exact hasCompleteMapping_of_odd (odd_card_alternatingGroup (by omega))
  | succ n ih =>
    intro α _ _ hα
    rcases Nat.lt_or_ge n 3 with hn | hn
    · exact hasCompleteMapping_of_odd (odd_card_alternatingGroup (by omega))
    obtain ⟨a₀⟩ : Nonempty α := Fintype.card_pos_iff.mp (by omega)
    have hcard : Fintype.card {x // x ≠ a₀} = n := by
      have := Fintype.card_subtype_compl (fun x => x = a₀)
      simp only [Fintype.card_unique] at this
      rw [this]; omega
    have : IsMultiplyPretransitive (alternatingGroup α) α 2 := by
      have := alternatingGroup.isMultiplyPretransitive α
      rw [Nat.card_eq_fintype_card, hα] at this
      exact isMultiplyPretransitive_of_le (n := n + 1 - 2) (by omega)
        (by rw [Nat.card_eq_fintype_card, hα]; omega)
    exact hasCompleteMapping_of_isMultiplyPretransitive hcos (by omega) a₀
      ((ih _ hcard).of_mulEquiv (stabilizerAlternatingGroupEquiv a₀))

/-- **Hall–Paige, Theorem 3.** Every alternating group has a complete mapping (assuming Wilcox's
coset criterion `CosetStatement`). -/
theorem hasCompleteMapping_alternatingGroup_of_cosetStatement (hcos : CosetStatement.{0})
    (n : ℕ) : HasCompleteMapping (alternatingGroup (Fin n)) :=
  hasCompleteMapping_alternatingGroup_of_cosetStatement' hcos n (Fin n) (Fintype.card_fin n)

end CFSGOutside.HallPaige
