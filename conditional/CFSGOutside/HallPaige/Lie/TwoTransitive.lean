import CFSGOutside.HallPaige.Lie.Good
import CFSGOutside.HallPaige.DoubleCosets
import CFSGOutside.HallPaige.Cosets

/-!
# Two-transitive actions with a good point stabilizer

`CFSGOutside.HallPaige.hasCompleteMapping_of_two_transitive'`: a good group with admissible proper good
subgroups, acting 2-transitively on at least three points with a good point stabilizer, has a
complete mapping; `CFSGOutside.HallPaige.hasCompleteMapping_of_two_transitive_of_odd`: the same when the
number of points is odd (the stabilizer then has odd index, hence is good).
-/

namespace CFSGOutside.HallPaige

open MulAction

variable {G : Type} [Group G] [Finite G] {α : Type*} [MulAction G α] [Finite α]

/-- In a 2-transitive action on at least two points the orbit of a point is everything. -/
theorem orbit_eq_univ_of_two_transitive (x₀ : α)
    (h2 : ∀ x y x' y' : α, x ≠ y → x' ≠ y' → ∃ g : G, g • x = x' ∧ g • y = y') :
    orbit G x₀ = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  by_cases hy : y = x₀
  · rw [hy]; exact mem_orbit_self _
  · obtain ⟨g, hg, -⟩ := h2 x₀ y y x₀ (Ne.symm hy) hy
    exact ⟨g, hg⟩

theorem index_stabilizer_of_two_transitive (x₀ : α)
    (h2 : ∀ x y x' y' : α, x ≠ y → x' ≠ y' → ∃ g : G, g • x = x' ∧ g • y = y') :
    (stabilizer G x₀).index = Nat.card α := by
  rw [index_stabilizer, orbit_eq_univ_of_two_transitive x₀ h2, Set.ncard_univ]

theorem stabilizer_ne_top_of_two_transitive (x₀ : α)
    (h2 : ∀ x y x' y' : α, x ≠ y → x' ≠ y' → ∃ g : G, g • x = x' ∧ g • y = y')
    (h3 : 2 ≤ Nat.card α) : stabilizer G x₀ ≠ ⊤ := by
  intro htop
  have := index_stabilizer_of_two_transitive x₀ h2
  rw [htop, Subgroup.index_top] at this
  omega

/-- **2-transitive actions with a good point stabilizer.** -/
theorem hasCompleteMapping_of_two_transitive' (x₀ : α)
    (h2 : ∀ x y x' y' : α, x ≠ y → x' ≠ y' → ∃ g : G, g • x = x' ∧ g • y = y')
    (h3 : 3 ≤ Nat.card α) (hgood : IsGood (stabilizer G x₀))
    (hP : ProperSubgroupsAdmissible G) : HasCompleteMapping G :=
  hasCompleteMapping_of_two_transitive cosetStatement x₀ h2 h3
    (hP _ (stabilizer_ne_top_of_two_transitive x₀ h2 (by omega)) hgood)

/-- **2-transitive actions on an odd number of points.** -/
theorem hasCompleteMapping_of_two_transitive_of_odd (x₀ : α)
    (h2 : ∀ x y x' y' : α, x ≠ y → x' ≠ y' → ∃ g : G, g • x = x' ∧ g • y = y')
    (h3 : 3 ≤ Nat.card α) (hodd : Odd (Nat.card α)) (hG : IsGood G)
    (hP : ProperSubgroupsAdmissible G) : HasCompleteMapping G :=
  hasCompleteMapping_of_two_transitive' x₀ h2 h3
    (isGood_of_index_odd hG _ (by rw [index_stabilizer_of_two_transitive x₀ h2]; exact hodd)) hP

end CFSGOutside.HallPaige
