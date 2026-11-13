import CFSGOutside.HallPaige.Statements

/-!
# Double coset criteria used for the groups of Lie type

* `CFSGOutside.HallPaige.wilcoxCriterion_of_forall_mul_mem`: the Wilcox criterion with `ψ = id`, i.e. Wilcox,
  Corollary 16: a proper good subgroup `H` all of whose double cosets `D` meet `D * D`.
* `CFSGOutside.HallPaige.wilcoxCriterion_of_rankOne`: the rank-one case of a (B,N)-pair: if
  `G = B ∪ BsB` and `sBs ⊄ B`, and `B` is good, then the Wilcox criterion holds with `H = B`.
-/

namespace CFSGOutside.HallPaige

open DoubleCoset

universe u

variable {G : Type u} [Group G]

/-- **Wilcox, Corollary 16** in the form of `WilcoxCriterion` (with `ψ = id`): a proper good
subgroup `H` such that every double coset `HgH` contains `a`, `b` with `a * b ∈ HgH`. -/
theorem wilcoxCriterion_of_forall_mul_mem (H : Subgroup G) (hH : H ≠ ⊤) (hgood : IsGood H)
    (h : ∀ g : G, ∃ a b : G, a ∈ doubleCoset g (H : Set G) H ∧ b ∈ doubleCoset g (H : Set G) H ∧
      a * b ∈ doubleCoset g (H : Set G) H) :
    WilcoxCriterion G := by
  refine ⟨H, hH, hgood, Equiv.refl _, fun _ => rfl, fun q => ?_⟩
  induction q using Quotient.inductionOn with
  | h g =>
    obtain ⟨a, b, ha, hb, hab⟩ := h g
    exact ⟨a, b, mk_eq_of_doubleCoset_eq (doubleCoset_eq_of_mem ha),
      mk_eq_of_doubleCoset_eq (doubleCoset_eq_of_mem hb),
      mk_eq_of_doubleCoset_eq (doubleCoset_eq_of_mem hab)⟩

/-- The double coset of an element of `H` is `H` itself, and contains `1`. -/
theorem one_mem_doubleCoset_of_mem {H : Subgroup G} {g : G} (hg : g ∈ H) :
    (1 : G) ∈ doubleCoset g (H : Set G) H :=
  mem_doubleCoset.2 ⟨g⁻¹, H.inv_mem hg, 1, H.one_mem, by group⟩

/-- **Rank-one (B,N)-pairs.** Suppose `G = B ∪ BsB` with `s ∉ B`, and `s b s ∉ B` for some
`b ∈ B`. If `B` is good then the Wilcox criterion holds for `G` (with `H = B`, `ψ = id`): the
double coset `BsB` contains `s` and `b * s`, whose product `s * b * s` lies in `BsB`. -/
theorem wilcoxCriterion_of_rankOne (B : Subgroup G) (s : G) (hs : s ∉ B)
    (hcov : ∀ g : G, g ∉ B → g ∈ doubleCoset s (B : Set G) B) (b : G) (hb : b ∈ B)
    (hsbs : s * b * s ∉ B) (hgood : IsGood B) : WilcoxCriterion G := by
  refine wilcoxCriterion_of_forall_mul_mem B (fun h => hs (h ▸ Subgroup.mem_top s)) hgood
    fun g => ?_
  by_cases hg : g ∈ B
  · exact ⟨1, 1, one_mem_doubleCoset_of_mem hg, one_mem_doubleCoset_of_mem hg,
      by simpa using one_mem_doubleCoset_of_mem hg⟩
  · rw [doubleCoset_eq_of_mem (hcov g hg)]
    refine ⟨s, b * s, mem_doubleCoset_self _ _ s,
      mem_doubleCoset.2 ⟨b, hb, 1, B.one_mem, by group⟩, ?_⟩
    rw [← mul_assoc]
    exact hcov _ hsbs

end CFSGOutside.HallPaige
