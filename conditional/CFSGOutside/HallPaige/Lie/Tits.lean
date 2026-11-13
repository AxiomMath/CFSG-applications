import CFSGOutside.HallPaige.Lie.Basic
import TauCeti.GroupTheory.TitsSystem.Bruhat.Exchange

/-!
# Involutions of the Weyl group and the Wilcox criterion

Let `(B, N)` be a Tits system (`TauCeti.TitsSystem`) with Weyl group `W`. We show that the
Bruhat cell of every involution `w` of `W` is contained in its own square,
`BwB ⊆ (BwB)(BwB)` (`CFSGOutside.HallPaige.TitsSystem.bruhatCell_subset_mul_self`). The proof is by induction
on the length of `w`, using a left descent `s` of `w`: either `s` commutes with `w`, and then
`BwB = (Bw'B)(BsB) = (BsB)(Bw'B)` with `w' = sw`, or `ℓ (sws) = ℓ w - 2`, and then
`BwB = (BsB)(Bw'B)(BsB)` with `w' = sws`.

Consequently, if `H ⊇ B` is a proper good subgroup and every double coset `HgH` meets the Bruhat
cell of an involution, then the Wilcox criterion holds for `G` with `ψ = id`
(`CFSGOutside.HallPaige.TitsSystem.wilcoxCriterion_of_involution_cover`). For a parabolic subgroup `P_J` this
is the case as soon as every double coset `W_J w W_J` contains an involution. This generalises
Wilcox, Lemma 18 (whose representatives `u⁻¹ s₁ ⋯ s_p u` are involutions).
-/

namespace CFSGOutside.HallPaige

namespace TitsSystem

open DoubleCoset TauCeti TauCeti.TitsSystem
open scoped Pointwise

universe u

variable {G : Type u} [Group G] (T : TauCeti.TitsSystem G)

local prefix:100 "ℓ " => T.simpleGenerators.wordLength

/-- A nontrivial element of the Weyl group has a left descent. -/
theorem exists_simple_wordLength_mul_lt {w : T.WeylGroup} (hw : w ≠ 1) :
    ∃ s ∈ T.simple, ℓ (s * w) < ℓ w := by
  obtain ⟨l, hl, hlen, hprod⟩ := T.exists_prod_eq_of_wordLength w
  match l, hl, hlen, hprod with
  | [], _, _, hprod => exact absurd hprod.symm (by simpa using hw)
  | s :: l', hl, hlen, hprod =>
    have hs : s ∈ T.simple := hl s (by simp)
    refine ⟨s, hs, ?_⟩
    have hsw : s * w = l'.prod := by
      rw [← hprod, List.prod_cons, T.simple_mul_simple_cancel_left hs]
    rw [hsw]
    have := T.wordLength_prod_le (l := l') fun x hx => hl x (by simp [hx])
    simp only [List.length_cons] at hlen
    omega

/-- For an involution `w` with a left descent `s`, either `s` commutes with `w` or conjugation by
`s` shortens `w` by two. -/
theorem simple_mul_comm_or_wordLength {w s : T.WeylGroup} (hw : w * w = 1) (hs : s ∈ T.simple)
    (hsw : ℓ (s * w) < ℓ w) : s * w = w * s ∨ ℓ (s * w * s) + 2 = ℓ w := by
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  have h1 : ℓ (s * w) + 1 = ℓ w := by
    have := T.wordLength_simple_mul hs w
    omega
  have hws : ℓ (w * s) = ℓ (s * w) := by
    rw [T.wordLength_mul_simple_eq_wordLength_simple_mul_inv w hs, hwinv]
  rcases T.wordLength_mul_simple (s * w) hs with h2 | h2
  · left
    -- `x = s w` with `ℓ (x s) = ℓ x + 1`; the exchange step gives `s x = x s`.
    have hx : T.bruhatCell s * T.bruhatCell (s * w) = T.bruhatCell (s * (s * w)) :=
      T.bruhatCell_mul_eq_of_wordLength_le hs (by rw [T.simple_mul_simple_cancel_left hs]; omega)
    have hne : T.bruhatCell s * T.bruhatCell (s * w * s) ≠ T.bruhatCell (s * (s * w * s)) := by
      rw [Ne, T.bruhatCell_mul_eq_iff_wordLength_lt hs]
      have : s * (s * w * s) = w * s := by
        rw [mul_assoc, T.simple_mul_simple_cancel_left hs]
      rw [this]
      omega
    have key := simple_mul_eq_mul_simple_of_bruhatCell_mul_ne T hs hs hx hne
    rw [T.simple_mul_simple_cancel_left hs] at key
    calc s * w = s * (s * w * s) := by rw [← key]
      _ = w * s := by rw [mul_assoc, T.simple_mul_simple_cancel_left hs]
  · right
    omega

/-- The square of a simple cell contains the cell itself. -/
theorem bruhatCell_subset_mul_self_simple {s : T.WeylGroup} (hs : s ∈ T.simple) :
    T.bruhatCell s ⊆ T.bruhatCell s * T.bruhatCell s := by
  rw [T.bruhatCell_mul_self_eq_union_of_mem_simple hs]
  exact Set.subset_union_right

/-- The square of a simple cell contains `B`. -/
theorem subgroupB_subset_mul_self_simple {s : T.WeylGroup} (hs : s ∈ T.simple) :
    (T.subgroupB : Set G) ⊆ T.bruhatCell s * T.bruhatCell s := by
  rw [T.bruhatCell_mul_self_eq_union_of_mem_simple hs, T.bruhatCell_one]
  exact Set.subset_union_left

/-- **Involution cells are contained in their squares.** For every involution `w` of the Weyl
group, `BwB ⊆ (BwB)(BwB)`. -/
theorem bruhatCell_subset_mul_self {w : T.WeylGroup} (hw : w * w = 1) :
    T.bruhatCell w ⊆ T.bruhatCell w * T.bruhatCell w := by
  induction hn : ℓ w using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    by_cases h1 : w = 1
    · subst h1
      rw [T.bruhatCell_one]
      intro x hx
      exact ⟨x, hx, 1, T.subgroupB.one_mem, mul_one x⟩
    obtain ⟨s, hs, hsw⟩ := exists_simple_wordLength_mul_lt T h1
    rcases simple_mul_comm_or_wordLength T hw hs hsw with hc | hl
    · -- `w = w' s = s w'` with `w' = s w` an involution.
      obtain ⟨w', hw'⟩ : ∃ w', w' = s * w := ⟨_, rfl⟩
      have hsw' : s * w' = w := by rw [hw', T.simple_mul_simple_cancel_left hs]
      have hw's : w' * s = w := by rw [hw', hc, mul_assoc, T.simple_sq_eq_one hs, mul_one]
      have hw'2 : w' * w' = 1 := by
        have : w' * w' = w' * s * w := by rw [mul_assoc, ← hw']
        rw [this, hw's, hw]
      have hlen : ℓ w' < ℓ w := by rw [hw']; exact hsw
      have ih' := ih (ℓ w') (hn ▸ hlen) hw'2 rfl
      have hL : T.bruhatCell s * T.bruhatCell w' = T.bruhatCell w := by
        rw [← hsw']
        exact T.bruhatCell_mul_eq_of_wordLength_le hs (by rw [hsw']; omega)
      have hR : T.bruhatCell w' * T.bruhatCell s = T.bruhatCell w := by
        rw [← hw's]
        exact T.bruhatCell_mul_eq_of_wordLength_le_right w' hs (by rw [hw's]; omega)
      calc T.bruhatCell w = T.bruhatCell w' * T.bruhatCell s := hR.symm
        _ ⊆ (T.bruhatCell w' * T.bruhatCell w') * (T.bruhatCell s * T.bruhatCell s) :=
            Set.mul_subset_mul ih' (bruhatCell_subset_mul_self_simple T hs)
        _ = T.bruhatCell w' * (T.bruhatCell w' * T.bruhatCell s) * T.bruhatCell s := by
            simp only [mul_assoc]
        _ = T.bruhatCell w' * T.bruhatCell w * T.bruhatCell s := by rw [hR]
        _ = T.bruhatCell w' * (T.bruhatCell s * T.bruhatCell w') * T.bruhatCell s := by rw [hL]
        _ = T.bruhatCell w * T.bruhatCell w := by rw [← hR]; simp only [mul_assoc]
    · -- `w = s w' s` with `w' = s w s` an involution of length `ℓ w - 2`.
      set w' := s * w * s with hw'
      have hw'2 : w' * w' = 1 := by
        rw [hw']
        calc s * w * s * (s * w * s) = s * w * (s * s) * w * s := by simp only [mul_assoc]
          _ = 1 := by rw [T.simple_sq_eq_one hs, mul_one, mul_assoc s w w, hw, mul_one,
                T.simple_sq_eq_one hs]
      have hlen : ℓ w' < ℓ w := by omega
      have ih' := ih (ℓ w') (hn ▸ hlen) hw'2 rfl
      have hsw' : s * w' = w * s := by
        rw [hw', ← mul_assoc, ← mul_assoc, T.simple_sq_eq_one hs, one_mul]
      have hsws : s * w' * s = w := by
        rw [hsw', mul_assoc, T.simple_sq_eq_one hs, mul_one]
      have hlws : ℓ (w * s) + 1 = ℓ w := by
        have h := T.wordLength_mul_simple_eq_wordLength_simple_mul_inv w hs
        rw [inv_eq_of_mul_eq_one_right hw] at h
        have := T.wordLength_simple_mul hs w
        omega
      have hL : T.bruhatCell s * T.bruhatCell w' = T.bruhatCell (s * w') :=
        T.bruhatCell_mul_eq_of_wordLength_le hs (by rw [hsw']; omega)
      have hR : T.bruhatCell (s * w') * T.bruhatCell s = T.bruhatCell w := by
        rw [← hsws]
        exact T.bruhatCell_mul_eq_of_wordLength_le_right (s * w') hs
          (by rw [hsws, hsw']; omega)
      have hw_eq : T.bruhatCell w = T.bruhatCell s * T.bruhatCell w' * T.bruhatCell s := by
        rw [hL, hR]
      have hBw' : T.bruhatCell w' = T.bruhatCell w' * (T.subgroupB : Set G) :=
        (T.bruhatCell_mul_subgroupB w').symm
      calc T.bruhatCell w = T.bruhatCell s * T.bruhatCell w' * T.bruhatCell s := hw_eq
        _ ⊆ T.bruhatCell s * ((T.bruhatCell w' * (T.subgroupB : Set G)) * T.bruhatCell w') *
              T.bruhatCell s := by
            rw [← hBw']
            exact Set.mul_subset_mul_right (Set.mul_subset_mul_left ih')
        _ ⊆ T.bruhatCell s * ((T.bruhatCell w' * (T.bruhatCell s * T.bruhatCell s)) *
              T.bruhatCell w') * T.bruhatCell s :=
            Set.mul_subset_mul_right (Set.mul_subset_mul_left (Set.mul_subset_mul_right
              (Set.mul_subset_mul_left (subgroupB_subset_mul_self_simple T hs))))
        _ = (T.bruhatCell s * T.bruhatCell w' * T.bruhatCell s) *
              (T.bruhatCell s * T.bruhatCell w' * T.bruhatCell s) := by
            simp only [mul_assoc]
        _ = T.bruhatCell w * T.bruhatCell w := by rw [← hw_eq]

/-- A Bruhat cell lies in the `H`-double coset of any of its elements, for `H ⊇ B`. -/
theorem bruhatCell_subset_doubleCoset {H : Subgroup G} (hBH : T.subgroupB ≤ H)
    {w : T.WeylGroup} {x : G} (hx : x ∈ T.bruhatCell w) :
    T.bruhatCell w ⊆ doubleCoset x (H : Set G) H := by
  rw [T.bruhatCell_eq_doubleCoset hx]
  intro y hy
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_doubleCoset.1 hy
  exact mem_doubleCoset.2 ⟨b, hBH hb, b', hBH hb', rfl⟩

/-- **The Wilcox criterion from involutions of the Weyl group.** Let `H ⊇ B` be a proper good
subgroup such that every double coset `HgH` meets the Bruhat cell of an involution of the Weyl
group. Then `WilcoxCriterion G` holds (with `ψ = id`). -/
theorem wilcoxCriterion_of_involution_cover (H : Subgroup G) (hBH : T.subgroupB ≤ H)
    (hH : H ≠ ⊤) (hgood : IsGood H)
    (hcov : ∀ g : G, ∃ w : T.WeylGroup, w * w = 1 ∧
      ∃ x ∈ T.bruhatCell w, x ∈ doubleCoset g (H : Set G) H) :
    WilcoxCriterion G := by
  refine wilcoxCriterion_of_forall_mul_mem H hH hgood fun g => ?_
  obtain ⟨w, hw, x, hxw, hxg⟩ := hcov g
  have hsub : T.bruhatCell w ⊆ doubleCoset g (H : Set G) H := by
    rw [← doubleCoset_eq_of_mem hxg]
    exact bruhatCell_subset_doubleCoset T hBH hxw
  obtain ⟨a, ha, b, hb, hab⟩ := bruhatCell_subset_mul_self T hw hxw
  exact ⟨a, b, hsub ha, hsub hb, by rw [show a * b = x from hab]; exact hxg⟩

/-- `B x B · B y B ⊇ B (x y) B`. -/
theorem bruhatCell_mul_subset_mul (x y : T.WeylGroup) :
    T.bruhatCell (x * y) ⊆ T.bruhatCell x * T.bruhatCell y := by
  obtain ⟨n, hn, -⟩ := T.exists_mem_bruhatCell x
  obtain ⟨m, hm, -⟩ := T.exists_mem_bruhatCell y
  rw [← hn, ← hm, ← QuotientGroup.mk_mul, T.bruhatCell_mk, T.bruhatCell_mk, T.bruhatCell_mk]
  intro z hz
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_doubleCoset.1 hz
  exact ⟨b * (n : G), mem_doubleCoset.2 ⟨b, hb, 1, T.subgroupB.one_mem, by simp⟩,
    (m : G) * b', mem_doubleCoset.2 ⟨1, T.subgroupB.one_mem, b', hb', by simp⟩,
    by simp [mul_assoc]⟩

/-- **The Wilcox criterion for overgroups of `B` from the Weyl group.** Let `H ⊇ B` be a proper
good subgroup and `J` a set of elements of `W` whose cells lie in `H` (for a parabolic subgroup
`P_J`, the simple reflections in `J`). If every double coset `⟨J⟩ w ⟨J⟩` of the subgroup `⟨J⟩`
generated by `J` contains an involution, then `WilcoxCriterion G` holds. -/
theorem wilcoxCriterion_of_weyl_cover (H : Subgroup G) (hBH : T.subgroupB ≤ H) (hH : H ≠ ⊤)
    (hgood : IsGood H) (J : Subgroup T.WeylGroup) (hJ : ∀ x ∈ J, T.bruhatCell x ⊆ H)
    (hcov : ∀ w : T.WeylGroup, ∃ x ∈ J, ∃ y ∈ J, (x * w * y) * (x * w * y) = 1) :
    WilcoxCriterion G := by
  refine wilcoxCriterion_of_involution_cover T H hBH hH hgood fun g => ?_
  obtain ⟨w, hw, -⟩ := T.existsUnique_mem_bruhatCell g
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov w
  refine ⟨_, hxy, ?_⟩
  obtain ⟨nx, hnx, hnxc⟩ := T.exists_mem_bruhatCell x
  obtain ⟨ny, hny, hnyc⟩ := T.exists_mem_bruhatCell y
  obtain ⟨nw, hnw, hnwc⟩ := T.exists_mem_bruhatCell w
  refine ⟨(nx : G) * nw * ny, ?_, ?_⟩
  · rw [← hnx, ← hnw, ← hny, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, T.bruhatCell_mk]
    exact mem_doubleCoset_self _ _ _
  · have hgw : (nw : G) ∈ doubleCoset g (H : Set G) H := by
      rw [← doubleCoset_eq_of_mem (bruhatCell_subset_doubleCoset T hBH hw hnwc)]
      exact mem_doubleCoset_self _ _ _
    obtain ⟨h, hh, h', hh', he⟩ := mem_doubleCoset.1 hgw
    refine mem_doubleCoset.2 ⟨nx * h, H.mul_mem (hJ x hx hnxc) hh, h' * ny,
      H.mul_mem hh' (hJ y hy hnyc), ?_⟩
    rw [he]
    group

end TitsSystem

end CFSGOutside.HallPaige
