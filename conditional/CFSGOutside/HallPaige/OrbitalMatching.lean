import Mathlib
import CFSGOutside.HallPaige.Cosets

/-!
# Complete mappings from a matching of suborbits

A generalisation of the Wilcox criterion (Wilcox, *Reduction of the Hall–Paige conjecture to sporadic
simple groups*, J. Algebra 321 (2009), Proposition 14) that allows the matching of double cosets to be
fractional.

Let `G` act transitively on `X` with point stabilizer `H = G_{x₀}`, and label the points by their
`H`-orbit (`lab : X → ι`). For points `p = g • x₀` and `q`, the *orbital* of `(p, q)` is the label of
`g⁻¹ • q`. If there is a permutation `f` of `X` such that the orbital of `(p, f p)` is the label of `p`
for every `p`, then `G` has a complete mapping (provided `H` has one): `CosetStatement` applies with
`x = y = id` and `z = f`.

Such a permutation exists as soon as there is a matrix `F : ι → ι → ℕ` with row and column sums the
suborbit sizes, positive only on pairs `(j, l)` for which some `p` labelled `j` and `q` labelled `l` have
orbital `j` (a *witness triangle* `x₀, p, q`). The proof is Hall's marriage theorem
(`Finset.all_card_le_biUnion_card_iff_exists_injective`) applied to a doubly stochastic weight built
from `F`; since `H` is transitive on each label class, the number of `q` labelled `l` related to a `p`
labelled `j` depends only on `j` and `l`.

The case `F = diag (sizes)` is `WilcoxCriterion` with `ψ = id`.

## Main results

* `CFSGOutside.HallPaige.exists_equiv_of_doublyStochastic`: Hall's theorem, fractional form.
* `CFSGOutside.HallPaige.exists_equiv_of_flow`: a flow matrix on the label classes gives a permutation.
* `CFSGOutside.HallPaige.hasCompleteMapping_of_flow`: the criterion.
-/

namespace CFSGOutside.HallPaige

open Finset MulAction

section Hall

variable {α : Type*} [Fintype α]

/-- **Hall's marriage theorem, fractional form.** If a relation `R` on a finite set carries a
nonnegative weight with all row and column sums `1`, positive only on `R`, then `R` contains the graph of
a permutation. -/
theorem exists_equiv_of_doublyStochastic (R : α → α → Prop) (w : α → α → ℚ)
    (hw0 : ∀ p q, 0 ≤ w p q) (hwR : ∀ p q, 0 < w p q → R p q)
    (hrow : ∀ p, ∑ q, w p q = 1) (hcol : ∀ q, ∑ p, w p q = 1) :
    ∃ f : α ≃ α, ∀ p, R p (f p) := by
  classical
  let t : α → Finset α := fun p => univ.filter fun q => 0 < w p q
  have hall : ∀ s : Finset α, s.card ≤ (s.biUnion t).card := by
    intro s
    have key : (s.card : ℚ) ≤ (s.biUnion t).card := by
      calc (s.card : ℚ) = ∑ p ∈ s, ∑ q, w p q := by simp [hrow]
        _ = ∑ p ∈ s, ∑ q ∈ s.biUnion t, w p q := by
          refine Finset.sum_congr rfl fun p hp => (Finset.sum_subset (Finset.subset_univ _) ?_).symm
          intro q _ hq
          refine le_antisymm (not_lt.1 fun h => hq ?_) (hw0 p q)
          exact Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩
        _ = ∑ q ∈ s.biUnion t, ∑ p ∈ s, w p q := Finset.sum_comm
        _ ≤ ∑ q ∈ s.biUnion t, ∑ p, w p q :=
          Finset.sum_le_sum fun q _ =>
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun p _ _ => hw0 p q
        _ = (s.biUnion t).card := by simp [hcol]
    exact_mod_cast key
  obtain ⟨f, hinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
  exact ⟨Equiv.ofBijective f hinj.bijective_of_finite, fun p =>
    hwR p (f p) (Finset.mem_filter.1 (hf p)).2⟩

end Hall

section Flow

variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]

/-- The points with label `l`. -/
def fiber (lab : α → ι) (l : ι) : Finset α := univ.filter fun q => lab q = l

theorem mem_fiber {lab : α → ι} {l : ι} {q : α} : q ∈ fiber lab l ↔ lab q = l := by
  simp [fiber]

/-- **A flow on the label classes gives a permutation.** Let `R` be a relation on `α` whose number of
`R`-successors (`R`-predecessors) with a given label `l` (`j`) depends only on the label of the point
(`a`, `b`). If `F` has row and column sums the label class sizes and `a j l > 0` wherever `F j l > 0`,
then `R` contains the graph of a permutation. -/
theorem exists_equiv_of_flow (R : α → α → Prop) [DecidableRel R] (lab : α → ι)
    (F : ι → ι → ℕ) (hrow : ∀ j, ∑ l, F j l = (fiber lab j).card)
    (hcol : ∀ l, ∑ j, F j l = (fiber lab l).card)
    (a b : ι → ι → ℕ) (ha : ∀ p l, ((fiber lab l).filter (R p)).card = a (lab p) l)
    (hb : ∀ q j, ((fiber lab j).filter fun p => R p q).card = b j (lab q))
    (hpos : ∀ j l, 0 < F j l → 0 < a j l) : ∃ f : α ≃ α, ∀ p, R p (f p) := by
  classical
  set n : ι → ℕ := fun j => (fiber lab j).card with hn
  have hdc : ∀ j l, n j * a j l = n l * b j l := by
    intro j l
    have h1 : ∑ p ∈ fiber lab j, ((fiber lab l).filter (R p)).card = n j * a j l :=
      Finset.sum_const_nat fun p hp => by rw [ha, mem_fiber.1 hp]
    have h2 : ∑ q ∈ fiber lab l, ((fiber lab j).filter fun p => R p q).card = n l * b j l :=
      Finset.sum_const_nat fun q hq => by rw [hb, mem_fiber.1 hq]
    rw [← h1, ← h2]
    exact Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow R
  have hnpos : ∀ p, 0 < n (lab p) := fun p => Finset.card_pos.2 ⟨p, mem_fiber.2 rfl⟩
  have hFle : ∀ j l, F j l ≤ n j := fun j l => by
    show F j l ≤ (fiber lab j).card
    rw [← hrow j]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  let c : ι → ι → ℚ := fun j l => (F j l : ℚ) / ((n j : ℚ) * a j l)
  let w : α → α → ℚ := fun p q => if R p q then c (lab p) (lab q) else 0
  have hc0 : ∀ j l, 0 ≤ c j l := fun j l => by positivity
  have hsum : ∀ (s : Finset α) (P : α → Prop) [DecidablePred P] (x : ℚ),
      ∑ q ∈ s, (if P q then x else 0) = (s.filter P).card * x := fun s P _ x => by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hfib : ∀ (g : α → ℚ), ∑ q, g q = ∑ l, ∑ q ∈ fiber lab l, g q := fun g =>
    (Finset.sum_fiberwise Finset.univ lab g).symm
  refine exists_equiv_of_doublyStochastic R w (fun p q => ?_) (fun p q h => ?_) (fun p => ?_)
    (fun q => ?_)
  · dsimp only [w]
    split_ifs
    · exact hc0 _ _
    · exact le_rfl
  · dsimp only [w] at h
    split_ifs at h with hr
    · exact hr
    · exact absurd h (lt_irrefl 0)
  · have hl : ∀ l, ∑ q ∈ fiber lab l, w p q = (F (lab p) l : ℚ) / n (lab p) := by
      intro l
      calc ∑ q ∈ fiber lab l, w p q = ∑ q ∈ fiber lab l, (if R p q then c (lab p) l else 0) :=
            Finset.sum_congr rfl fun q hq => by simp only [w, mem_fiber.1 hq]
        _ = a (lab p) l * c (lab p) l := by rw [hsum, ha]
        _ = (F (lab p) l : ℚ) / n (lab p) := by
          rcases Nat.eq_zero_or_pos (F (lab p) l) with h0 | h0
          · simp [c, h0]
          · have ha0 : (a (lab p) l : ℚ) ≠ 0 := by exact_mod_cast (hpos _ _ h0).ne'
            have hn0 : (n (lab p) : ℚ) ≠ 0 := by exact_mod_cast (hnpos p).ne'
            simp only [c]
            field_simp
    have hn0 : (n (lab p) : ℚ) ≠ 0 := by exact_mod_cast (hnpos p).ne'
    rw [hfib, Finset.sum_congr rfl fun l _ => hl l, ← Finset.sum_div, ← Nat.cast_sum, hrow]
    exact div_self hn0
  · have hl : ∀ j, ∑ p ∈ fiber lab j, w p q = (F j (lab q) : ℚ) / n (lab q) := by
      intro j
      calc ∑ p ∈ fiber lab j, w p q = ∑ p ∈ fiber lab j, (if R p q then c j (lab q) else 0) :=
            Finset.sum_congr rfl fun p hp => by simp only [w, mem_fiber.1 hp]
        _ = b j (lab q) * c j (lab q) := by rw [hsum, hb]
        _ = (F j (lab q) : ℚ) / n (lab q) := by
          rcases Nat.eq_zero_or_pos (F j (lab q)) with h0 | h0
          · simp [c, h0]
          · have hapos := hpos _ _ h0
            have hnj : 0 < n j := lt_of_lt_of_le h0 (hFle _ _)
            have hprod : 0 < n (lab q) * b j (lab q) := by
              rw [← hdc]
              exact Nat.mul_pos hnj hapos
            have hb0 : (b j (lab q) : ℚ) ≠ 0 := by
              exact_mod_cast (Nat.pos_of_mul_pos_left hprod).ne'
            have hnq : (n (lab q) : ℚ) ≠ 0 := by exact_mod_cast (hnpos q).ne'
            have e : (n j : ℚ) * a j (lab q) = n (lab q) * b j (lab q) := by
              exact_mod_cast hdc j (lab q)
            simp only [c]
            rw [e]
            field_simp
    have hn0 : (n (lab q) : ℚ) ≠ 0 := by exact_mod_cast (hnpos q).ne'
    rw [hfib, Finset.sum_congr rfl fun j _ => hl j, ← Finset.sum_div, ← Nat.cast_sum, hcol]
    exact div_self hn0

end Flow

section Action

variable {G X ι : Type*} [Group G] [MulAction G X]

/-- **Complete mappings from a flow on the suborbits.** Let `G` act transitively on `X`, let the point
stabilizer `H = G_{x₀}` have a complete mapping, and let `lab` label the `H`-orbits. Let `F` be a
matrix with row and column sums the suborbit sizes such that, wherever `F j l > 0`, some `g, g'` have
`g • x₀` labelled `j`, `g' • x₀` labelled `l`, and `(g⁻¹ * g') • x₀` labelled `j` (the triangle
`x₀, g • x₀, g' • x₀` has orbitals `j, l, j`). Then `G` has a complete mapping. -/
theorem hasCompleteMapping_of_flow [Finite G] [Fintype ι] [DecidableEq ι] (x₀ : X)
    (htrans : ∀ y : X, ∃ g : G, g • x₀ = y) (hH : HasCompleteMapping (stabilizer G x₀))
    (lab : X → ι) (hlab : ∀ y y', lab y = lab y' ↔ ∃ h ∈ stabilizer G x₀, h • y = y')
    (F : ι → ι → ℕ) (hrow : ∀ j, ∑ l, F j l = Nat.card {y // lab y = j})
    (hcol : ∀ l, ∑ j, F j l = Nat.card {y // lab y = l})
    (hwit : ∀ j l, 0 < F j l →
      ∃ g g' : G, lab (g • x₀) = j ∧ lab (g' • x₀) = l ∧ lab ((g⁻¹ * g') • x₀) = j) :
    HasCompleteMapping G := by
  classical
  haveI : Finite X := Finite.of_surjective (fun g : G => g • x₀) htrans
  letI := Fintype.ofFinite X
  set H := stabilizer G x₀ with hHdef
  have hinv : ∀ h ∈ H, ∀ y, lab (h • y) = lab y := fun h hh y =>
    ((hlab _ _).2 ⟨h, hh, rfl⟩).symm
  let R : X → X → Prop := fun p q => ∀ g : G, g • x₀ = p → lab (g⁻¹ • q) = lab p
  have hR : ∀ (g : G) (p q : X), g • x₀ = p → lab (g⁻¹ • q) = lab p → R p q := by
    intro g p q hg hq g' hg'
    have hh : g⁻¹ * g' ∈ H := by
      rw [mem_stabilizer_iff, mul_smul, hg', ← hg, inv_smul_smul]
    have e : (g⁻¹ * g')⁻¹ * g⁻¹ = g'⁻¹ := by group
    rw [← e, ← smul_smul, hinv _ (H.inv_mem hh), hq]
  have hRinv : ∀ h ∈ H, ∀ p q, R p q → R (h • p) (h • q) := by
    intro h hh p q hpq g hg
    have hg' : (h⁻¹ * g) • x₀ = p := by rw [mul_smul, hg, inv_smul_smul]
    have e := hpq _ hg'
    have e2 : (h⁻¹ * g)⁻¹ • q = g⁻¹ • h • q := by rw [mul_inv_rev, inv_inv, mul_smul]
    rw [e2] at e
    rw [e, hinv h hh]
  have hRiff : ∀ h ∈ H, ∀ p q, R (h • p) (h • q) ↔ R p q := by
    intro h hh p q
    refine ⟨fun hr => ?_, hRinv h hh p q⟩
    have := hRinv h⁻¹ (H.inv_mem hh) _ _ hr
    rwa [inv_smul_smul, inv_smul_smul] at this
  have hrowC : ∀ p p' l, lab p = lab p' →
      ((fiber lab l).filter (R p)).card = ((fiber lab l).filter (R p')).card := by
    intro p p' l hpp'
    obtain ⟨h, hh, rfl⟩ := (hlab p p').1 hpp'
    refine Finset.card_nbij' (fun q => h • q) (fun q => h⁻¹ • q) (fun q hq => ?_) (fun q hq => ?_)
      (fun q _ => inv_smul_smul h q) (fun q _ => smul_inv_smul h q)
    · simp only [Finset.coe_filter, mem_fiber, Set.mem_setOf_eq] at hq ⊢
      exact ⟨by rw [hinv h hh, hq.1], (hRiff h hh p q).2 hq.2⟩
    · simp only [Finset.coe_filter, mem_fiber, Set.mem_setOf_eq] at hq ⊢
      refine ⟨by rw [hinv _ (H.inv_mem hh), hq.1], ?_⟩
      have := (hRiff h hh p (h⁻¹ • q)).1
      rw [smul_inv_smul] at this
      exact this hq.2
  have hcolC : ∀ q q' j, lab q = lab q' →
      ((fiber lab j).filter fun p => R p q).card = ((fiber lab j).filter fun p => R p q').card := by
    intro q q' j hqq'
    obtain ⟨h, hh, rfl⟩ := (hlab q q').1 hqq'
    refine Finset.card_nbij' (fun p => h • p) (fun p => h⁻¹ • p) (fun p hp => ?_) (fun p hp => ?_)
      (fun p _ => inv_smul_smul h p) (fun p _ => smul_inv_smul h p)
    · simp only [Finset.coe_filter, mem_fiber, Set.mem_setOf_eq] at hp ⊢
      exact ⟨by rw [hinv h hh, hp.1], (hRiff h hh p q).2 hp.2⟩
    · simp only [Finset.coe_filter, mem_fiber, Set.mem_setOf_eq] at hp ⊢
      refine ⟨by rw [hinv _ (H.inv_mem hh), hp.1], ?_⟩
      have := (hRiff h hh (h⁻¹ • p) q).1
      rw [smul_inv_smul] at this
      exact this hp.2
  let rep : ι → X := fun j => if hj : ∃ p, lab p = j then hj.choose else x₀
  have hrep : ∀ p, lab (rep (lab p)) = lab p := fun p => by
    have hj : ∃ p', lab p' = lab p := ⟨p, rfl⟩
    simp only [rep, dif_pos hj]
    exact hj.choose_spec
  let a : ι → ι → ℕ := fun j l => ((fiber lab l).filter (R (rep j))).card
  let b : ι → ι → ℕ := fun j l => ((fiber lab j).filter fun p => R p (rep l)).card
  have hcard : ∀ j, Nat.card {y // lab y = j} = (fiber lab j).card := fun j => by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  obtain ⟨f, hf⟩ := exists_equiv_of_flow R lab F (fun j => by rw [hrow, hcard])
    (fun l => by rw [hcol, hcard]) a b (fun p l => hrowC _ _ _ (hrep p).symm)
    (fun q j => hcolC _ _ _ (hrep q).symm) (fun j l hF => by
      obtain ⟨g, g', hj, hl, hjj⟩ := hwit j l hF
      have hpq : R (g • x₀) (g' • x₀) := hR g _ _ rfl (by rw [smul_smul, hjj, hj])
      have hmem : g' • x₀ ∈ (fiber lab l).filter (R (g • x₀)) :=
        Finset.mem_filter.2 ⟨mem_fiber.2 hl, hpq⟩
      have := Finset.card_pos.2 ⟨_, hmem⟩
      rwa [hrowC (g • x₀) (rep j) l (by rw [← hj, hrep])] at this)
  let E : G ⧸ H ≃ X := (MulAction.orbitEquivQuotientStabilizer G x₀).symm.trans
    (Equiv.subtypeUnivEquiv fun y => htrans y)
  have hE : ∀ g : G, E g = g • x₀ := fun g => rfl
  refine hasCompleteMapping_of_cosets H hH (Equiv.refl _) (Equiv.refl _) (E.trans (f.trans E.symm))
    fun i => ?_
  induction i using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨g', hg'⟩ := htrans (f (g • x₀))
    have hq := hf (g • x₀) g rfl
    rw [← hg', smul_smul] at hq
    obtain ⟨h₁, hh₁, he⟩ := (hlab _ _).1 hq.symm
    refine ⟨g * h₁, g, ?_, rfl, ?_⟩
    · rw [Equiv.refl_apply, QuotientGroup.eq]
      have e : (g * h₁)⁻¹ * g = h₁⁻¹ := by group
      rw [e]
      exact H.inv_mem hh₁
    · show ((g * h₁ * g : G) : G ⧸ H) = E.symm (f (E (g : G ⧸ H)))
      rw [Equiv.eq_symm_apply, hE, hE, ← hg', mul_assoc, mul_smul, mul_smul, he, ← mul_smul,
        mul_inv_cancel_left]

end Action

end CFSGOutside.HallPaige
