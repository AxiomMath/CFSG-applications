import CFSGOutside.HallPaige.DoubleCosets
import CFSGOutside.HallPaige.Sporadic.GoodOfKlein
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# The Wilcox criterion for groups with a class of 3-transpositions

Let `d` be an involution of a finite group `G` whose conjugacy class `D` consists of
`3`-transpositions (any product of two elements of `D` has order `1`, `2` or `3`), and let
`H = C_G(d)`. The double cosets `HgH` correspond to the `H`-orbits on `D` via `g ↦ g d g⁻¹`:
`{d}`, the conjugates commuting with `d`, and those that do not. Suppose `|D|` is odd, `H` is
transitive on the commuting conjugates `D_d = D ∩ C(d) \ {d}`, and `D_d` is non-empty. Then

* for `y = g d g⁻¹` not commuting with `d`, `a = d y` lies in `HgH` and so does `a²`
  (`(dy)³ = 1`), so no information about the non-commuting conjugates is needed;
* `|D_d|` is even (`d` acts on `D \ {d}` as an involution with fixed points `D_d`), so any
  `e ∈ D_d` acting on `D_d` by conjugation has a second fixed point `f`: `d, e, f` pairwise
  commute, which gives `a, b ∈ HgH` with `ab ∈ HgH` for the commuting double coset;
* `d` and `e` are commuting involutions of `H`, so `H` is good.

The result is `CFSGOutside.HallPaige.wilcoxCriterion_of_threeTransposition`.
-/

namespace CFSGOutside.HallPaige

open DoubleCoset

universe u

/-- An involutive self-map of a finite type of even cardinality has an even number of fixed
points. -/
theorem even_card_fixed {α : Type*} [Finite α] (f : α → α) (hf : ∀ x, f (f x) = x)
    (hα : Even (Nat.card α)) : Even (Nat.card {x // f x = x}) := by
  classical
  have := Fintype.ofFinite α
  let F : Function.End α := f
  have h2 : F ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq]
    funext x
    exact hf x
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) h2
  rw [Nat.card_eq_fintype_card] at hα
  have : Nat.card {x // f x = x} = Fintype.card (Function.fixedPoints F) := by
    rw [Nat.card_eq_fintype_card]
    rfl
  rw [this, Nat.even_iff]
  have h1 := Nat.even_iff.1 hα
  unfold Nat.ModEq at hmod
  omega

section Group

variable {G : Type u} [Group G]

/-- The conjugates of `d` other than `d` that commute with `d`. -/
def commClass (d : G) : Set G := {x | IsConj d x ∧ x ≠ d ∧ x * d = d * x}

theorem mul_self_of_isConj {d x : G} (hd : d * d = 1) (hx : IsConj d x) : x * x = 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hx
  calc c * d * c⁻¹ * (c * d * c⁻¹) = c * (d * d) * c⁻¹ := by group
    _ = 1 := by rw [hd, mul_one, mul_inv_cancel]

theorem inv_eq_of_mul_self {x : G} (hx : x * x = 1) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right hx

/-- If `|D|` is odd then `|D_d|` is even. -/
theorem even_card_commClass [Finite G] {d : G} (hd : d * d = 1)
    (hodd : Odd (Nat.card {x // IsConj d x})) : Even (Nat.card (commClass d)) := by
  classical
  have hdi : d⁻¹ = d := inv_eq_of_mul_self hd
  let α := {x : G // IsConj d x ∧ x ≠ d}
  let f : α → α := fun x => ⟨d * x * d⁻¹, x.2.1.trans (isConj_iff.2 ⟨d, rfl⟩), fun h => x.2.2 (by
    calc (x : G) = d⁻¹ * (d * x * d⁻¹) * d := by group
      _ = d := by rw [h, hdi, hd, one_mul])⟩
  have hf : ∀ x, f (f x) = x := fun x => Subtype.ext (by
    change d * (d * (x : G) * d⁻¹) * d⁻¹ = x
    rw [hdi]
    calc d * (d * (x : G) * d) * d = (d * d) * x * (d * d) := by group
      _ = x := by rw [hd, one_mul, mul_one])
  -- `|α| = |D| - 1` is even
  have hαcard : Nat.card α + 1 = Nat.card {x // IsConj d x} := by
    let C := {x // IsConj d x}
    let c₀ : C := ⟨d, IsConj.refl d⟩
    have e1 : {b : C // b ≠ c₀} ≃ α :=
      { toFun := fun b => ⟨b.1.1, b.1.2, fun h => b.2 (Subtype.ext h)⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, fun h => x.2.2 (congrArg Subtype.val h)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have e2 := Equiv.optionSubtypeNe c₀
    rw [← Nat.card_congr e2, Finite.card_option, Nat.card_congr e1]
  have hαeven : Even (Nat.card α) := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩
  have hfix := even_card_fixed f hf hαeven
  have e3 : {x // f x = x} ≃ commClass d :=
    { toFun := fun x => ⟨x.1.1, x.1.2.1, x.1.2.2, by
        have h := congrArg Subtype.val x.2
        change d * (x.1 : G) * d⁻¹ = x.1 at h
        rw [hdi] at h
        calc (x.1 : G) * d = d * x.1 * d * d := by rw [h]
          _ = d * x.1 := by rw [mul_assoc (d * x.1), hd, mul_one]⟩
      invFun := fun x => ⟨⟨x.1, x.2.1, x.2.2.1⟩, Subtype.ext (by
        change d * (x : G) * d⁻¹ = x
        rw [← x.2.2.2, hdi, mul_assoc, hd, mul_one])⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rwa [← Nat.card_congr e3]

/-- **A triangle of commuting conjugates.** If `|D|` is odd and `e ∈ D_d`, some `f ∈ D_d` other
than `e` commutes with `e`. -/
theorem exists_commClass_commute [Finite G] {d : G} (hd : d * d = 1)
    (hodd : Odd (Nat.card {x // IsConj d x})) {e : G} (he : e ∈ commClass d) :
    ∃ f ∈ commClass d, f ≠ e ∧ f * e = e * f := by
  classical
  have hee : e * e = 1 := mul_self_of_isConj hd he.1
  have hei : e⁻¹ = e := inv_eq_of_mul_self hee
  have hed : e * d = d * e := he.2.2
  let β := commClass d
  let f : β → β := fun x => ⟨e * x * e⁻¹, by
    refine ⟨x.2.1.trans (isConj_iff.2 ⟨e, rfl⟩), fun h => x.2.2.1 ?_, ?_⟩
    · calc (x : G) = e⁻¹ * (e * x * e⁻¹) * e := by group
        _ = e⁻¹ * d * e := by rw [h]
        _ = d := by rw [hei, mul_assoc, ← hed, ← mul_assoc, hee, one_mul]
    · rw [hei]
      calc e * x * e * d = e * x * (e * d) := by group
        _ = e * (x * d) * e := by rw [hed]; group
        _ = e * (d * x) * e := by rw [x.2.2.2]
        _ = (e * d) * x * e := by group
        _ = d * (e * x * e) := by rw [hed]; group⟩
  have hf : ∀ x, f (f x) = x := fun x => Subtype.ext (by
    change e * (e * (x : G) * e⁻¹) * e⁻¹ = x
    rw [hei]
    calc e * (e * (x : G) * e) * e = (e * e) * x * (e * e) := by group
      _ = x := by rw [hee, one_mul, mul_one])
  have hfix := even_card_fixed f hf (even_card_commClass hd hodd)
  let e₀ : {x // f x = x} := ⟨⟨e, he⟩, Subtype.ext (by
    change e * e * e⁻¹ = e
    rw [hee, one_mul, hei])⟩
  have := Fintype.ofFinite {x // f x = x}
  have hlt : 1 < Fintype.card {x // f x = x} := by
    rw [← Nat.card_eq_fintype_card]
    have hpos : 0 < Nat.card {x // f x = x} := Nat.card_pos_iff.2 ⟨⟨e₀⟩, inferInstance⟩
    obtain ⟨k, hk⟩ := hfix
    omega
  obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card hlt e₀
  refine ⟨y.1.1, y.1.2, fun h => hy (Subtype.ext (Subtype.ext h)), ?_⟩
  have h := congrArg Subtype.val y.2
  change e * (y.1 : G) * e⁻¹ = y.1 at h
  calc (y.1 : G) * e = e * y.1 * e⁻¹ * e := by rw [h]
    _ = e * y.1 := by group

/-- Double cosets of `H = C_G(d)`: if `c ∈ H` conjugates `a d a⁻¹` to `g d g⁻¹`, then
`HaH = HgH`. -/
theorem mk_centralizer_eq {d c a g : G} (hc : c * d = d * c)
    (h : c * (a * d * a⁻¹) * c⁻¹ = g * d * g⁻¹) :
    mk (Subgroup.centralizer {d}) (Subgroup.centralizer {d}) a =
      mk (Subgroup.centralizer {d}) (Subgroup.centralizer {d}) g := by
  rw [DoubleCoset.eq]
  refine ⟨c, Subgroup.mem_centralizer_singleton_iff.2 hc, a⁻¹ * c⁻¹ * g,
    Subgroup.mem_centralizer_singleton_iff.2 ?_, by group⟩
  have h' : g⁻¹ * c * a * d = d * (g⁻¹ * c * a) := by
    have : g * d = c * a * d * a⁻¹ * c⁻¹ * g := by
      calc g * d = (g * d * g⁻¹) * g := by group
        _ = (c * (a * d * a⁻¹) * c⁻¹) * g := by rw [h]
        _ = c * a * d * a⁻¹ * c⁻¹ * g := by group
    calc g⁻¹ * c * a * d = g⁻¹ * (c * a * d * a⁻¹ * c⁻¹ * g) * (g⁻¹ * c * a) := by group
      _ = g⁻¹ * (g * d) * (g⁻¹ * c * a) := by rw [this]
      _ = d * (g⁻¹ * c * a) := by group
  have hinv : (a⁻¹ * c⁻¹ * g) = (g⁻¹ * c * a)⁻¹ := by group
  rw [hinv]
  calc (g⁻¹ * c * a)⁻¹ * d = (g⁻¹ * c * a)⁻¹ * (d * (g⁻¹ * c * a)) * (g⁻¹ * c * a)⁻¹ := by group
    _ = (g⁻¹ * c * a)⁻¹ * ((g⁻¹ * c * a) * d) * (g⁻¹ * c * a)⁻¹ := by rw [h']
    _ = d * (g⁻¹ * c * a)⁻¹ := by group

/-- **Wilcox criterion from a class of 3-transpositions.** -/
theorem wilcoxCriterion_of_threeTransposition [Finite G] (d : G) (hd : d * d = 1)
    (h3 : ∀ x z : G, IsConj d x → IsConj d z →
      orderOf (x * z) = 1 ∨ orderOf (x * z) = 2 ∨ orderOf (x * z) = 3)
    (htrans : ∀ x ∈ commClass d, ∀ y ∈ commClass d, ∃ c : G, c * d = d * c ∧ c * x * c⁻¹ = y)
    (hne : (commClass d).Nonempty) (hodd : Odd (Nat.card {x // IsConj d x}))
    (hcard : Nat.card {x // IsConj d x} ≠ 1) : WilcoxCriterion G := by
  classical
  set H := Subgroup.centralizer ({d} : Set G) with hH
  have hdi : d⁻¹ = d := inv_eq_of_mul_self hd
  have hmemH : ∀ c : G, c ∈ H ↔ c * d = d * c := fun c =>
    Subgroup.mem_centralizer_singleton_iff
  obtain ⟨e, he⟩ := hne
  obtain ⟨f, hf, hfe, hfe'⟩ := exists_commClass_commute hd hodd he
  have hee : e * e = 1 := mul_self_of_isConj hd he.1
  -- `H` is proper
  have hHne : H ≠ ⊤ := by
    intro htop
    apply hcard
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨d, IsConj.refl d⟩⟩⟩
    have key : ∀ z : {x // IsConj d x}, (z : G) = d := fun z => by
      obtain ⟨c, hc⟩ := isConj_iff.1 z.2
      have hcd := (hmemH c).1 (htop ▸ Subgroup.mem_top c)
      rw [← hc, hcd, mul_inv_cancel_right]
    rw [key x, key y]
  have hd1 : d ≠ 1 := by
    intro h1
    obtain ⟨c, hc⟩ := isConj_iff.1 he.1
    rw [h1, mul_one, mul_inv_cancel] at hc
    exact he.2.1 (hc.symm.trans h1.symm)
  have he1 : e ≠ 1 := by
    intro h1
    obtain ⟨c, hc⟩ := isConj_iff.1 he.1
    rw [h1] at hc
    have : d = 1 := by
      calc d = c⁻¹ * (c * d * c⁻¹) * c := by group
        _ = 1 := by rw [hc]; group
    exact hd1 this
  -- `H` is good
  have hgood : IsGood H :=
    Subgroup.isGood_of_commuting_involutions H (u := d) (v := e)
      ((hmemH d).2 rfl) ((hmemH e).2 he.2.2) (by rw [sq, hd]) (by rw [sq, hee])
      he.2.2.symm hd1 he1 (fun h => he.2.1 h.symm)
  refine ⟨H, hHne, hgood, Equiv.refl _, fun q => rfl, fun q => ?_⟩
  rw [← out_eq' q]
  set g := q.out
  simp only [Equiv.refl_apply]
  set y := g * d * g⁻¹ with hy
  have hyc : IsConj d y := isConj_iff.2 ⟨g, rfl⟩
  have hyy : y * y = 1 := mul_self_of_isConj hd hyc
  have hyi : y⁻¹ = y := inv_eq_of_mul_self hyy
  by_cases h1 : y = d
  · -- the trivial double coset
    have hmk : mk H H 1 = mk H H g :=
      mk_centralizer_eq (c := 1) (by rw [one_mul, mul_one])
        (by simp only [one_mul, inv_one, mul_one]; exact h1.symm)
    exact ⟨1, 1, hmk, hmk, by rw [mul_one, hmk]⟩
  by_cases h2 : y * d = d * y
  · -- the conjugates commuting with `d`
    have hyC : y ∈ commClass d := ⟨hyc, h1, h2⟩
    have key : ∀ {a : G} {x : G}, x ∈ commClass d → a * d * a⁻¹ = x → mk H H a = mk H H g := by
      intro a x hx hax
      obtain ⟨c, hc, hcx⟩ := htrans x hx y hyC
      exact mk_centralizer_eq hc (by rw [hax, hcx])
    obtain ⟨α, hα⟩ := isConj_iff.1 he.1
    have hdα : d = α⁻¹ * e * α := by rw [← hα]; group
    have hz : α⁻¹ * f * α ∈ commClass d := by
      refine ⟨hf.1.trans (isConj_iff.2 ⟨α⁻¹, by group⟩), fun h => hfe ?_, ?_⟩
      · calc f = α * (α⁻¹ * f * α) * α⁻¹ := by group
          _ = e := by rw [h, hα]
      · rw [hdα]
        calc α⁻¹ * f * α * (α⁻¹ * e * α) = α⁻¹ * (f * e) * α := by group
          _ = α⁻¹ * (e * f) * α := by rw [hfe']
          _ = α⁻¹ * e * α * (α⁻¹ * f * α) := by group
    obtain ⟨β, hβ⟩ := isConj_iff.1 hz.1
    refine ⟨α, β, key he hα, key hz hβ, key hf ?_⟩
    calc α * β * d * (α * β)⁻¹ = α * (β * d * β⁻¹) * α⁻¹ := by group
      _ = f := by rw [hβ]; group
  · -- the conjugates not commuting with `d`: `d * y` has order `3`
    have h3' : (d * y) ^ 3 = 1 := by
      rcases h3 d y (IsConj.refl d) hyc with h | h | h
      · exfalso
        apply h1
        have := orderOf_eq_one_iff.1 h
        calc y = d⁻¹ * (d * y) := by group
          _ = d := by rw [this, mul_one, hdi]
      · exfalso
        apply h2
        have h' : (d * y) ^ 2 = 1 := by rw [← h]; exact pow_orderOf_eq_one _
        have h'' : d * y * (d * y) = 1 := by rw [← sq]; exact h'
        calc y * d = (d * d) * y * d * (y * y) := by rw [hd, hyy, one_mul, mul_one]
          _ = d * (d * y * (d * y)) * y := by group
          _ = d * y := by rw [h'', mul_one]
      · rw [← h]; exact pow_orderOf_eq_one _
    have hdy : d * y * d * y * d = y := by
      calc d * y * d * y * d = (d * y * (d * y) * (d * y)) * y⁻¹ := by group
        _ = (d * y) ^ 3 * y⁻¹ := by rw [pow_three, mul_assoc (d * y)]
        _ = y := by rw [h3', one_mul, hyi]
    have ha : mk H H (d * y) = mk H H g := mk_centralizer_eq (c := 1) (by rw [one_mul, mul_one])
      (by
        calc 1 * (d * y * d * (d * y)⁻¹) * 1⁻¹ = d * y * d * y⁻¹ * d⁻¹ := by group
          _ = g * d * g⁻¹ := by rw [hyi, hdi, hdy])
    have haa : mk H H (d * y * (d * y)) = mk H H g := mk_centralizer_eq (c := d) rfl (by
      calc d * (d * y * (d * y) * d * (d * y * (d * y))⁻¹) * d⁻¹
          = d * (d * y * d * y * d * y⁻¹ * d⁻¹ * y⁻¹ * d⁻¹) * d⁻¹ := by group
        _ = d * (y * y * d * y * d) * d := by rw [hdy, hyi, hdi]
        _ = d * (d * y * d) * d := by rw [hyy, one_mul]
        _ = (d * d) * y * (d * d) := by group
        _ = g * d * g⁻¹ := by rw [hd, one_mul, mul_one])
    exact ⟨d * y, d * y, ha, ha, haa⟩

/-- The hypotheses of `wilcoxCriterion_of_threeTransposition` transported along an isomorphism. -/
theorem wilcoxCriterion_of_threeTransposition_of_mulEquiv {K : Type*} [Group K] [Finite K]
    {G : Type u} [Group G] (ψ : K ≃* G) (d : K) (hd : d * d = 1)
    (h3 : ∀ x z : K, IsConj d x → IsConj d z →
      orderOf (x * z) = 1 ∨ orderOf (x * z) = 2 ∨ orderOf (x * z) = 3)
    (htrans : ∀ x ∈ commClass d, ∀ y ∈ commClass d, ∃ c : K, c * d = d * c ∧ c * x * c⁻¹ = y)
    (hne : (commClass d).Nonempty) (hodd : Odd (Nat.card {x // IsConj d x}))
    (hcard : Nat.card {x // IsConj d x} ≠ 1) : WilcoxCriterion G := by
  have : Finite G := Finite.of_equiv _ ψ.toEquiv
  have hconj : ∀ x : G, IsConj (ψ d) x ↔ IsConj d (ψ.symm x) := fun x => by
    constructor
    · intro h
      obtain ⟨c, hc⟩ := isConj_iff.1 h
      exact isConj_iff.2 ⟨ψ.symm c, by rw [← hc]; simp⟩
    · intro h
      obtain ⟨c, hc⟩ := isConj_iff.1 h
      refine isConj_iff.2 ⟨ψ c, ?_⟩
      apply ψ.symm.injective
      simp [← hc]
  have hmem : ∀ x : G, x ∈ commClass (ψ d) ↔ ψ.symm x ∈ commClass d := fun x => by
    simp only [commClass, Set.mem_ofPred_eq, hconj]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, fun h => h2 (by rw [← h, MulEquiv.apply_symm_apply]), ?_⟩
      apply ψ.injective
      simp [h3]
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, fun h => h2 (by rw [h, MulEquiv.symm_apply_apply]), ?_⟩
      apply ψ.symm.injective
      simp [h3]
  have hcardG : Nat.card {x // IsConj (ψ d) x} = Nat.card {x // IsConj d x} :=
    Nat.card_congr (ψ.symm.toEquiv.subtypeEquiv fun x => hconj x)
  refine wilcoxCriterion_of_threeTransposition (ψ d) (by rw [← map_mul, hd, map_one]) ?_ ?_ ?_
    (hcardG ▸ hodd) (hcardG ▸ hcard)
  · intro x z hx hz
    have h := h3 _ _ ((hconj x).1 hx) ((hconj z).1 hz)
    rwa [← map_mul, MulEquiv.orderOf_eq] at h
  · intro x hx y hy
    obtain ⟨c, hc, hcy⟩ := htrans _ ((hmem x).1 hx) _ ((hmem y).1 hy)
    refine ⟨ψ c, by rw [← map_mul, hc, map_mul], ?_⟩
    apply ψ.symm.injective
    simp [hcy]
  · obtain ⟨e, he⟩ := hne
    exact ⟨ψ e, (hmem _).2 (by simpa using he)⟩

end Group

end CFSGOutside.HallPaige
