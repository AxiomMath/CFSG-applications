import CFSGOutside.HallPaige.DoubleCosets
import CFSGOutside.HallPaige.Sporadic.GoodOfKlein

/-!
# Triangles of `a`-conjugates and the Wilcox criterion

Let `a` be an involution of `G` and `H = C(a)`. The double cosets `H x H` correspond to the
`H`-orbits on the conjugates `x a x⁻¹`. When `H`-orbits are told apart by the class of `a · β`
(the first clause of the corpus `IsTwoAGraphData`, `CFSG/Monster/Existence/Defs.lean:71`), a triangle
`α, β, γ` of conjugates of `a` whose three products are conjugate to `a · β` gives a triangle witness
for the double coset of `β` (`wilcoxCriterion_of_triangles`).

The file also has the generic triangles used for the Monster: dihedral ones (`tri_two`,
`tri_dihedral`), and the counting argument (`exists_tri_of_card`): if the conjugates `γ` of `a`
with `a γ ∼ c` are more than half of the class of `a`, there is a triangle with all products
conjugate to `c`.
-/

namespace CFSGOutside.HallPaige.M

open DoubleCoset

variable {G : Type*} [Group G]

/-- The orbit clause: `H`-orbits on the conjugates of `a` are told apart by the class of `a β`. -/
def OrbitClause (a : G) : Prop :=
  ∀ β β' : G, IsConj a β → IsConj a β' → IsConj (a * β) (a * β') →
    ∃ g ∈ Subgroup.centralizer ({a} : Set G), g * β * g⁻¹ = β'

/-- A triangle of conjugates of `a` with all three products conjugate to `c`. -/
def Tri (a c : G) : Prop :=
  ∃ α β γ : G, IsConj a α ∧ IsConj a β ∧ IsConj a γ ∧ IsConj (α * β) c ∧ IsConj (β * γ) c ∧
    IsConj (α * γ) c

theorem mem_cent_iff {a g : G} : g ∈ Subgroup.centralizer ({a} : Set G) ↔ g * a * g⁻¹ = a := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h; rw [h, mul_inv_cancel_right]
  · intro h; calc g * a = g * a * g⁻¹ * g := by group
      _ = a * g := by rw [h]

theorem mk_eq_of_conj {a : G} {h x y : G} (hh : h ∈ Subgroup.centralizer ({a} : Set G))
    (hxy : h * (x * a * x⁻¹) * h⁻¹ = y * a * y⁻¹) :
    mk (Subgroup.centralizer ({a} : Set G)) (Subgroup.centralizer ({a} : Set G)) x =
      mk (Subgroup.centralizer ({a} : Set G)) (Subgroup.centralizer ({a} : Set G)) y := by
  rw [DoubleCoset.eq]
  refine ⟨h, hh, x⁻¹ * h⁻¹ * y, ?_, by group⟩
  rw [mem_cent_iff]
  calc x⁻¹ * h⁻¹ * y * a * (x⁻¹ * h⁻¹ * y)⁻¹ = x⁻¹ * h⁻¹ * (y * a * y⁻¹) * h * x := by group
    _ = a := by rw [← hxy]; group

theorem mk_eq_of_isConj {a : G} (horb : OrbitClause a) {x y : G}
    (hc : IsConj (a * (x * a * x⁻¹)) (a * (y * a * y⁻¹))) :
    mk (Subgroup.centralizer ({a} : Set G)) (Subgroup.centralizer ({a} : Set G)) x =
      mk (Subgroup.centralizer ({a} : Set G)) (Subgroup.centralizer ({a} : Set G)) y := by
  obtain ⟨h, hh, e⟩ := horb _ _ (isConj_iff.2 ⟨x, rfl⟩) (isConj_iff.2 ⟨y, rfl⟩) hc
  exact mk_eq_of_conj hh e

theorem isConj_conj (g x : G) : IsConj x (g * x * g⁻¹) := isConj_iff.2 ⟨g, rfl⟩

theorem isConj_conj_inv (g x : G) : IsConj x (g⁻¹ * x * g) := isConj_iff.2 ⟨g⁻¹, by group⟩

/-- **Triangle form of the criterion for `C(a)`.** -/
theorem wilcoxCriterion_of_triangles {a : G} (horb : OrbitClause a)
    (hne : Subgroup.centralizer ({a} : Set G) ≠ ⊤) (hgood : IsGood (Subgroup.centralizer ({a} : Set G)))
    (htri : ∀ β, IsConj a β → Tri a (a * β)) : WilcoxCriterion G := by
  set H := Subgroup.centralizer ({a} : Set G) with hH
  refine wilcoxCriterion_of_triangle H hne hgood fun q => ?_
  set g := q.out
  have hq : mk H H g = q := out_eq' q
  obtain ⟨α, β, γ, hα, hβ, hγ, hαβ, hβγ, hαγ⟩ := htri (g * a * g⁻¹) (isConj_conj g a)
  obtain ⟨k, rfl⟩ := isConj_iff.1 hα
  -- move the triangle to `a`
  set β1 := k⁻¹ * β * k
  set γ1 := k⁻¹ * γ * k
  have e1 : a * β1 = k⁻¹ * (k * a * k⁻¹ * β) * k := by simp only [β1]; group
  have e2 : a * γ1 = k⁻¹ * (k * a * k⁻¹ * γ) * k := by simp only [γ1]; group
  have e3 : β1 * γ1 = k⁻¹ * (β * γ) * k := by simp only [β1, γ1]; group
  have hβ1 : IsConj a β1 := hβ.trans (isConj_conj_inv k β)
  have hγ1 : IsConj a γ1 := hγ.trans (isConj_conj_inv k γ)
  have c1 : IsConj (a * β1) (a * (g * a * g⁻¹)) := by
    rw [e1]; exact (isConj_conj_inv k _).symm.trans hαβ
  obtain ⟨h, hh, hhb⟩ := horb _ _ hβ1 (isConj_conj g a) c1
  set γ2 := h * γ1 * h⁻¹
  have hha : h * a * h⁻¹ = a := (mem_cent_iff).1 hh
  have hγ2 : IsConj a γ2 := hγ1.trans (isConj_conj h γ1)
  obtain ⟨g', hg'⟩ := isConj_iff.1 hγ2
  have c2 : IsConj (a * γ2) (a * (g * a * g⁻¹)) := by
    have : a * γ2 = h * (a * γ1) * h⁻¹ := by
      calc a * γ2 = (h * a * h⁻¹) * (h * γ1 * h⁻¹) := by rw [hha]
        _ = h * (a * γ1) * h⁻¹ := by group
    rw [this, e2]
    exact (isConj_conj h _).symm.trans ((isConj_conj_inv k _).symm.trans hαγ)
  have c3 : IsConj ((g * a * g⁻¹) * γ2) (a * (g * a * g⁻¹)) := by
    have : (g * a * g⁻¹) * γ2 = h * (β1 * γ1) * h⁻¹ := by
      calc (g * a * g⁻¹) * γ2 = (h * β1 * h⁻¹) * (h * γ1 * h⁻¹) := by rw [hhb]
        _ = h * (β1 * γ1) * h⁻¹ := by group
    rw [this, e3]
    exact (isConj_conj h _).symm.trans ((isConj_conj_inv k _).symm.trans hβγ)
  refine ⟨g, g⁻¹ * g', hq, ?_, Or.inl ?_⟩
  · rw [← hq]
    refine mk_eq_of_isConj horb ?_
    have : g⁻¹ * g' * a * (g⁻¹ * g')⁻¹ = g⁻¹ * γ2 * g := by rw [← hg']; group
    rw [this]
    have : a * (g⁻¹ * γ2 * g) = g⁻¹ * ((g * a * g⁻¹) * γ2) * g := by group
    rw [this]
    exact (isConj_conj_inv g _).symm.trans c3
  · rw [← hq, show g * (g⁻¹ * g') = g' by group]
    refine mk_eq_of_isConj horb ?_
    rw [hg']
    exact c2

/-- The trivial triangle. -/
theorem tri_one {a : G} (ha : a * a = 1) {c : G} (hc : c = 1) : Tri a c :=
  ⟨a, a, a, IsConj.refl a, IsConj.refl a, IsConj.refl a, by rw [ha, hc], by rw [ha, hc],
    by rw [ha, hc]⟩

theorem mul_self_of_isConj {a x : G} (ha : a * a = 1) (hx : IsConj a x) : x * x = 1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 hx
  calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
    _ = 1 := by rw [ha]; group

/-- The short triangle `α, β, α β` when `α β` is conjugate to `a`. -/
theorem tri_two {a α β c : G} (ha : a * a = 1) (hα : IsConj a α) (hβ : IsConj a β)
    (hαβ : IsConj (α * β) c) (hca : IsConj a c) : Tri a c := by
  have hα2 := mul_self_of_isConj ha hα
  have hβ2 := mul_self_of_isConj ha hβ
  refine ⟨α, β, α * β, hα, hβ, hca.trans hαβ.symm, hαβ, ?_, ?_⟩
  · have : β * (α * β) = β * α * β⁻¹ := by
      rw [inv_eq_of_mul_eq_one_right hβ2]; group
    rw [this]; exact (isConj_conj β α).symm.trans (hα.symm.trans hca)
  · have : α * (α * β) = β := by rw [← mul_assoc, hα2, one_mul]
    rw [this]; exact hβ.symm.trans hca

/-- The dihedral triangle `α, β, β α β`: products `α β`, `α β`, `(α β) ^ 2`. -/
theorem tri_dihedral {a α β c : G} (ha : a * a = 1) (hα : IsConj a α) (hβ : IsConj a β)
    (hαβ : IsConj (α * β) c) (hsq : IsConj ((α * β) ^ 2) c) : Tri a c := by
  have hβ2 := mul_self_of_isConj ha hβ
  refine ⟨α, β, β * α * β, hα, hβ, ?_, hαβ, ?_, ?_⟩
  · have : β * α * β = β * α * β⁻¹ := by rw [inv_eq_of_mul_eq_one_right hβ2]
    rw [this]; exact hα.trans (isConj_conj β α)
  · rw [show β * (β * α * β) = (β * β) * α * β by group, hβ2, one_mul]; exact hαβ
  · rw [show α * (β * α * β) = (α * β) ^ 2 by rw [sq]; group]; exact hsq

/-- For an element of order `3`, the square is conjugate to the element (the inverse of `α β` is
`β α = α⁻¹ (α β) α`). -/
theorem isConj_sq_of_order_three {a α β : G} (ha : a * a = 1) (hα : IsConj a α)
    (hβ : IsConj a β) (h3 : orderOf (α * β) = 3) : IsConj ((α * β) ^ 2) (α * β) := by
  have hα2 := mul_self_of_isConj ha hα
  have hβ2 := mul_self_of_isConj ha hβ
  have hp : (α * β) ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one _
  have h1 : (α * β) ^ 2 = (α * β)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]; exact hp
  have e : (α * β) ^ 2 = α * (α * β) * α⁻¹ := by
    rw [h1, mul_inv_rev, inv_eq_of_mul_eq_one_right hα2, inv_eq_of_mul_eq_one_right hβ2,
      ← mul_assoc α α β, hα2, one_mul]
  rw [e]; exact (isConj_conj α _).symm

open Classical in
/-- **Counting.** If the conjugates `γ` of `a` with `a γ ∼ c` are more than half of the class of
`a`, there is a triangle with all products conjugate to `c`. -/
theorem tri_of_card [Finite G] {a c : G}
    (hcard : Nat.card {x : G // IsConj a x} <
      2 * Nat.card {γ : G // IsConj a γ ∧ IsConj (a * γ) c}) : Tri a c := by
  set X := {x : G | IsConj a x}
  set S := {γ : G | IsConj a γ ∧ IsConj (a * γ) c}
  have hX : Nat.card {x : G // IsConj a x} = X.ncard := (Nat.card_coe_set_eq X)
  have hS : Nat.card {γ : G // IsConj a γ ∧ IsConj (a * γ) c} = S.ncard :=
    Nat.card_coe_set_eq S
  rw [hX, hS] at hcard
  obtain ⟨β, hβ⟩ : S.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨g, rfl⟩ := isConj_iff.1 hβ.1
  set T := (fun x => g * x * g⁻¹) '' S
  have hTS : T.ncard = S.ncard :=
    Set.ncard_image_of_injective S (fun x y h => by simpa using h)
  have hSX : S ⊆ X := fun x hx => hx.1
  have hTX : T ⊆ X := by
    rintro _ ⟨x, hx, rfl⟩; exact hx.1.trans (isConj_conj g x)
  have hfin : X.Finite := Set.toFinite X
  have hmeet : ¬ Disjoint S T := by
    intro hd
    have hu := Set.ncard_union_eq hd (hfin.subset hSX) (hfin.subset hTX)
    have hle := Set.ncard_le_ncard (Set.union_subset hSX hTX) hfin
    omega
  rw [Set.not_disjoint_iff] at hmeet
  obtain ⟨γ, hγS, ⟨x, hxS, rfl⟩⟩ := hmeet
  refine ⟨a, g * a * g⁻¹, g * x * g⁻¹, IsConj.refl a, hβ.1, hγS.1, hβ.2, ?_, hγS.2⟩
  have : g * a * g⁻¹ * (g * x * g⁻¹) = g * (a * x) * g⁻¹ := by group
  rw [this]; exact (isConj_conj g _).symm.trans hxS.2

end CFSGOutside.HallPaige.M
