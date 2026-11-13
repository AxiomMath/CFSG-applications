import CFSGOutside.HallPaige.Sporadic.M.Glue

/-!
# The Wilcox criterion from the nine orbitals of the Monster on `2A`

Abstract assembly. The hypotheses are the clauses of the corpus `IsTwoAGraphData a z`
(`CFSG/Monster/Existence/Defs.lean:71`) that are used, together with:

* a triangle for the orbital `c 8` (from counting, `Sporadic/M/Count.lean`);
* a triangle of conjugates of `a` with all products conjugate to `z` (orbital `2B`);
* triangles with all products of order `4`, squares conjugate to `z` (`4A`) and to `a` (`4B`).

The two order-`4` orbitals `c 5`, `c 6` are told apart by the class of the square: the two given
triangles show that both square classes occur, so each order-`4` class `c i` has one square class.
The orbitals `1A`, `2A`, `3A`, `3C`, `5A` have dihedral triangles.
-/

namespace CFSGOutside.HallPaige.M

variable {G : Type*} [Group G]

theorem tri_congr {a c c' : G} (h : IsConj c c') (ht : Tri a c) : Tri a c' := by
  obtain ⟨α, β, γ, h1, h2, h3, h4, h5, h6⟩ := ht
  exact ⟨α, β, γ, h1, h2, h3, h4.trans h, h5.trans h, h6.trans h⟩

theorem orderOf_eq_of_isConj {x y : G} (h : IsConj x y) : orderOf x = orderOf y := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 h
  exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x).symm

theorem isConj_sq {x y : G} (h : IsConj x y) : IsConj (x ^ 2) (y ^ 2) := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 h
  exact isConj_iff.2 ⟨g, (conj_pow).symm⟩

/-- `p` has order `4` and square conjugate to `s`. -/
def SqClass (s p : G) : Prop := orderOf p = 4 ∧ IsConj s (p ^ 2)

/-- A triangle of conjugates of `a` whose three products satisfy `P`. -/
def TriP (a : G) (P : G → Prop) : Prop :=
  ∃ α β γ : G, IsConj a α ∧ IsConj a β ∧ IsConj a γ ∧ P (α * β) ∧ P (β * γ) ∧ P (α * γ)

/-- The suborbit orders of the Monster on `2A`. Corpus: `CFSG.Monster.Existence.suborbitClassOrder`,
CFSG/Monster/Existence/Defs.lean:19. -/
def ord9 : Fin 9 → ℕ := ![1, 2, 2, 3, 3, 4, 4, 5, 6]

section

variable [Finite G] {a z : G} {c : Fin 9 → G}

theorem tri_of_triP {P : G → Prop} {i : Fin 9}
    (hcover : ∀ α β : G, IsConj a α → IsConj a β → ∃ i, IsConj (α * β) (c i))
    (hP : ∀ p j, P p → IsConj p (c j) → j = i) (ht : TriP a P) : Tri a (c i) := by
  obtain ⟨α, β, γ, h1, h2, h3, p1, p2, p3⟩ := ht
  obtain ⟨j1, e1⟩ := hcover α β h1 h2
  obtain ⟨j2, e2⟩ := hcover β γ h2 h3
  obtain ⟨j3, e3⟩ := hcover α γ h1 h3
  rw [hP _ _ p1 e1] at e1
  rw [hP _ _ p2 e2] at e2
  rw [hP _ _ p3 e3] at e3
  exact ⟨α, β, γ, h1, h2, h3, e1, e2, e3⟩

theorem wilcoxCriterion_of_orbitals
    (hsimple : IsSimpleGroup G) (hnc : ∃ x y : G, x * y ≠ y * x)
    (ha : orderOf a = 2) (haz : ¬ IsConj a z)
    (horb : ∀ α β β' : G, IsConj a α → IsConj a β → IsConj a β' → IsConj (α * β) (α * β') →
      ∃ g ∈ Subgroup.centralizer ({α} : Set G), g * β * g⁻¹ = β')
    (hinj : ∀ i j, IsConj (c i) (c j) → i = j) (hc0 : c 0 = 1) (hc1 : IsConj a (c 1))
    (hc2 : IsConj z (c 2)) (hord : ∀ i, orderOf (c i) = ord9 i)
    (hcover : ∀ α β : G, IsConj a α → IsConj a β → ∃ i, IsConj (α * β) (c i))
    (hocc : ∀ i, ∃ α β : G, IsConj a α ∧ IsConj a β ∧ IsConj (α * β) (c i))
    (h8 : Tri a (c 8)) (h2B : TriP a (IsConj z)) (h4A : TriP a (SqClass z))
    (h4B : TriP a (SqClass a)) : WilcoxCriterion G := by
  have ha2 : a * a = 1 := by rw [← sq, ← ha]; exact pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := by rintro rfl; simp at ha
  have hordc : ∀ {p : G} {j : Fin 9}, IsConj p (c j) → orderOf p = ord9 j := fun h =>
    (orderOf_eq_of_isConj h).trans (hord _)
  -- the two order-4 indices
  obtain ⟨α₁, β₁, -, hα₁, hβ₁, -, ⟨o₁, s₁⟩, -, -⟩ := id h4A
  obtain ⟨α₂, β₂, -, hα₂, hβ₂, -, ⟨o₂, s₂⟩, -, -⟩ := id h4B
  obtain ⟨iA, eA⟩ := hcover α₁ β₁ hα₁ hβ₁
  obtain ⟨iB, eB⟩ := hcover α₂ β₂ hα₂ hβ₂
  have hiA := (hordc eA).symm.trans o₁
  have hiB := (hordc eB).symm.trans o₂
  have sqA : ∀ {p : G}, IsConj p (c iA) → IsConj z (p ^ 2) := fun hp =>
    s₁.trans (isConj_sq (eA.trans hp.symm))
  have sqB : ∀ {p : G}, IsConj p (c iB) → IsConj a (p ^ 2) := fun hp =>
    s₂.trans (isConj_sq (eB.trans hp.symm))
  have hne : iA ≠ iB := by
    intro e
    exact haz ((sqB (e ▸ eA)).trans (sqA eA).symm)
  have hiAB : (iA = 5 ∧ iB = 6) ∨ (iA = 6 ∧ iB = 5) := by
    revert hne hiA hiB; fin_cases iA <;> fin_cases iB <;> simp [ord9]
  have four : ∀ {p : G} {j : Fin 9}, orderOf p = 4 → IsConj p (c j) → j = iA ∨ j = iB := by
    intro p j hp hj
    have hj4 := (hordc hj).symm.trans hp
    rcases hiAB with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
      (revert hj4; fin_cases j <;> simp [ord9])
  have hAB : ∀ {p : G} {j : Fin 9}, SqClass a p → IsConj p (c j) → j = iB := by
    intro p j ⟨hp4, hps⟩ hj
    rcases four hp4 hj with rfl | rfl
    · exact absurd (hps.trans (sqA hj).symm) haz
    · rfl
  have hBA : ∀ {p : G} {j : Fin 9}, SqClass z p → IsConj p (c j) → j = iA := by
    intro p j ⟨hp4, hps⟩ hj
    rcases four hp4 hj with rfl | rfl
    · rfl
    · exact absurd (sqB hj |>.trans hps.symm) haz
  have tA : Tri a (c iA) := tri_of_triP hcover (fun p j hp hj => hBA hp hj) h4A
  have tB : Tri a (c iB) := tri_of_triP hcover (fun p j hp hj => hAB hp hj) h4B
  have htri : ∀ i, Tri a (c i) := by
    intro i
    obtain ⟨α, β, hα, hβ, hαβ⟩ := hocc i
    fin_cases i
    · exact tri_one ha2 hc0
    · exact tri_two ha2 hα hβ hαβ hc1
    · obtain ⟨α', β', γ', h1, h2, h3, p1, p2, p3⟩ := h2B
      exact ⟨α', β', γ', h1, h2, h3, p1.symm.trans hc2, p2.symm.trans hc2, p3.symm.trans hc2⟩
    · have h3 : orderOf (α * β) = 3 := hordc hαβ
      exact tri_dihedral ha2 hα hβ hαβ ((isConj_sq_of_order_three ha2 hα hβ h3).trans hαβ)
    · have h3 : orderOf (α * β) = 3 := hordc hαβ
      exact tri_dihedral ha2 hα hβ hαβ ((isConj_sq_of_order_three ha2 hα hβ h3).trans hαβ)
    · rcases hiAB with ⟨h1, -⟩ | ⟨-, h2⟩
      · subst h1; exact tA
      · subst h2; exact tB
    · rcases hiAB with ⟨-, h1⟩ | ⟨h2, -⟩
      · subst h1; exact tB
      · subst h2; exact tA
    · have h5 : orderOf (α * β) = 5 := hordc hαβ
      have hβ2 := mul_self_of_isConj ha2 hβ
      have hsq : (α * β) ^ 2 = α * (β * α * β⁻¹) := by
        rw [inv_eq_of_mul_eq_one_right hβ2, sq]; group
      obtain ⟨j, hj⟩ := hcover α (β * α * β⁻¹) hα (hα.trans (isConj_conj β α))
      rw [← hsq] at hj
      have hj5 : orderOf ((α * β) ^ 2) = 5 := by
        rw [orderOf_pow' _ (by norm_num), h5]; norm_num
      have := (hordc hj).symm.trans hj5
      have hj7 : j = 7 := by revert this; fin_cases j <;> simp [ord9]
      subst hj7
      exact tri_dihedral ha2 hα hβ hαβ hj
    · exact h8
  -- the stabilizer
  set H := Subgroup.centralizer ({a} : Set G)
  have hne : H ≠ ⊤ := by
    intro hH
    have hcen : a ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have : g ∈ H := hH ▸ Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_singleton_iff.1 this)
    haveI := hsimple
    rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with h | h
    · rw [h, Subgroup.mem_bot] at hcen; exact ha1 hcen
    · obtain ⟨x, y, hxy⟩ := hnc
      have : x ∈ Subgroup.center G := h ▸ Subgroup.mem_top x
      exact hxy ((Subgroup.mem_center_iff.1 this y).symm)
  have hgood : IsGood H := by
    obtain ⟨α, β, hα, hβ, hαβ⟩ := hocc 1
    obtain ⟨k, rfl⟩ := isConj_iff.1 hα
    set v := k⁻¹ * β * k
    have hv : IsConj a v := hβ.trans (isConj_conj_inv k β)
    have hav : IsConj (a * v) (c 1) := by
      have : a * v = k⁻¹ * (k * a * k⁻¹ * β) * k := by simp only [v]; group
      rw [this]; exact (isConj_conj_inv k _).symm.trans hαβ
    have hv2 := mul_self_of_isConj ha2 hv
    have ho : orderOf (a * v) = 2 := hordc hav
    have hav2 : (a * v) * (a * v) = 1 := by rw [← sq, ← ho]; exact pow_orderOf_eq_one _
    have hcomm : a * v = v * a := by
      have := eq_inv_of_mul_eq_one_left hav2
      rw [this, mul_inv_rev, inv_eq_of_mul_eq_one_right ha2, inv_eq_of_mul_eq_one_right hv2]
    refine Subgroup.isGood_of_commuting_involutions H (Subgroup.mem_centralizer_singleton_iff.2 rfl)
      (Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm) (by rw [sq]; exact ha2)
      (by rw [sq]; exact hv2) hcomm ha1 ?_ ?_
    · intro h1
      apply ha1
      obtain ⟨g, hg⟩ := isConj_iff.1 hv
      rw [h1] at hg
      calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
        _ = 1 := by rw [hg]; group
    · intro h
      rw [← h, ha2] at ho
      simp at ho
  refine wilcoxCriterion_of_triangles (a := a) (fun β β' hβ hβ' h => horb a β β' (IsConj.refl a)
    hβ hβ' h) hne hgood fun β hβ => ?_
  obtain ⟨i, hi⟩ := hcover a β (IsConj.refl a) hβ
  exact tri_congr hi.symm (htri i)

end

end CFSGOutside.HallPaige.M
