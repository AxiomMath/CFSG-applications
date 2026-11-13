import CFSGOutside.HallPaige.Sporadic.M.Glue

/-!
# Counting a triangle

If `C(a)` acts transitively (by conjugation) on the conjugates `γ` of `a` with `a γ ∼ c`, and this
suborbit has more than half of the class of `a`, there is a triangle with all products conjugate to
`c` (`tri_of_card`). The orbit-stabilizer theorem turns the condition into group orders
(`tri_of_orders`): `|G| · |C(a) ∩ C(β)| < 2 · |C(a)|²`.
-/

namespace CFSGOutside.HallPaige.M

open MulAction

variable {G : Type*} [Group G] [Finite G]

theorem card_class_mul_card_cent (a : G) :
    Nat.card {x : G // IsConj a x} * Nat.card (Subgroup.centralizer ({a} : Set G)) = Nat.card G := by
  have horb : orbit (ConjAct G) a = {x : G | IsConj a x} := by
    ext x
    simp only [mem_orbit_iff, Set.mem_setOf_eq, isConj_iff, ConjAct.smul_def]
    constructor
    · rintro ⟨g, rfl⟩; exact ⟨ConjAct.ofConjAct g, rfl⟩
    · rintro ⟨g, rfl⟩; exact ⟨ConjAct.toConjAct g, by simp⟩
  have hstab : Nat.card (stabilizer (ConjAct G) a) =
      Nat.card (Subgroup.centralizer ({a} : Set G)) := by
    refine Nat.card_congr (Equiv.subtypeEquiv ConjAct.ofConjAct.toEquiv fun g => ?_)
    rw [mem_stabilizer_iff, ConjAct.smul_def, mem_cent_iff]
    rfl
  have h1 := (stabilizer (ConjAct G) a).card_mul_index
  rw [index_stabilizer, horb, hstab] at h1
  have hX : Nat.card {x : G // IsConj a x} = {x : G | IsConj a x}.ncard := Nat.card_coe_set_eq _
  rw [hX, mul_comm, h1]
  exact Nat.card_congr ConjAct.ofConjAct.toEquiv

theorem card_suborbit_mul_card_cent2 {a β₀ c : G} (horb : OrbitClause a) (hβ₀ : IsConj a β₀)
    (hc : IsConj (a * β₀) c) :
    Nat.card {γ : G // IsConj a γ ∧ IsConj (a * γ) c} *
      Nat.card ↥(Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({β₀} : Set G)) =
      Nat.card (Subgroup.centralizer ({a} : Set G)) := by
  set H := Subgroup.centralizer ({a} : Set G)
  letI : MulAction H G :=
    MulAction.compHom G ((ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp H.subtype)
  have hsmul : ∀ (h : H) (x : G), h • x = (h : G) * x * (h : G)⁻¹ := fun h x => by
    show ConjAct.toConjAct (h : G) • x = _
    rw [ConjAct.smul_def]; simp
  have horbit : orbit H β₀ = {γ : G | IsConj a γ ∧ IsConj (a * γ) c} := by
    ext γ
    simp only [mem_orbit_iff, Set.mem_setOf_eq, hsmul]
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨hβ₀.trans (isConj_conj _ _), ?_⟩
      have hha : (h : G) * a * (h : G)⁻¹ = a := mem_cent_iff.1 h.2
      have : a * ((h : G) * β₀ * (h : G)⁻¹) = (h : G) * (a * β₀) * (h : G)⁻¹ := by
        calc a * ((h : G) * β₀ * (h : G)⁻¹)
            = ((h : G) * a * (h : G)⁻¹) * ((h : G) * β₀ * (h : G)⁻¹) := by rw [hha]
          _ = (h : G) * (a * β₀) * (h : G)⁻¹ := by group
      rw [this]; exact (isConj_conj _ _).symm.trans hc
    · rintro ⟨h1, h2⟩
      obtain ⟨g, hg, e⟩ := horb β₀ γ hβ₀ h1 (hc.trans h2.symm)
      exact ⟨⟨g, hg⟩, e⟩
  have hstab : Nat.card (stabilizer H β₀) =
      Nat.card ↥(Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({β₀} : Set G)) := by
    refine Nat.card_congr
      { toFun := fun h => ⟨(h : H), (h : H).2, mem_cent_iff.2 (by
          have := mem_stabilizer_iff.1 h.2; rwa [hsmul] at this)⟩
        invFun := fun g => ⟨⟨g, g.2.1⟩, mem_stabilizer_iff.2 (by
          rw [hsmul]; exact mem_cent_iff.1 g.2.2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have h1 := (stabilizer H β₀).card_mul_index
  rw [index_stabilizer, horbit, hstab] at h1
  have hS : Nat.card {γ : G // IsConj a γ ∧ IsConj (a * γ) c} =
      {γ : G | IsConj a γ ∧ IsConj (a * γ) c}.ncard := Nat.card_coe_set_eq _
  rw [hS, mul_comm, h1]

/-- **Counting, with orders.** -/
theorem tri_of_orders {a β₀ c : G} (horb : OrbitClause a) (hβ₀ : IsConj a β₀)
    (hc : IsConj (a * β₀) c) {N C K : ℕ} (hN : Nat.card G = N)
    (hC : Nat.card (Subgroup.centralizer ({a} : Set G)) = C)
    (hK : Nat.card ↥(Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({β₀} : Set G)) = K)
    (hK0 : 0 < K) (hlt : N * K < 2 * C * C) : Tri a c := by
  refine tri_of_card ?_
  have e1 := card_class_mul_card_cent a
  have e2 := card_suborbit_mul_card_cent2 horb hβ₀ hc
  rw [hN, hC] at e1
  rw [hK, hC] at e2
  set X := Nat.card {x : G // IsConj a x}
  set S := Nat.card {γ : G // IsConj a γ ∧ IsConj (a * γ) c}
  by_contra hle
  push_neg at hle
  have : X * C * K ≥ 2 * S * K * C := by
    have := Nat.mul_le_mul_right (C * K) hle
    nlinarith
  nlinarith
end CFSGOutside.HallPaige.M
