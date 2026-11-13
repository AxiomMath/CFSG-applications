import Mathlib
open scoped MatrixGroups

namespace CFSGOutside.GiuliettiKorchmaros.PSL23

/-- normalizing a nonzero vector to one of the four points of the projective line -/
def normFun (x y : ZMod 3) : Fin 4 :=
  if x = 1 then (if y = 0 then 0 else if y = 1 then 2 else 3)
  else if x = 0 then 1
  else (if y = 0 then 0 else if y = 1 then 3 else 2)

def repX : Fin 4 → ZMod 3 := ![1, 0, 1, 1]
def repY : Fin 4 → ZMod 3 := ![0, 1, 1, 2]

def actE (a b c d : ZMod 3) (i : Fin 4) : Fin 4 :=
  normFun (a * repX i + b * repY i) (c * repX i + d * repY i)

lemma actE_mul : ∀ a b c d a' b' c' d' : ZMod 3, a*d - b*c = 1 → a'*d'-b'*c' = 1 → ∀ i : Fin 4,
    actE (a*a'+b*c') (a*b'+b*d') (c*a'+d*c') (c*b'+d*d') i = actE a b c d (actE a' b' c' d' i) := by
  decide +kernel

lemma actE_one : ∀ i : Fin 4, actE 1 0 0 1 i = i := by decide +kernel

lemma actE_ker : ∀ a b c d : ZMod 3, a*d - b*c = 1 →
    ((∀ i, actE a b c d i = i) ↔ (b = 0 ∧ c = 0 ∧ a = d)) := by decide +kernel

lemma sq_one : ∀ a d : ZMod 3, a = d → a * d = 1 → a = 1 ∨ a = -1 := by decide +kernel


/-- action of a matrix on the four points -/
def act (M : SL(2, ZMod 3)) (i : Fin 4) : Fin 4 :=
  actE (M 0 0) (M 0 1) (M 1 0) (M 1 1) i

lemma det_ent (M : SL(2, ZMod 3)) : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
  have := M.2
  rw [Matrix.det_fin_two] at this
  exact this

lemma act_mul (M N : SL(2, ZMod 3)) (i : Fin 4) : act (M * N) i = act M (act N i) := by
  have h := actE_mul _ _ _ _ _ _ _ _ (det_ent M) (det_ent N) i
  simp only [act]
  rw [← h]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma act_one (i : Fin 4) : act 1 i = i := by
  simpa [act] using actE_one i

def fperm (M : SL(2, ZMod 3)) : Equiv.Perm (Fin 4) where
  toFun := act M
  invFun := act M⁻¹
  left_inv i := by rw [← act_mul, inv_mul_cancel, act_one]
  right_inv i := by rw [← act_mul, mul_inv_cancel, act_one]

def f : SL(2, ZMod 3) →* Equiv.Perm (Fin 4) where
  toFun := fperm
  map_one' := Equiv.ext fun i => act_one i
  map_mul' M N := Equiv.ext fun i => act_mul M N i

lemma mem_ker_iff (M : SL(2, ZMod 3)) : M ∈ f.ker ↔ M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 0 0 = M 1 1 := by
  rw [MonoidHom.mem_ker, ← actE_ker _ _ _ _ (det_ent M)]
  constructor
  · intro h i
    have := congrArg (fun p => p i) h
    exact this
  · intro h
    exact Equiv.ext fun i => h i

lemma ker_eq_center : f.ker = Subgroup.center SL(2, ZMod 3) := by
  ext M
  rw [mem_ker_iff, Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨M 0 0, ?_, ?_⟩
    · have := det_ent M
      rw [h1, h2, ← h3] at this
      rw [Fintype.card_fin]; linear_combination this
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [h1, h2, h3]
  · rintro ⟨r, hr, hM⟩
    have e : ∀ i j, (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) i j = Matrix.scalar (Fin 2) r i j := by
      intro i j; rw [hM]
    refine ⟨?_, ?_, ?_⟩
    · rw [e]; simp
    · rw [e]; simp
    · rw [e, e]; simp

lemma card_ker : Nat.card f.ker = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, f.ker.one_mem⟩, ⟨-1, ?_⟩, ?_, ?_⟩
  · rw [mem_ker_iff]; simp
  · intro h
    have := congrArg (fun x : f.ker => (x.1 : SL(2, ZMod 3)) 0 0) h
    simp at this
    revert this; decide
  · ext ⟨g, hg⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rw [mem_ker_iff] at hg
    obtain ⟨h1, h2, h3⟩ := hg
    have hd := det_ent g
    rw [h1, h2, ← h3] at hd
    rcases sq_one (g 0 0) (g 0 0) rfl (by linear_combination hd) with h | h
    · left
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h1, h2, ← h3, h]
    · right
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_neg, h1, h2, ← h3, h] <;> rfl

lemma card_SL : Nat.card SL(2, ZMod 3) = 24 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

lemma range_eq : f.range = alternatingGroup (Fin 4) := by
  apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
  have h1 := Subgroup.index_mul_card f.range
  have h2 : Nat.card f.range = 12 := by
    have := Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    rw [← this]
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [card_SL, card_ker] at h3
    omega
  have h4 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by rw [Nat.card_perm, Nat.card_eq_fintype_card]; simp [Nat.factorial]
  rw [h2, h4] at h1
  omega

theorem nonempty_psl23_mulEquiv_alternating_four : Nonempty (PSL(2, ZMod 3) ≃* alternatingGroup (Fin 4)) := by
  refine ⟨(QuotientGroup.quotientMulEquivOfEq ker_eq_center.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr range_eq))⟩


/-- An injective hom from a group of order 12 to `S₄` has image `A₄`. -/
lemma nonempty_of_injective {H : Type*} [Group H] (hcard : Nat.card H = 12)
    (φ : H →* Equiv.Perm (Fin 4)) (hφ : Function.Injective φ) :
    Nonempty (H ≃* alternatingGroup (Fin 4)) := by
  have hr : φ.range = alternatingGroup (Fin 4) := by
    apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
    have h1 := Subgroup.index_mul_card φ.range
    have h2 : Nat.card φ.range = 12 := by
      rw [← hcard]; exact (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm
    have h4 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
      rw [Nat.card_perm, Nat.card_eq_fintype_card]; simp [Nat.factorial]
    rw [h2, h4] at h1
    omega
  exact ⟨(MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hr)⟩

theorem nonempty_mulEquiv_alternating_four {H : Type*} [Group H] [Finite H] (hcard : Nat.card H = 12)
    (V : Subgroup H) (hVn : V.Normal) (hV : Nat.card V = 4)
    (hC : Subgroup.centralizer (V : Set H) = V) :
    Nonempty (H ≃* alternatingGroup (Fin 4)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 H) := inferInstance
  have hP : Nat.card P = 3 := by
    rw [Sylow.card_eq_multiplicity, hcard]
    have : (12 : ℕ).factorization 3 = 1 := by
      have : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
      rw [this, Nat.factorization_mul (by norm_num) (by norm_num)]
      simp [Nat.Prime.factorization_self Nat.prime_three,
        Nat.Prime.factorization_pow Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd (show ¬ 3 ∣ 4 by norm_num)]
    rw [this]; norm_num
  set Q : Subgroup H := (P : Subgroup H) with hQ
  -- P is not normal
  have hnn : ¬ Q.Normal := by
    intro hQn
    have hinf : Q ⊓ V = ⊥ := by
      rw [Subgroup.eq_bot_iff_card]
      have d1 : Nat.card (Q ⊓ V : Subgroup H) ∣ 3 := by
        rw [← hP]; exact Subgroup.card_dvd_of_le inf_le_left
      have d2 : Nat.card (Q ⊓ V : Subgroup H) ∣ 4 := by
        rw [← hV]; exact Subgroup.card_dvd_of_le inf_le_right
      have := Nat.dvd_gcd d1 d2
      simpa using this
    have hle : Q ≤ V := by
      intro x hx
      rw [← hC, Subgroup.mem_centralizer_iff]
      intro v hv
      have h1 : x * v * x⁻¹ * v⁻¹ ∈ Q := by
        have := Q.mul_mem hx (hQn.conj_mem x⁻¹ (Q.inv_mem hx) v)
        simpa [mul_assoc] using this
      have h2 : x * v * x⁻¹ * v⁻¹ ∈ V := by
        exact V.mul_mem (hVn.conj_mem v hv x) (V.inv_mem hv)
      have h3 : x * v * x⁻¹ * v⁻¹ ∈ Q ⊓ V := ⟨h1, h2⟩
      rw [hinf, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
      exact h3.symm
    have hQ1 : Q = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [← hinf]
      exact ⟨hx, hle hx⟩
    have : Nat.card Q = 1 := by rw [hQ1]; simp
    omega
  have hidx : Q.index = 4 := by
    have := Subgroup.index_mul_card Q
    rw [hcard, hP] at this
    omega
  haveI : Finite (H ⧸ Q) := Subgroup.finite_quotient_of_finiteIndex
  have hcq : Nat.card (H ⧸ Q) = 4 := by rw [← Subgroup.index, hidx]
  let e : H ⧸ Q ≃ Fin 4 := (Finite.equivFin (H ⧸ Q)).trans (finCongr hcq)
  let φ : H →* Equiv.Perm (Fin 4) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom H (H ⧸ Q))
  have hker : (MulAction.toPermHom H (H ⧸ Q)).ker = ⊥ := by
    set K := (MulAction.toPermHom H (H ⧸ Q)).ker with hK
    have hKn : K.Normal := MonoidHom.normal_ker _
    have hKle : K ≤ Q := by
      rw [hK, ← Subgroup.normalCore_eq_ker]; exact Subgroup.normalCore_le Q
    have hKd : Nat.card K ∣ 3 := by rw [← hP]; exact Subgroup.card_dvd_of_le hKle
    rcases (Nat.dvd_prime Nat.prime_three).1 hKd with h | h
    · exact (Subgroup.eq_bot_iff_card K).2 h
    · exfalso
      have : K = Q := Subgroup.eq_of_le_of_card_ge hKle (by rw [h, hP])
      exact hnn (this ▸ hKn)
  refine nonempty_of_injective hcard φ ?_
  intro a b hab
  have : (MulAction.toPermHom H (H ⧸ Q)) a = (MulAction.toPermHom H (H ⧸ Q)) b :=
    e.permCongrHom.injective hab
  rw [← inv_mul_eq_one, ← map_inv, ← map_mul] at this
  have h : a⁻¹ * b ∈ (MulAction.toPermHom H (H ⧸ Q)).ker := this
  rw [hker, Subgroup.mem_bot, inv_mul_eq_one] at h
  exact h


/-- A finite group of order 12 with a normal subgroup `V` of order 4 that is its own centralizer is
isomorphic to `PSL(2,3)`. -/
theorem nonempty_mulEquiv_psl23 {H : Type*} [Group H] [Finite H] (hcard : Nat.card H = 12)
    (V : Subgroup H) (hVn : V.Normal) (hV : Nat.card V = 4)
    (hC : Subgroup.centralizer (V : Set H) = V) :
    Nonempty (H ≃* PSL(2, ZMod 3)) := by
  obtain ⟨e1⟩ := nonempty_mulEquiv_alternating_four hcard V hVn hV hC
  obtain ⟨e2⟩ := nonempty_psl23_mulEquiv_alternating_four
  exact ⟨e1.trans e2.symm⟩

end CFSGOutside.GiuliettiKorchmaros.PSL23
