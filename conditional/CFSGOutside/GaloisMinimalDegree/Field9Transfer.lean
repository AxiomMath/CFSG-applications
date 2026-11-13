import CFSGOutside.GaloisMinimalDegree.Field9

open scoped MatrixGroups

namespace CFSGOutside.GaloisMinimalDegree

abbrev TupG (F : Type) := F × F × F × F

def mulG {F : Type} [Field F] (x y : TupG F) : TupG F :=
  (x.1 * y.1 + x.2.1 * y.2.2.1, x.1 * y.2.1 + x.2.1 * y.2.2.2,
    x.2.2.1 * y.1 + x.2.2.2 * y.2.2.1, x.2.2.1 * y.2.1 + x.2.2.2 * y.2.2.2)

def invG {F : Type} [Field F] (x : TupG F) : TupG F := (x.2.2.2, -x.2.1, -x.2.2.1, x.1)

def tupG {F : Type} [Field F] (g : Matrix.SpecialLinearGroup (Fin 2) F) : TupG F :=
  (g 0 0, g 0 1, g 1 0, g 1 1)

lemma tupG_mul {F : Type} [Field F] (g h : Matrix.SpecialLinearGroup (Fin 2) F) :
    tupG (g * h) = mulG (tupG g) (tupG h) := by
  simp [tupG, mulG, Matrix.mul_apply, Fin.sum_univ_two]

lemma tupG_inv {F : Type} [Field F] (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    tupG g⁻¹ = invG (tupG g) := by
  simp [tupG, invG, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

lemma card_of_list {F : Type} [Field F] (L : List (TupG F)) (hnd : L.Nodup)
    (hdet : ∀ t ∈ L, t.1 * t.2.2.2 - t.2.1 * t.2.2.1 = 1)
    (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) (hS : ∀ g, g ∈ S ↔ tupG g ∈ L) :
    Nat.card S = L.length := by
  classical
  rw [← List.toFinset_card_of_nodup hnd, ← Nat.card_eq_finsetCard]
  refine Nat.card_congr
    { toFun := fun g => ⟨tupG g.1, List.mem_toFinset.2 ((hS _).1 g.2)⟩
      invFun := fun t => ⟨⟨!![t.1.1, t.1.2.1; t.1.2.2.1, t.1.2.2.2], by
        have := hdet t.1 (List.mem_toFinset.1 t.2)
        simpa [Matrix.det_fin_two] using this⟩, (hS _).2 (by
          have h : t.1 ∈ L := List.mem_toFinset.1 t.2
          convert h using 1
          simp [tupG, Prod.ext_iff])⟩
      left_inv := fun g => by
        apply Subtype.ext
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp [tupG]
      right_inv := fun t => by
        apply Subtype.ext
        simp [tupG] }

section Embedding

variable {F : Type} [Field F] [CharP F 3] {i : F}

def cast3 (F : Type) [Field F] [CharP F 3] : ZMod 3 →+* F := ZMod.castHom (dvd_refl 3) F

def embZ (i : F) (x : ZMod 3 × ZMod 3) : F := cast3 F x.1 + cast3 F x.2 * i

def embP (i : F) (x : P9) : F := embZ i ((x.1 : ZMod 3), (x.2 : ZMod 3))

def embQ (i : F) (q : Q9) : TupG F :=
  (embP i q.1, embP i q.2.1, embP i q.2.2.1, embP i q.2.2.2)

lemma three_F : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3

lemma cast3_two : cast3 F 2 = -1 := by
  rw [map_ofNat]
  linear_combination (three_F (F := F))

lemma embP_pm (hi : i ^ 2 = -1) (x y : P9) : embP i (pm x y) = embP i x * embP i y := by
  simp only [embP, embZ, pm, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    map_add, map_mul, map_ofNat]
  linear_combination (cast3 F (x.2 : ZMod 3) * cast3 F (y.2 : ZMod 3)) * (three_F (F := F)) -
    (cast3 F (x.2 : ZMod 3) * cast3 F (y.2 : ZMod 3)) * hi

lemma embP_pa (x y : P9) : embP i (pa x y) = embP i x + embP i y := by
  simp only [embP, embZ, pa, ZMod.natCast_mod, Nat.cast_add, map_add]; ring

lemma embP_pn (x : P9) : embP i (pn x) = -embP i x := by
  simp only [embP, embZ, pn, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_ofNat, map_mul, map_ofNat]
  linear_combination (cast3 F (x.1 : ZMod 3) + cast3 F (x.2 : ZMod 3) * i) * (three_F (F := F))

lemma embQ_mul (hi : i ^ 2 = -1) (x y : Q9) :
    embQ i (mulQ x y) = mulG (embQ i x) (embQ i y) := by
  simp only [embQ, mulQ, mulG, embP_pm hi, embP_pa]

lemma embQ_inv (x : Q9) : embQ i (invQ x) = invG (embQ i x) := by
  simp only [embQ, invQ, invG, embP_pn]

lemma embQ_det (hi : i ^ 2 = -1) (q : Q9) (h : detQ q = (1, 0)) :
    (embQ i q).1 * (embQ i q).2.2.2 - (embQ i q).2.1 * (embQ i q).2.2.1 = 1 := by
  have := congrArg (embP i) h
  simp only [detQ, embP_pa, embP_pn, embP_pm hi] at this
  have e1 : embP i ((1, 0) : P9) = 1 := by simp [embP, embZ]
  rw [e1] at this
  simp only [embQ]
  linear_combination this

lemma sq_add_sq_zero : ∀ a b : ZMod 3, a ^ 2 + b ^ 2 = 0 → b = 0 := by decide

lemma embZ_injective (hi : i ^ 2 = -1) : Function.Injective (embZ (F := F) i) := by
  intro x y h
  have key : cast3 F (x.1 - y.1) + cast3 F (x.2 - y.2) * i = 0 := by
    simp only [embZ] at h
    simp only [map_sub]
    linear_combination h
  have hb : x.2 - y.2 = 0 := by
    apply sq_add_sq_zero (x.1 - y.1)
    apply (cast3 F).injective
    have hc : cast3 F (x.1 - y.1) = -(cast3 F (x.2 - y.2) * i) := by linear_combination key
    simp only [map_add, map_pow, map_zero, hc]
    linear_combination (cast3 F (x.2 - y.2)) ^ 2 * hi
  rw [hb, map_zero, zero_mul, add_zero] at key
  have ha : x.1 - y.1 = 0 := (cast3 F).injective (by rw [key, map_zero])
  exact Prod.ext (sub_eq_zero.1 ha) (sub_eq_zero.1 hb)

lemma embP_inj_of_lt (hi : i ^ 2 = -1) {x y : P9} (hx1 : x.1 < 3) (hx2 : x.2 < 3)
    (hy1 : y.1 < 3) (hy2 : y.2 < 3) (h : embP i x = embP i y) : x = y := by
  have := embZ_injective hi h
  simp only [Prod.mk.injEq, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hx1,
    Nat.mod_eq_of_lt hx2, Nat.mod_eq_of_lt hy1, Nat.mod_eq_of_lt hy2] at this
  exact Prod.ext this.1 this.2

lemma embQ_inj_on (hi : i ^ 2 = -1) : Set.InjOn (embQ (F := F) i) {t | t ∈ q9list} := by
  intro x hx y hy h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := q9_lt x hx
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := q9_lt y hy
  simp only [embQ, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact Prod.ext (embP_inj_of_lt hi a1 a2 b1 b2 h1)
    (Prod.ext (embP_inj_of_lt hi a3 a4 b3 b4 h2)
      (Prod.ext (embP_inj_of_lt hi a5 a6 b5 b6 h3) (embP_inj_of_lt hi a7 a8 b7 b8 h4)))

def H9 (hi : i ^ 2 = -1) : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) where
  carrier := {g | tupG g ∈ q9list.map (embQ i)}
  one_mem' := by
    refine List.mem_map.2 ⟨_, q9_one, ?_⟩
    simp [tupG, embQ, embP, embZ]
  mul_mem' := by
    intro a b ha hb
    obtain ⟨x, hx, ex⟩ := List.mem_map.1 ha
    obtain ⟨y, hy, ey⟩ := List.mem_map.1 hb
    refine List.mem_map.2 ⟨mulQ x y, q9_mul x hx y hy, ?_⟩
    rw [embQ_mul hi, ex, ey, tupG_mul]
  inv_mem' := by
    intro a ha
    obtain ⟨x, hx, ex⟩ := List.mem_map.1 ha
    refine List.mem_map.2 ⟨invQ x, q9_inv x hx, ?_⟩
    rw [embQ_inv, ex, tupG_inv]

lemma card_H9 (hi : i ^ 2 = -1) : Nat.card (H9 hi) = 120 := by
  rw [card_of_list (q9list.map (embQ i)) ?_ ?_ (H9 hi) (fun g => Iff.rfl), List.length_map, q9_length]
  · exact q9_nodup.map_on (fun x hx y hy h => embQ_inj_on hi hx hy h)
  · intro t ht
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ht
    exact embQ_det hi x (q9_det x hx)

lemma center_le_H9 (hi : i ^ 2 = -1) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) ≤ H9 hi := by
  intro z hz
  obtain ⟨r, hr, hz'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have e : ∀ a b, z a b = Matrix.scalar (Fin 2) r a b := fun a b => by rw [hz']
  have hfac : (r - 1) * (r + 1) = 0 := by linear_combination hr2
  show tupG z ∈ q9list.map (embQ i)
  rcases mul_eq_zero.1 hfac with h | h
  · have hr1 : r = 1 := sub_eq_zero.1 h
    refine List.mem_map.2 ⟨_, q9_one, ?_⟩
    simp [tupG, embQ, embP, embZ, e, Matrix.scalar_apply, hr1]
  · have hr1 : r = -1 := eq_neg_of_add_eq_zero_left h
    refine List.mem_map.2 ⟨_, q9_neg_one, ?_⟩
    simp [tupG, embQ, cast3_two, embP, embZ, e, Matrix.scalar_apply, hr1]

end Embedding

lemma charP_three_of_card_nine {F : Type} [Field F] [Finite F] (hF : Nat.card F = 9) :
    CharP F 3 := by
  have := Fintype.ofFinite F
  haveI := ringChar.charP F
  obtain ⟨n, hp, hq⟩ := FiniteField.card F (ringChar F)
  rw [← Nat.card_eq_fintype_card, hF] at hq
  have hdvd : ringChar F ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, hq]
    exact dvd_pow_self _ n.ne_zero
  have h3 : ringChar F = 3 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow hdvd)
  exact CharP.congr (ringChar F) h3

theorem exists_index_six {F : Type} [Field F] [Finite F] (hF : Nat.card F = 9) :
    ∃ H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F), H ≠ ⊤ ∧ H.index = 6 := by
  haveI := charP_three_of_card_nine hF
  have := Fintype.ofFinite F
  obtain ⟨i, hi'⟩ := FiniteField.isSquare_neg_one_iff.2
    (by rw [← Nat.card_eq_fintype_card, hF]; norm_num : Fintype.card F % 4 ≠ 3)
  have hi : i ^ 2 = -1 := by rw [sq, hi']
  have hidx : ((H9 hi).map (QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))).index = (H9 hi).index := by
    rw [Subgroup.index_map, QuotientGroup.ker_mk', sup_eq_left.2 (center_le_H9 hi),
      (MonoidHom.range_eq_top).2 (QuotientGroup.mk'_surjective _), Subgroup.index_top, mul_one]
  have hcard := Subgroup.index_mul_card (H9 hi)
  rw [card_H9 hi, card_sl2 F, hF] at hcard
  have h6 : (H9 hi).index = 6 := by omega
  refine ⟨(H9 hi).map (QuotientGroup.mk' _), ?_, by rw [hidx, h6]⟩
  intro h
  have := congrArg Subgroup.index h
  rw [hidx, h6, Subgroup.index_top] at this
  omega

end CFSGOutside.GaloisMinimalDegree
