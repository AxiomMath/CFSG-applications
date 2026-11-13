import CFSGOutside.GaloisMinimalDegree.Main

open scoped MatrixGroups

namespace CFSGOutside.GaloisMinimalDegree

abbrev Tup (p : ℕ) := ZMod p × ZMod p × ZMod p × ZMod p

def tupOf {p : ℕ} (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) : Tup p :=
  (g 0 0, g 0 1, g 1 0, g 1 1)

def mulT {p : ℕ} (x y : Tup p) : Tup p :=
  (x.1 * y.1 + x.2.1 * y.2.2.1, x.1 * y.2.1 + x.2.1 * y.2.2.2,
    x.2.2.1 * y.1 + x.2.2.2 * y.2.2.1, x.2.2.1 * y.2.1 + x.2.2.2 * y.2.2.2)

def invT {p : ℕ} (x : Tup p) : Tup p := (x.2.2.2, -x.2.1, -x.2.2.1, x.1)

structure SubgroupData (p : ℕ) where
  elems : List (Tup p)
  nodup : elems.Nodup
  det : ∀ t ∈ elems, t.1 * t.2.2.2 - t.2.1 * t.2.2.1 = 1
  one : ((1 : ZMod p), (0 : ZMod p), (0 : ZMod p), (1 : ZMod p)) ∈ elems
  mul : ∀ x ∈ elems, ∀ y ∈ elems, mulT x y ∈ elems
  inv : ∀ x ∈ elems, invT x ∈ elems
  center : ∀ r : ZMod p, r ^ 2 = 1 → (r, (0 : ZMod p), (0 : ZMod p), r) ∈ elems

variable {p : ℕ}

def SubgroupData.subgroup (D : SubgroupData p) : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) where
  carrier := {g | tupOf g ∈ D.elems}
  one_mem' := by simpa [tupOf] using D.one
  mul_mem' := by
    intro a b ha hb
    have := D.mul _ ha _ hb
    simpa [tupOf, mulT, Matrix.mul_apply, Fin.sum_univ_two] using this
  inv_mem' := by
    intro a ha
    have := D.inv _ ha
    simpa [tupOf, invT, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two] using this

lemma SubgroupData.card_subgroup (D : SubgroupData p) :
    Nat.card D.subgroup = D.elems.length := by
  classical
  rw [← List.toFinset_card_of_nodup D.nodup, ← Nat.card_eq_finsetCard]
  refine Nat.card_congr
    { toFun := fun g => ⟨tupOf g.1, List.mem_toFinset.2 g.2⟩
      invFun := fun t => ⟨⟨!![t.1.1, t.1.2.1; t.1.2.2.1, t.1.2.2.2], by
        have := D.det t.1 (List.mem_toFinset.1 t.2)
        simpa [Matrix.det_fin_two] using this⟩, by
          have h : t.1 ∈ D.elems := List.mem_toFinset.1 t.2
          change tupOf _ ∈ D.elems
          convert h using 1
          rfl⟩
      left_inv := fun g => by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp [tupOf]
      right_inv := fun t => by
        apply Subtype.ext
        simp [tupOf] }

lemma SubgroupData.center_le (D : SubgroupData p) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) ≤ D.subgroup := by
  intro z hz
  obtain ⟨r, hr, hz'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  have h := D.center r (by simpa using hr)
  have e : ∀ i j, z i j = Matrix.scalar (Fin 2) r i j := fun i j => by rw [hz']
  show tupOf z ∈ D.elems
  simpa [tupOf, e, Matrix.scalar_apply] using h

theorem SubgroupData.exists_psl_index (D : SubgroupData p) [Fact p.Prime]
    (hlen : D.elems.length = p * p - 1) :
    ∃ H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)),
      H ≠ ⊤ ∧ H.index = p := by
  have hp := (inferInstance : Fact p.Prime).out.two_le
  refine ⟨D.subgroup.map (QuotientGroup.mk' _), ?_⟩
  have hidx : (D.subgroup.map (QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))))).index = D.subgroup.index := by
    rw [Subgroup.index_map, QuotientGroup.ker_mk', sup_eq_left.2 D.center_le,
      (MonoidHom.range_eq_top).2 (QuotientGroup.mk'_surjective _), Subgroup.index_top, mul_one]
  have hcard := Subgroup.index_mul_card D.subgroup
  rw [D.card_subgroup, hlen, card_sl2] at hcard
  have hpos : 0 < p * p - 1 := by
    have : 4 ≤ p * p := by nlinarith
    omega
  have hcard' : D.subgroup.index = p := by
    have h2 : D.subgroup.index * (p * p - 1) = p * (p * p - 1) := by
      simpa [Nat.card_eq_fintype_card, ZMod.card] using hcard
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  rw [hidx, hcard']
  refine ⟨fun h => ?_, rfl⟩
  have := congrArg Subgroup.index h
  rw [hidx, hcard', Subgroup.index_top] at this
  omega



abbrev NTup := ℕ × ℕ × ℕ × ℕ

def toTup (p : ℕ) (t : NTup) : Tup p := ((t.1 : ZMod p), (t.2.1 : ZMod p), (t.2.2.1 : ZMod p), (t.2.2.2 : ZMod p))

def mulN (p : ℕ) (x y : NTup) : NTup :=
  ((x.1 * y.1 + x.2.1 * y.2.2.1) % p, (x.1 * y.2.1 + x.2.1 * y.2.2.2) % p,
    (x.2.2.1 * y.1 + x.2.2.2 * y.2.2.1) % p, (x.2.2.1 * y.2.1 + x.2.2.2 * y.2.2.2) % p)

def invN (p : ℕ) (x : NTup) : NTup := (x.2.2.2, (p - x.2.1) % p, (p - x.2.2.1) % p, x.1)

structure NatData (p : ℕ) where
  elems : List NTup
  one_lt : 1 < p
  lt : ∀ t ∈ elems, t.1 < p ∧ t.2.1 < p ∧ t.2.2.1 < p ∧ t.2.2.2 < p
  nodup : elems.Nodup
  det : ∀ t ∈ elems, (t.1 * t.2.2.2) % p = (t.2.1 * t.2.2.1 + 1) % p
  one : ((1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ)) ∈ elems
  mul : ∀ x ∈ elems, ∀ y ∈ elems, mulN p x y ∈ elems
  inv : ∀ x ∈ elems, invN p x ∈ elems
  center : ∀ r ∈ List.range p, (r * r) % p = 1 → (r, 0, 0, r) ∈ elems

lemma toTup_mulN (p : ℕ) (x y : NTup) : toTup p (mulN p x y) = mulT (toTup p x) (toTup p y) := by
  simp [toTup, mulN, mulT, ZMod.natCast_mod]

lemma toTup_invN (p : ℕ) (x : NTup) (h1 : x.2.1 < p) (h2 : x.2.2.1 < p) :
    toTup p (invN p x) = invT (toTup p x) := by
  simp [toTup, invN, invT, ZMod.natCast_mod, Nat.cast_sub h1.le, Nat.cast_sub h2.le]

def NatData.toData {p : ℕ} (D : NatData p) : SubgroupData p :=
  haveI : NeZero p := ⟨by have := D.one_lt; omega⟩
  { elems := D.elems.map (toTup p)
    nodup := by
      refine D.nodup.map_on ?_
      intro x hx y hy hxy
      obtain ⟨a1, a2, a3, a4⟩ := D.lt x hx
      obtain ⟨b1, b2, b3, b4⟩ := D.lt y hy
      simp only [toTup, Prod.mk.injEq] at hxy
      obtain ⟨h1, h2, h3, h4⟩ := hxy
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt a1, Nat.mod_eq_of_lt b1] at h1
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt a2, Nat.mod_eq_of_lt b2] at h2
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt a3, Nat.mod_eq_of_lt b3] at h3
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt a4, Nat.mod_eq_of_lt b4] at h4
      ext <;> assumption
    det := by
      intro t ht
      obtain ⟨t, htm, rfl⟩ := List.mem_map.1 ht
      have h := (ZMod.natCast_eq_natCast_iff' _ _ p).2 (D.det t htm)
      push_cast at h
      simp only [toTup]
      linear_combination h
    one := by
      have := List.mem_map_of_mem (f := toTup p) D.one
      simpa [toTup] using this
    mul := by
      intro x hx y hy
      obtain ⟨x, hxm, rfl⟩ := List.mem_map.1 hx
      obtain ⟨y, hym, rfl⟩ := List.mem_map.1 hy
      rw [← toTup_mulN]
      exact List.mem_map_of_mem (f := toTup p) (D.mul x hxm y hym)
    inv := by
      intro x hx
      obtain ⟨x, hxm, rfl⟩ := List.mem_map.1 hx
      obtain ⟨_, a2, a3, _⟩ := D.lt x hxm
      rw [← toTup_invN p x a2 a3]
      exact List.mem_map_of_mem (f := toTup p) (D.inv x hxm)
    center := by
      intro r hr
      have hrv : ((r.val : ℕ) : ZMod p) = r := ZMod.natCast_zmod_val r
      have hlt : r.val < p := ZMod.val_lt r
      have h : (r.val * r.val) % p = 1 := by
        have h1 : (((r.val * r.val : ℕ)) : ZMod p) = ((1 : ℕ) : ZMod p) := by
          push_cast
          rw [hrv]; linear_combination hr
        rw [ZMod.natCast_eq_natCast_iff'] at h1
        rwa [Nat.mod_eq_of_lt D.one_lt] at h1
      have := List.mem_map_of_mem (f := toTup p) (D.center r.val (List.mem_range.2 hlt) h)
      simpa [toTup, hrv] using this }

theorem NatData.exists_psl_index {p : ℕ} (D : NatData p) [Fact p.Prime]
    (hlen : D.elems.length = p * p - 1) :
    ∃ H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)),
      H ≠ ⊤ ∧ H.index = p :=
  D.toData.exists_psl_index (by simpa [NatData.toData] using hlen)

def nlist2 : List NTup :=
  [(0, 1, 1, 1), (1, 0, 0, 1), (1, 1, 1, 0)]

def ndata2 : NatData 2 where
  elems := nlist2
  one_lt := by norm_num
  lt := by decide +kernel
  nodup := by decide +kernel
  det := by decide +kernel
  one := by decide +kernel
  mul := by decide +kernel
  inv := by decide +kernel
  center := by decide +kernel

theorem exists_index_2 :
    ∃ H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2)), H ≠ ⊤ ∧ H.index = 2 :=
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  ndata2.exists_psl_index (by decide +kernel)

def nlist3 : List NTup :=
  [(0, 1, 2, 0), (0, 2, 1, 0), (1, 0, 0, 1), (1, 1, 1, 2), (1, 2, 2, 2), (2, 0, 0, 2), (2, 1, 1, 1), (2, 2, 2, 1)]

def ndata3 : NatData 3 where
  elems := nlist3
  one_lt := by norm_num
  lt := by decide +kernel
  nodup := by decide +kernel
  det := by decide +kernel
  one := by decide +kernel
  mul := by decide +kernel
  inv := by decide +kernel
  center := by decide +kernel

theorem exists_index_3 :
    ∃ H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 3)), H ≠ ⊤ ∧ H.index = 3 :=
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  ndata3.exists_psl_index (by decide +kernel)

def nlist5 : List NTup :=
  [(0, 1, 4, 0), (0, 2, 2, 0), (0, 3, 3, 0), (0, 4, 1, 0), (1, 0, 0, 1), (1, 1, 2, 3), (1, 2, 1, 3), (1, 3, 4, 3), (1, 4, 3, 3), (2, 0, 0, 3), (2, 1, 2, 4), (2, 2, 1, 4), (2, 3, 4, 4), (2, 4, 3, 4), (3, 0, 0, 2), (3, 1, 2, 1), (3, 2, 1, 1), (3, 3, 4, 1), (3, 4, 3, 1), (4, 0, 0, 4), (4, 1, 2, 2), (4, 2, 1, 2), (4, 3, 4, 2), (4, 4, 3, 2)]

def ndata5 : NatData 5 where
  elems := nlist5
  one_lt := by norm_num
  lt := by decide +kernel
  nodup := by decide +kernel
  det := by decide +kernel
  one := by decide +kernel
  mul := by decide +kernel
  inv := by decide +kernel
  center := by decide +kernel

theorem exists_index_5 :
    ∃ H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)), H ≠ ⊤ ∧ H.index = 5 :=
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  ndata5.exists_psl_index (by decide +kernel)

def nlist7 : List NTup :=
  [(0, 1, 6, 1), (0, 2, 3, 6), (0, 3, 2, 0), (0, 4, 5, 0), (0, 5, 4, 1), (0, 6, 1, 6), (1, 0, 0, 1), (1, 1, 5, 6), (1, 2, 3, 0), (1, 3, 4, 6), (1, 4, 2, 2), (1, 5, 6, 3), (1, 6, 1, 0), (2, 0, 2, 4), (2, 1, 3, 2), (2, 2, 1, 5), (2, 3, 5, 1), (2, 4, 0, 4), (2, 5, 6, 5), (2, 6, 4, 2), (3, 0, 2, 5), (3, 1, 4, 4), (3, 2, 1, 1), (3, 3, 6, 4), (3, 4, 0, 5), (3, 5, 5, 4), (3, 6, 3, 4), (4, 0, 5, 2), (4, 1, 4, 3), (4, 2, 2, 3), (4, 3, 0, 2), (4, 4, 1, 3), (4, 5, 6, 6), (4, 6, 3, 3), (5, 0, 5, 3), (5, 1, 3, 5), (5, 2, 1, 2), (5, 3, 0, 3), (5, 4, 2, 6), (5, 5, 6, 2), (5, 6, 4, 5), (6, 0, 0, 6), (6, 1, 6, 0), (6, 2, 1, 4), (6, 3, 5, 5), (6, 4, 3, 1), (6, 5, 4, 0), (6, 6, 2, 1)]

def ndata7 : NatData 7 where
  elems := nlist7
  one_lt := by norm_num
  lt := by decide +kernel
  nodup := by decide +kernel
  det := by decide +kernel
  one := by decide +kernel
  mul := by decide +kernel
  inv := by decide +kernel
  center := by decide +kernel

theorem exists_index_7 :
    ∃ H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)), H ≠ ⊤ ∧ H.index = 7 :=
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  ndata7.exists_psl_index (by decide +kernel)

def nlist11 : List NTup :=
  [(0, 1, 10, 0), (0, 2, 5, 10), (0, 3, 7, 8), (0, 4, 8, 3), (0, 5, 2, 10), (0, 6, 9, 1), (0, 7, 3, 8), (0, 8, 4, 3), (0, 9, 6, 1), (0, 10, 1, 0), (1, 0, 0, 1), (1, 1, 8, 9), (1, 2, 5, 0), (1, 3, 3, 10), (1, 4, 4, 6), (1, 5, 2, 0), (1, 6, 7, 10), (1, 7, 6, 10), (1, 8, 1, 9), (1, 9, 10, 3), (1, 10, 9, 3), (2, 0, 10, 6), (2, 1, 8, 10), (2, 2, 3, 9), (2, 3, 2, 9), (2, 4, 7, 9), (2, 5, 5, 2), (2, 6, 6, 2), (2, 7, 4, 9), (2, 8, 1, 10), (2, 9, 9, 8), (2, 10, 0, 6), (3, 0, 8, 4), (3, 1, 2, 1), (3, 2, 1, 1), (3, 3, 7, 0), (3, 4, 5, 7), (3, 5, 4, 7), (3, 6, 6, 5), (3, 7, 3, 0), (3, 8, 0, 4), (3, 9, 9, 9), (3, 10, 10, 8), (4, 0, 3, 3), (4, 1, 1, 6), (4, 2, 2, 4), (4, 3, 0, 3), (4, 4, 5, 8), (4, 5, 4, 8), (4, 6, 10, 7), (4, 7, 8, 6), (4, 8, 7, 6), (4, 9, 9, 4), (4, 10, 6, 7), (5, 0, 10, 9), (5, 1, 1, 7), (5, 2, 9, 6), (5, 3, 6, 6), (5, 4, 4, 10), (5, 5, 5, 3), (5, 6, 3, 6), (5, 7, 8, 7), (5, 8, 7, 7), (5, 9, 2, 6), (5, 10, 0, 9), (6, 0, 1, 2), (6, 1, 0, 2), (6, 2, 9, 5), (6, 3, 4, 4), (6, 4, 3, 4), (6, 5, 8, 5), (6, 6, 6, 8), (6, 7, 7, 1), (6, 8, 5, 5), (6, 9, 2, 5), (6, 10, 10, 4), (7, 0, 8, 8), (7, 1, 5, 4), (7, 2, 2, 7), (7, 3, 4, 5), (7, 4, 3, 5), (7, 5, 1, 4), (7, 6, 7, 3), (7, 7, 6, 3), (7, 8, 0, 8), (7, 9, 9, 7), (7, 10, 10, 5), (8, 0, 3, 7), (8, 1, 1, 3), (8, 2, 2, 2), (8, 3, 0, 7), (8, 4, 8, 0), (8, 5, 5, 6), (8, 6, 7, 4), (8, 7, 6, 4), (8, 8, 4, 0), (8, 9, 10, 10), (8, 10, 9, 10), (9, 0, 1, 5), (9, 1, 0, 5), (9, 2, 2, 3), (9, 3, 10, 1), (9, 4, 7, 2), (9, 5, 5, 9), (9, 6, 6, 9), (9, 7, 4, 2), (9, 8, 9, 2), (9, 9, 8, 2), (9, 10, 3, 1), (10, 0, 0, 10), (10, 1, 2, 8), (10, 2, 1, 8), (10, 3, 10, 2), (10, 4, 5, 1), (10, 5, 4, 1), (10, 6, 9, 0), (10, 7, 7, 5), (10, 8, 8, 1), (10, 9, 6, 0), (10, 10, 3, 2)]

set_option maxHeartbeats 2000000 in
def ndata11 : NatData 11 where
  elems := nlist11
  one_lt := by norm_num
  lt := by decide +kernel
  nodup := by decide +kernel
  det := by decide +kernel
  one := by decide +kernel
  mul := by decide +kernel
  inv := by decide +kernel
  center := by decide +kernel

theorem exists_index_11 :
    ∃ H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 11)), H ≠ ⊤ ∧ H.index = 11 :=
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  ndata11.exists_psl_index (by decide +kernel)

end CFSGOutside.GaloisMinimalDegree
