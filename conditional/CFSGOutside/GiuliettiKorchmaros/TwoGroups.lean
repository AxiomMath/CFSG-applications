import Mathlib

/-!
# Finite 2-groups with a cyclic subgroup of index 2

Classical facts (Huppert I.14.9, Hall 12.5.1) about a finite group `T` with a cyclic subgroup
`zpowers a` of index 2, `orderOf a = 2 ^ k`.

All statements are as in the task description, with no changes of mathematical content.  The
hypotheses `[Finite T]` and `IsPGroup 2 T` are not needed anywhere (only `orderOf a = 2 ^ k` and the
index-2 hypothesis are used); `dihedral_type`, `semidihedral_type`, `modular_type` take the extra
hypotheses `hb2 : b ^ 2 = 1`, `2 ≤ k` (resp. `3 ≤ k`) in the order
`(a b k) hak hidx hb hb2 hk hr`.  `quaternion_type` takes `(a k) hak hidx hno hnab`.
-/

namespace CFSGOutside.GiuliettiKorchmaros.TwoGroups

open Subgroup

section General

variable {T : Type*} [Group T]

lemma comm_of_closure_comm (s : Set T) (h : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) :
    ∀ x ∈ Subgroup.closure s, ∀ y ∈ Subgroup.closure s, x * y = y * x := by
  intro x hx y hy
  have : Commute x y := by
    induction hx, hy using Subgroup.closure_induction₂ with
    | mem x y hx hy => exact h x hx y hy
    | one_left x hx => exact Commute.one_left x
    | one_right x hx => exact Commute.one_right x
    | mul_left x y z _ _ _ h1 h2 => exact h1.mul_left h2
    | mul_right y z x _ _ _ h1 h2 => exact h1.mul_right h2
    | inv_left x y _ _ h1 => exact h1.inv_left
    | inv_right x y _ _ h1 => exact h1.inv_right
  exact this.eq

lemma mem_or_inv_mul_mem {U : Subgroup T} (hU : U.index = 2) {g : T} (hg : g ∉ U) (t : T) :
    t ∈ U ∨ g⁻¹ * t ∈ U := by
  by_cases ht : t ∈ U
  · exact Or.inl ht
  · right
    rw [Subgroup.mul_mem_iff_of_index_two hU]
    exact iff_of_false (fun h => hg (by simpa using U.inv_mem h)) ht

lemma closure_pair_eq_top {a b : T} (hidx : (Subgroup.zpowers a).index = 2)
    (hb : b ∉ Subgroup.zpowers a) : Subgroup.closure ({a, b} : Set T) = ⊤ := by
  rw [eq_top_iff]
  intro t _
  rcases mem_or_inv_mul_mem hidx hb t with h | h
  · exact (Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))) h
  · have : t = b * (b⁻¹ * t) := by simp
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      ((Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))) h)

lemma comm_of_comm_gen {a b : T} (hidx : (Subgroup.zpowers a).index = 2)
    (hb : b ∉ Subgroup.zpowers a) (hab : a * b = b * a) : ∀ x y : T, x * y = y * x := by
  intro x y
  have := comm_of_closure_comm ({a, b} : Set T) (by
    rintro x (rfl | rfl) y (rfl | rfl) <;> first | rfl | exact hab | exact hab.symm)
    x (by rw [closure_pair_eq_top hidx hb]; trivial) y (by rw [closure_pair_eq_top hidx hb]; trivial)
  exact this

lemma c_mul_d {c d : T} (h : c * d = d * c⁻¹) (n : ℕ) : c ^ n * d = d * (c ^ n)⁻¹ := by
  have h1 : SemiconjBy d c⁻¹ c := h.symm
  have h2 := h1.pow_right n
  rw [inv_pow] at h2
  exact h2.symm

lemma comm_of_conj_inv {c d : T} (hd : d * c * d⁻¹ = c⁻¹) : c * d = d * c⁻¹ := by
  have : c = d * c⁻¹ * d⁻¹ := by
    calc c = (c⁻¹)⁻¹ := (inv_inv c).symm
      _ = (d * c * d⁻¹)⁻¹ := by rw [hd]
      _ = d * c⁻¹ * d⁻¹ := by group
  rw [eq_mul_inv_iff_mul_eq] at this
  exact this

end General

section Models

variable {T : Type*} [Group T]

lemma pow_val_add {N : ℕ} [NeZero N] {c : T} (hc : orderOf c = N) (i j : ZMod N) :
    c ^ (i + j).val = c ^ i.val * c ^ j.val := by
  have h := pow_mod_orderOf c (i.val + j.val)
  rw [hc] at h
  rw [ZMod.val_add, h, pow_add]

lemma pow_val_inj {N : ℕ} [NeZero N] {c : T} (hc : orderOf c = N) {i j : ZMod N}
    (h : c ^ i.val = c ^ j.val) : i = j := by
  rw [pow_eq_pow_iff_modEq, hc] at h
  apply ZMod.val_injective
  unfold Nat.ModEq at h
  rwa [Nat.mod_eq_of_lt (ZMod.val_lt i), Nat.mod_eq_of_lt (ZMod.val_lt j)] at h

lemma pow_val_sub {N : ℕ} [NeZero N] {c : T} (hc : orderOf c = N) (i j : ZMod N) :
    c ^ (j - i).val = (c ^ i.val)⁻¹ * c ^ j.val := by
  apply eq_inv_mul_of_mul_eq
  rw [← pow_val_add hc, add_sub_cancel]

lemma pow_val_neg {N : ℕ} [NeZero N] {c : T} (hc : orderOf c = N) (i : ZMod N) :
    c ^ (-i).val = (c ^ i.val)⁻¹ := by
  have := pow_val_sub hc i 0
  simpa using this

lemma pow_val_natCast {N : ℕ} [NeZero N] {c : T} (hc : orderOf c = N) (m : ℕ) :
    c ^ (m : ZMod N).val = c ^ m := by
  have h := pow_mod_orderOf c m
  rw [hc] at h
  rw [ZMod.val_natCast]
  exact h

lemma pow_val_one {N : ℕ} [NeZero N] {c : T} (hc : orderOf c = N) :
    c ^ (1 : ZMod N).val = c := by
  have := pow_val_natCast hc 1
  simpa using this

lemma d_ne {c d : T} (hd : d ∉ Subgroup.zpowers c) (m l : ℕ) : d * c ^ m ≠ c ^ l := by
  intro h
  apply hd
  have : d = c ^ l * (c ^ m)⁻¹ := by rw [← h]; simp
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _)
    (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _))

/-- Generic: an injective hom onto a closure. -/
lemma nonempty_mulEquiv_closure {D : Type*} [Group D] (f : D →* T) (hf : Function.Injective f)
    (c d : T) (hc : c ∈ f.range) (hd : d ∈ f.range)
    (hS : ∀ x, f x ∈ Subgroup.closure ({c, d} : Set T)) :
    Nonempty (Subgroup.closure ({c, d} : Set T) ≃* D) := by
  have hbij : Function.Bijective (f.codRestrict (Subgroup.closure ({c, d} : Set T)) hS) := by
    constructor
    · intro x y h
      exact hf (congrArg Subtype.val h)
    · rintro ⟨y, hy⟩
      have : y ∈ f.range := by
        refine (Subgroup.closure_le f.range).2 ?_ hy
        rintro z (rfl | rfl)
        · exact hc
        · exact hd
      obtain ⟨x, rfl⟩ := this
      exact ⟨x, rfl⟩
  exact ⟨(MulEquiv.ofBijective _ hbij).symm⟩

lemma nonempty_mulEquiv_of_closure_eq_top {D : Type*} [Group D] {c d : T}
    (h : Subgroup.closure ({c, d} : Set T) = ⊤)
    (e : Nonempty (Subgroup.closure ({c, d} : Set T) ≃* D)) : Nonempty (T ≃* D) := by
  obtain ⟨e⟩ := e
  exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr h.symm)).trans e⟩

/-! ### Dihedral models -/

/-- The map from `DihedralGroup N` -/
def dihMap (c d : T) (N : ℕ) : DihedralGroup N → T
  | .r i => c ^ i.val
  | .sr i => d * c ^ i.val

lemma dihMap_mul {N : ℕ} [NeZero N] {c d : T} (hc : orderOf c = N) (hcd : c * d = d * c⁻¹)
    (hd : d * d = 1) (x y : DihedralGroup N) :
    dihMap c d N (x * y) = dihMap c d N x * dihMap c d N y := by
  rcases x with i | i <;> rcases y with j | j <;> simp only [dihMap, DihedralGroup.r_mul_r,
    DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
  · exact pow_val_add hc i j
  · rw [pow_val_sub hc, ← mul_assoc (c ^ i.val), c_mul_d hcd, mul_assoc]
  · rw [pow_val_add hc, mul_assoc]
  · rw [pow_val_sub hc]
    calc (c ^ i.val)⁻¹ * c ^ j.val = (d * d) * (c ^ i.val)⁻¹ * c ^ j.val := by rw [hd, one_mul]
      _ = d * (d * (c ^ i.val)⁻¹) * c ^ j.val := by simp only [mul_assoc]
      _ = d * (c ^ i.val * d) * c ^ j.val := by rw [c_mul_d hcd]
      _ = _ := by simp only [mul_assoc]

lemma dihMap_inj {N : ℕ} [NeZero N] {c d : T} (hc : orderOf c = N)
    (hd : d ∉ Subgroup.zpowers c) : Function.Injective (dihMap c d N) := by
  rintro (i | i) (j | j) h <;> simp only [dihMap] at h
  · rw [pow_val_inj hc h]
  · exact (d_ne hd _ _ h.symm).elim
  · exact (d_ne hd _ _ h).elim
  · rw [pow_val_inj hc (mul_left_cancel h)]

lemma nonempty_dihedral_closure {N : ℕ} [NeZero N] {c d : T} (hc : orderOf c = N)
    (hcd : c * d = d * c⁻¹) (hd1 : d * d = 1) (hd : d ∉ Subgroup.zpowers c) :
    Nonempty (Subgroup.closure ({c, d} : Set T) ≃* DihedralGroup N) := by
  let f : DihedralGroup N →* T := MonoidHom.mk' (dihMap c d N) (dihMap_mul hc hcd hd1)
  have hcm : c ∈ Subgroup.closure ({c, d} : Set T) := Subgroup.subset_closure (by simp)
  have hdm : d ∈ Subgroup.closure ({c, d} : Set T) := Subgroup.subset_closure (by simp)
  refine nonempty_mulEquiv_closure f (dihMap_inj hc hd) c d ⟨DihedralGroup.r 1, pow_val_one hc⟩
    ⟨DihedralGroup.sr 0, by simp [f, dihMap]⟩ ?_
  rintro (i | i)
  · exact Subgroup.pow_mem _ hcm _
  · exact Subgroup.mul_mem _ hdm (Subgroup.pow_mem _ hcm _)

/-! ### Quaternion models -/

def quatMap (c d : T) (n : ℕ) : QuaternionGroup n → T
  | .a i => c ^ i.val
  | .xa i => d * c ^ i.val

lemma quatMap_mul {n : ℕ} [NeZero n] {c d : T} (hc : orderOf c = 2 * n) (hcd : c * d = d * c⁻¹)
    (hd : d * d = c ^ n) (x y : QuaternionGroup n) :
    quatMap c d n (x * y) = quatMap c d n x * quatMap c d n y := by
  rcases x with i | i <;> rcases y with j | j <;> simp only [quatMap, QuaternionGroup.a_mul_a,
    QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a, QuaternionGroup.xa_mul_xa]
  · exact pow_val_add hc i j
  · rw [pow_val_sub hc, ← mul_assoc (c ^ i.val), c_mul_d hcd, mul_assoc]
  · rw [pow_val_add hc, mul_assoc]
  · rw [add_sub_assoc, pow_val_add hc, pow_val_natCast hc, pow_val_sub hc]
    calc c ^ n * ((c ^ i.val)⁻¹ * c ^ j.val) = (d * d) * (c ^ i.val)⁻¹ * c ^ j.val := by
          rw [hd, mul_assoc]
      _ = d * (d * (c ^ i.val)⁻¹) * c ^ j.val := by simp only [mul_assoc]
      _ = d * (c ^ i.val * d) * c ^ j.val := by rw [c_mul_d hcd]
      _ = _ := by simp only [mul_assoc]

lemma quatMap_inj {n : ℕ} [NeZero n] {c d : T} (hc : orderOf c = 2 * n)
    (hd : d ∉ Subgroup.zpowers c) : Function.Injective (quatMap c d n) := by
  rintro (i | i) (j | j) h <;> simp only [quatMap] at h
  · rw [pow_val_inj hc h]
  · exact (d_ne hd _ _ h.symm).elim
  · exact (d_ne hd _ _ h).elim
  · rw [pow_val_inj hc (mul_left_cancel h)]

lemma nonempty_quaternion_closure {n : ℕ} [NeZero n] {c d : T} (hc : orderOf c = 2 * n)
    (hcd : c * d = d * c⁻¹) (hd1 : d * d = c ^ n) (hd : d ∉ Subgroup.zpowers c) :
    Nonempty (Subgroup.closure ({c, d} : Set T) ≃* QuaternionGroup n) := by
  let f : QuaternionGroup n →* T := MonoidHom.mk' (quatMap c d n) (quatMap_mul hc hcd hd1)
  have hcm : c ∈ Subgroup.closure ({c, d} : Set T) := Subgroup.subset_closure (by simp)
  have hdm : d ∈ Subgroup.closure ({c, d} : Set T) := Subgroup.subset_closure (by simp)
  refine nonempty_mulEquiv_closure f (quatMap_inj hc hd) c d ⟨QuaternionGroup.a 1, pow_val_one hc⟩
    ⟨QuaternionGroup.xa 0, by simp [f, quatMap]⟩ ?_
  rintro (i | i)
  · exact Subgroup.pow_mem _ hcm _
  · exact Subgroup.mul_mem _ hdm (Subgroup.pow_mem _ hcm _)

end Models

section NT

lemma two_pow_dvd_mul_succ (j : ℕ) (s : ℤ) (h : (2 : ℤ) ^ j ∣ s * (s + 1)) :
    (2 : ℤ) ^ j ∣ s ∨ (2 : ℤ) ^ j ∣ s + 1 := by
  rcases Int.even_or_odd' s with ⟨w, rfl | rfl⟩
  · left
    have hc : IsCoprime ((2 : ℤ) ^ j) (2 * w + 1) := IsCoprime.pow_left ⟨-w, 1, by ring⟩
    exact hc.dvd_of_dvd_mul_right h
  · right
    have hc : IsCoprime ((2 : ℤ) ^ j) (2 * w + 1) := IsCoprime.pow_left ⟨-w, 1, by ring⟩
    exact hc.dvd_of_dvd_mul_left h

lemma nt_sq (k : ℕ) (m : ℤ) (h : m * m ≡ 1 [ZMOD 2 ^ k]) (h1 : ¬ m ≡ 1 [ZMOD 2 ^ k]) :
    2 ≤ k ∧ (m ≡ -1 [ZMOD 2 ^ k] ∨ (3 ≤ k ∧ m ≡ 2 ^ (k - 1) - 1 [ZMOD 2 ^ k]) ∨
      (3 ≤ k ∧ m ≡ 2 ^ (k - 1) + 1 [ZMOD 2 ^ k])) := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · exfalso
    interval_cases k
    · rw [pow_zero] at h1
      exact h1 Int.modEq_one
    · rw [pow_one] at h h1
      apply h1
      rw [Int.modEq_iff_dvd] at h ⊢
      obtain ⟨t, rfl | rfl⟩ := Int.even_or_odd' m
      · exfalso
        obtain ⟨w, hw⟩ := h
        have : 2 * t * (2 * t) = 4 * (t * t) := by ring
        rw [this] at hw
        generalize t * t = u at hw
        omega
      · exact ⟨-t, by ring⟩
  refine ⟨hk, ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have e1 : (2 : ℤ) ^ (j + 2) = 4 * 2 ^ j := by ring
  have e2 : (2 : ℤ) ^ (j + 2 - 1) = 2 * 2 ^ j := by
    rw [show j + 2 - 1 = j + 1 by omega]; ring
  rw [e1] at h h1
  rw [e1, e2]
  have hh := Int.modEq_iff_dvd.1 h
  obtain ⟨s, rfl | rfl⟩ := Int.even_or_odd' m
  · exfalso
    obtain ⟨w, hw⟩ := dvd_trans (dvd_mul_right 4 ((2 : ℤ) ^ j)) hh
    have : 2 * s * (2 * s) = 4 * (s * s) := by ring
    rw [this] at hw
    generalize s * s = u at hw
    omega
  · have hd : 4 * (2 : ℤ) ^ j ∣ 4 * (s * (s + 1)) := by
      have : 1 - (2 * s + 1) * (2 * s + 1) = -(4 * (s * (s + 1))) := by ring
      rw [this] at hh
      exact dvd_neg.mp hh
    have hd2 : (2 : ℤ) ^ j ∣ s * (s + 1) :=
      (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp hd
    rcases two_pow_dvd_mul_succ j s hd2 with ⟨t, ht⟩ | ⟨t, ht⟩
    · subst ht
      obtain ⟨u, rfl | rfl⟩ := Int.even_or_odd' t
      · exfalso; apply h1
        exact Int.modEq_iff_dvd.2 ⟨-u, by ring⟩
      · rcases Nat.eq_zero_or_pos j with rfl | hj
        · left
          exact Int.modEq_iff_dvd.2 ⟨-(u + 1), by ring⟩
        · right; right
          exact ⟨by omega, Int.modEq_iff_dvd.2 ⟨-u, by ring⟩⟩
    · have hs : s = 2 ^ j * t - 1 := by linarith
      subst hs
      obtain ⟨u, rfl | rfl⟩ := Int.even_or_odd' t
      · left
        exact Int.modEq_iff_dvd.2 ⟨-u, by ring⟩
      · rcases Nat.eq_zero_or_pos j with rfl | hj
        · exfalso; apply h1
          exact Int.modEq_iff_dvd.2 ⟨-u, by ring⟩
        · right; left
          exact ⟨by omega, Int.modEq_iff_dvd.2 ⟨-u, by ring⟩⟩

end NT

section Conj

variable {T : Type*} [Group T]

lemma conj_zpow_eq {a x : T} {M : ℤ} (hM : x * a * x⁻¹ = a ^ M) (i : ℤ) :
    x * a ^ i * x⁻¹ = a ^ (M * i) := by
  rw [← conj_zpow, hM, ← zpow_mul]

lemma conj_sq_aux {a x : T} {M : ℤ} (hM : x * a * x⁻¹ = a ^ M) {s : ℤ} (hs : x ^ 2 = a ^ s) :
    a ^ (M * M) = a := by
  have h1 := conj_zpow_eq hM M
  have h2 : x * (x * a * x⁻¹) * x⁻¹ = a := by
    calc x * (x * a * x⁻¹) * x⁻¹ = x ^ 2 * a * (x ^ 2)⁻¹ := by simp only [pow_two, mul_inv_rev, mul_assoc]
      _ = a ^ s * a * (a ^ s)⁻¹ := by rw [hs]
      _ = a := by rw [((Commute.refl a).zpow_left s).eq, mul_inv_cancel_right]
  rw [hM, h1] at h2
  exact h2

lemma conj_s_aux {a x : T} {M : ℤ} (hM : x * a * x⁻¹ = a ^ M) {s : ℤ} (hs : x ^ 2 = a ^ s) :
    a ^ (M * s) = a ^ s := by
  calc a ^ (M * s) = x * a ^ s * x⁻¹ := (conj_zpow_eq hM s).symm
    _ = x * x ^ 2 * x⁻¹ := by rw [hs]
    _ = x ^ 2 := by group
    _ = a ^ s := hs

lemma zpow_congr_two {a : T} {k : ℕ} (hak : orderOf a = 2 ^ k) {m n : ℤ}
    (h : m ≡ n [ZMOD 2 ^ k]) : a ^ m = a ^ n := by
  rw [zpow_eq_zpow_iff_modEq, hak]
  exact_mod_cast h

lemma modEq_of_zpow_eq {a : T} {k : ℕ} (hak : orderOf a = 2 ^ k) {m n : ℤ}
    (h : a ^ m = a ^ n) : m ≡ n [ZMOD 2 ^ k] := by
  rw [zpow_eq_zpow_iff_modEq, hak] at h
  exact_mod_cast h

lemma conj_cases {a x : T} {k : ℕ} (hak : orderOf a = 2 ^ k)
    (hidx : (Subgroup.zpowers a).index = 2) (hx : x ∉ Subgroup.zpowers a)
    {s : ℤ} (hs : x ^ 2 = a ^ s) (hnab : ∃ u v : T, u * v ≠ v * u) :
    2 ≤ k ∧ (x * a * x⁻¹ = a ^ (-1 : ℤ) ∨
      (3 ≤ k ∧ x * a * x⁻¹ = a ^ ((2 : ℤ) ^ (k - 1) - 1)) ∨
      (3 ≤ k ∧ x * a * x⁻¹ = a ^ ((2 : ℤ) ^ (k - 1) + 1))) := by
  have hN : (Subgroup.zpowers a).Normal := Subgroup.normal_of_index_eq_two hidx
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hN.conj_mem a (Subgroup.mem_zpowers a) x)
  have hm' : x * a * x⁻¹ = a ^ m := hm.symm
  have h1 := conj_sq_aux hm' hs
  have h2 : m * m ≡ 1 [ZMOD 2 ^ k] := by
    apply modEq_of_zpow_eq hak
    rw [zpow_one]; exact h1
  have h3 : ¬ m ≡ 1 [ZMOD 2 ^ k] := by
    intro h
    have h4 : x * a * x⁻¹ = a := by rw [hm', zpow_congr_two hak h, zpow_one]
    obtain ⟨u, v, huv⟩ := hnab
    exact huv (comm_of_comm_gen hidx hx (mul_inv_eq_iff_eq_mul.mp h4).symm u v)
  obtain ⟨hk, hc⟩ := nt_sq k m h2 h3
  refine ⟨hk, ?_⟩
  rcases hc with h | ⟨h3k, h⟩ | ⟨h3k, h⟩
  · left; rw [hm', zpow_congr_two hak h]
  · right; left; exact ⟨h3k, by rw [hm', zpow_congr_two hak h]⟩
  · right; right; exact ⟨h3k, by rw [hm', zpow_congr_two hak h]⟩

end Conj

section Main

variable {T : Type*} [Group T] [Finite T]

/-- (1) If `T` is nonabelian then its center lies in the cyclic subgroup `U` of index 2. -/
theorem center_le_of_index_two {U : Subgroup T} (hU : IsCyclic U) (hidx : U.index = 2)
    (hnab : ∃ x y : T, x * y ≠ y * x) : Subgroup.center T ≤ U := by
  intro z hz
  by_contra hzU
  obtain ⟨x, y, hxy⟩ := hnab
  apply hxy
  have hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u := by
    intro u hu v hv
    have := hU.isMulCommutative.is_comm.comm (⟨u, hu⟩ : U) ⟨v, hv⟩
    exact congrArg Subtype.val this
  have hs : ∀ u ∈ ((U : Set T) ∪ {z}), ∀ v ∈ ((U : Set T) ∪ {z}), u * v = v * u := by
    rintro u (hu | rfl) v (hv | rfl)
    · exact hcomm u hu v hv
    · exact (Subgroup.mem_center_iff.mp hz) u
    · exact ((Subgroup.mem_center_iff.mp hz) v).symm
    · rfl
  have htop : ∀ t : T, t ∈ Subgroup.closure ((U : Set T) ∪ {z}) := by
    intro t
    rcases mem_or_inv_mul_mem hidx hzU t with h | h
    · exact Subgroup.subset_closure (Or.inl h)
    · have : t = z * (z⁻¹ * t) := by simp
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr rfl))
        (Subgroup.subset_closure (Or.inl h))
  exact comm_of_closure_comm _ hs x (htop x) y (htop y)

/-- (2) Conjugation exponent. -/
theorem conj_exponent_cases (a b : T) (k : ℕ) (hak : orderOf a = 2 ^ k)
    (hidx : (Subgroup.zpowers a).index = 2) (hb : b ∉ Subgroup.zpowers a) (hb2 : b ^ 2 = 1)
    (hnab : ∃ x y : T, x * y ≠ y * x) :
    2 ≤ k ∧ (b * a * b⁻¹ = a ^ (2 ^ k - 1) ∨
      (3 ≤ k ∧ b * a * b⁻¹ = a ^ (2 ^ (k - 1) - 1)) ∨
      (3 ≤ k ∧ b * a * b⁻¹ = a ^ (2 ^ (k - 1) + 1))) := by
  obtain ⟨hk, h⟩ := conj_cases hak hidx hb (s := 0) (by rw [zpow_zero, hb2]) hnab
  refine ⟨hk, ?_⟩
  rcases h with h | ⟨h3, h⟩ | ⟨h3, h⟩
  · left
    have e : ((2 ^ k - 1 : ℕ) : ℤ) = 2 ^ k - 1 := by
      rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
    calc b * a * b⁻¹ = a ^ (-1 : ℤ) := h
      _ = a ^ ((2 ^ k - 1 : ℕ) : ℤ) :=
        zpow_congr_two hak (by rw [e]; exact Int.modEq_iff_dvd.2 ⟨1, by ring⟩)
      _ = a ^ (2 ^ k - 1) := zpow_natCast a _
  · right; left
    refine ⟨h3, ?_⟩
    have e : ((2 ^ (k - 1) - 1 : ℕ) : ℤ) = 2 ^ (k - 1) - 1 := by
      rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
    rw [h, ← zpow_natCast, e]
  · right; right
    refine ⟨h3, ?_⟩
    have e : ((2 ^ (k - 1) + 1 : ℕ) : ℤ) = 2 ^ (k - 1) + 1 := by push_cast; ring
    rw [h, ← zpow_natCast, e]

end Main

section Types

variable {T : Type*} [Group T]

lemma orderOf_sq' {a : T} {k : ℕ} (hak : orderOf a = 2 ^ k) (hk : 1 ≤ k) :
    orderOf (a ^ 2) = 2 ^ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [orderOf_pow_of_dvd (by norm_num) (by rw [hak]; exact dvd_pow_self 2 (by omega)), hak]
  simp [pow_succ]

lemma sq_not_mem {a g : T} (hg : g ∉ Subgroup.zpowers a) : g ∉ Subgroup.zpowers (a ^ 2) :=
  fun h => hg ((Subgroup.zpowers_le.2 (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) 2)) h)

lemma ab_not_mem {a b : T} (hb : b ∉ Subgroup.zpowers a) : a * b ∉ Subgroup.zpowers a := by
  intro h; apply hb
  have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)) h
  simpa using this

lemma zpow_mul_not_mem {a x : T} (hx : x ∉ Subgroup.zpowers a) (i : ℤ) :
    a ^ i * x ∉ Subgroup.zpowers a := by
  intro h; apply hx
  have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) i)) h
  simpa using this

lemma pow_two_pow_eq_one {a : T} {k : ℕ} (hak : orderOf a = 2 ^ k) : a ^ (2 ^ k) = 1 := by
  rw [← hak]; exact pow_orderOf_eq_one a

lemma pow_sub_one_eq_inv {a : T} {k : ℕ} (hak : orderOf a = 2 ^ k) : a ^ (2 ^ k - 1) = a⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow]
  exact pow_two_pow_eq_one hak

lemma dih_sq_b {a b : T} {k : ℕ} (hak : orderOf a = 2 ^ k) (hk : 1 ≤ k)
    (hb : b ∉ Subgroup.zpowers a) (hb1 : b * b = 1) (hsq : b * a ^ 2 * b⁻¹ = (a ^ 2)⁻¹) :
    Nonempty (Subgroup.closure ({a ^ 2, b} : Set T) ≃* DihedralGroup (2 ^ (k - 1))) :=
  nonempty_dihedral_closure (orderOf_sq' hak hk) (comm_of_conj_inv hsq) hb1 (sq_not_mem hb)

lemma conj_ab_aux {a b : T} (hsq : b * a ^ 2 * b⁻¹ = (a ^ 2)⁻¹) :
    a * b * a ^ 2 * (a * b)⁻¹ = (a ^ 2)⁻¹ := by
  calc a * b * a ^ 2 * (a * b)⁻¹ = a * (b * a ^ 2 * b⁻¹) * a⁻¹ := by group
    _ = a * (a ^ 2)⁻¹ * a⁻¹ := by rw [hsq]
    _ = (a ^ 2)⁻¹ := by group

lemma dih_sq_ab {a b : T} {k : ℕ} (hak : orderOf a = 2 ^ k) (hk : 1 ≤ k)
    (hb : b ∉ Subgroup.zpowers a) (hsq : b * a ^ 2 * b⁻¹ = (a ^ 2)⁻¹)
    (hab : a * b * (a * b) = 1) :
    Nonempty (Subgroup.closure ({a ^ 2, a * b} : Set T) ≃* DihedralGroup (2 ^ (k - 1))) :=
  nonempty_dihedral_closure (orderOf_sq' hak hk) (comm_of_conj_inv (conj_ab_aux hsq)) hab
    (sq_not_mem (ab_not_mem hb))

lemma quat_sq_ab {a b : T} {k : ℕ} (hak : orderOf a = 2 ^ k) (hk : 2 ≤ k)
    (hb : b ∉ Subgroup.zpowers a) (hsq : b * a ^ 2 * b⁻¹ = (a ^ 2)⁻¹)
    (hab : a * b * (a * b) = (a ^ 2) ^ (2 ^ (k - 2))) :
    Nonempty (Subgroup.closure ({a ^ 2, a * b} : Set T) ≃* QuaternionGroup (2 ^ (k - 2))) := by
  have hc : orderOf (a ^ 2) = 2 * 2 ^ (k - 2) := by
    rw [orderOf_sq' hak (by omega), ← pow_succ']
    congr 1; omega
  exact nonempty_quaternion_closure hc (comm_of_conj_inv (conj_ab_aux hsq)) hab
    (sq_not_mem (ab_not_mem hb))

/-- (4D) Dihedral type. -/
theorem dihedral_type (a b : T) (k : ℕ) (hak : orderOf a = 2 ^ k)
    (hidx : (Subgroup.zpowers a).index = 2) (hb : b ∉ Subgroup.zpowers a) (hb2 : b ^ 2 = 1)
    (hk : 2 ≤ k) (hr : b * a * b⁻¹ = a ^ (2 ^ k - 1)) :
    Nonempty (T ≃* DihedralGroup (2 ^ k)) ∧
    Nonempty (Subgroup.closure ({a ^ 2, b} : Set T) ≃* DihedralGroup (2 ^ (k - 1))) ∧
    Nonempty (Subgroup.closure ({a ^ 2, a * b} : Set T) ≃* DihedralGroup (2 ^ (k - 1))) := by
  rw [pow_sub_one_eq_inv hak] at hr
  have hb1 : b * b = 1 := by rw [← pow_two]; exact hb2
  have hsq : b * a ^ 2 * b⁻¹ = (a ^ 2)⁻¹ := by rw [← conj_pow, hr, inv_pow]
  refine ⟨?_, dih_sq_b hak (by omega) hb hb1 hsq, dih_sq_ab hak (by omega) hb hsq ?_⟩
  · exact nonempty_mulEquiv_of_closure_eq_top (closure_pair_eq_top hidx hb)
      (nonempty_dihedral_closure hak (comm_of_conj_inv hr) hb1 hb)
  · have hba : b * a = a⁻¹ * b := mul_inv_eq_iff_eq_mul.mp hr
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a⁻¹ * b) * b := by rw [hba]
      _ = b * b := by group
      _ = 1 := hb1

/-- (4SD) Semidihedral type. -/
theorem semidihedral_type (a b : T) (k : ℕ) (hak : orderOf a = 2 ^ k)
    (hidx : (Subgroup.zpowers a).index = 2) (hb : b ∉ Subgroup.zpowers a) (hb2 : b ^ 2 = 1)
    (hk : 3 ≤ k) (hr : b * a * b⁻¹ = a ^ (2 ^ (k - 1) - 1)) :
    Nonempty (Subgroup.closure ({a ^ 2, b} : Set T) ≃* DihedralGroup (2 ^ (k - 1))) ∧
    Nonempty (Subgroup.closure ({a ^ 2, a * b} : Set T) ≃* QuaternionGroup (2 ^ (k - 2))) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  have hb1 : b * b = 1 := by rw [← pow_two]; exact hb2
  have e1 : j + 3 - 1 = j + 2 := by omega
  have e2 : j + 3 - 2 = j + 1 := by omega
  rw [e1] at hr
  have hP : 1 ≤ 2 ^ (j + 2) := Nat.one_le_two_pow
  have hsq : b * a ^ 2 * b⁻¹ = (a ^ 2)⁻¹ := by
    rw [← conj_pow, hr, ← pow_mul]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_add]
    have : (2 ^ (j + 2) - 1) * 2 + 2 = 2 ^ (j + 3) := by
      rw [pow_succ 2 (j + 2)]; omega
    rw [this]
    exact pow_two_pow_eq_one hak
  refine ⟨?_, ?_⟩
  · exact dih_sq_b hak (by omega) hb hb1 hsq
  · have : a * b * (a * b) = (a ^ 2) ^ (2 ^ (j + 1)) := by
      calc a * b * (a * b) = a * (b * a * b⁻¹) * (b * b) := by group
        _ = a * a ^ (2 ^ (j + 2) - 1) := by rw [hr, hb1, mul_one]
        _ = a ^ (2 ^ (j + 2)) := by rw [← pow_succ']; congr 1; omega
        _ = (a ^ 2) ^ (2 ^ (j + 1)) := by rw [← pow_mul]; congr 1; ring
    exact quat_sq_ab hak (by omega) hb hsq (by rw [e2]; exact this)

/-- (4M) Modular type. -/
theorem modular_type (a b : T) (k : ℕ) (hak : orderOf a = 2 ^ k)
    (hidx : (Subgroup.zpowers a).index = 2) (hb : b ∉ Subgroup.zpowers a) (hb2 : b ^ 2 = 1)
    (hk : 3 ≤ k) (hr : b * a * b⁻¹ = a ^ (2 ^ (k - 1) + 1)) :
    (∀ x ∈ Subgroup.closure ({a ^ 2, b} : Set T), ∀ y ∈ Subgroup.closure ({a ^ 2, b} : Set T),
      x * y = y * x) ∧
    IsCyclic (Subgroup.closure ({a ^ 2, a * b} : Set T)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  have hb1 : b * b = 1 := by rw [← pow_two]; exact hb2
  have e1 : j + 3 - 1 = j + 2 := by omega
  rw [e1] at hr
  have h8 : 2 ^ (j + 3) = 2 ^ (j + 2) * 2 := pow_succ 2 (j + 2)
  constructor
  · apply comm_of_closure_comm
    have hc : b * a ^ 2 = a ^ 2 * b := by
      have : b * a ^ 2 * b⁻¹ = a ^ 2 := by
        rw [← conj_pow, hr, ← pow_mul]
        have : (2 ^ (j + 2) + 1) * 2 = 2 ^ (j + 3) + 2 := by omega
        rw [this, pow_add, pow_two_pow_eq_one hak, one_mul]
      exact mul_inv_eq_iff_eq_mul.mp this
    rintro x (rfl | rfl) y (rfl | rfl)
    · rfl
    · exact hc.symm
    · exact hc
    · rfl
  · have hab : a * b * (a * b) = a ^ (4 * 2 ^ j + 2) := by
      calc a * b * (a * b) = a * (b * a * b⁻¹) * (b * b) := by group
        _ = a * a ^ (2 ^ (j + 2) + 1) := by rw [hr, hb1, mul_one]
        _ = a ^ (4 * 2 ^ j + 2) := by rw [← pow_succ']; congr 1; rw [pow_add]; ring
    have hmem : a ^ 2 ∈ Subgroup.zpowers (a * b) := by
      refine Subgroup.mem_zpowers_iff.2 ⟨2 * (1 - 2 * 2 ^ j), ?_⟩
      rw [zpow_mul, zpow_two, hab, ← zpow_natCast, ← zpow_mul]
      have e : ((4 * 2 ^ j + 2 : ℕ) : ℤ) * (1 - 2 * 2 ^ j) = 2 - 8 * 2 ^ j * 2 ^ j := by
        push_cast; ring
      rw [e]
      have : (2 : ℤ) ^ (j + 3) = 8 * 2 ^ j := by ring
      have h2 := zpow_congr_two hak (m := 2 - 8 * 2 ^ j * 2 ^ j) (n := 2) (by
        rw [this]; exact Int.modEq_iff_dvd.2 ⟨2 ^ j, by ring⟩)
      rw [h2]
      norm_cast
    have hcl : Subgroup.closure ({a ^ 2, a * b} : Set T) = Subgroup.zpowers (a * b) := by
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro z (rfl | rfl)
        · exact hmem
        · exact Subgroup.mem_zpowers _
      · rw [Subgroup.zpowers_le]
        exact Subgroup.subset_closure (by simp)
    rw [hcl]
    infer_instance

end Types

section Quat

variable {T : Type*} [Group T]

lemma sq_zpow_mul {a x : T} {M s : ℤ} (hM : x * a * x⁻¹ = a ^ M) (hs : x ^ 2 = a ^ s) (i : ℤ) :
    (a ^ i * x) ^ 2 = a ^ (i + M * i + s) := by
  have h1 : x * a ^ i = a ^ (M * i) * x := by
    have := conj_zpow_eq hM i
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  calc (a ^ i * x) ^ 2 = a ^ i * (x * a ^ i) * x := by rw [pow_two]; simp only [mul_assoc]
    _ = a ^ i * (a ^ (M * i) * x) * x := by rw [h1]
    _ = a ^ i * a ^ (M * i) * x ^ 2 := by rw [pow_two]; simp only [mul_assoc]
    _ = a ^ (i + M * i + s) := by rw [hs, ← zpow_add, ← zpow_add]

/-- (5) Quaternion type. -/
theorem quaternion_type (a : T) (k : ℕ) (hak : orderOf a = 2 ^ k)
    (hidx : (Subgroup.zpowers a).index = 2)
    (hno : ∀ x : T, x ∉ Subgroup.zpowers a → x ^ 2 ≠ 1)
    (hnab : ∃ x y : T, x * y ≠ y * x) :
    2 ≤ k ∧ Nonempty (T ≃* QuaternionGroup (2 ^ (k - 1))) := by
  obtain ⟨x, hx⟩ : ∃ x : T, x ∉ Subgroup.zpowers a := by
    by_contra hcon
    have h1 : Subgroup.zpowers a = ⊤ :=
      eq_top_iff.2 fun y _ => by_contra fun h => hcon ⟨y, h⟩
    rw [← Subgroup.index_eq_one] at h1
    omega
  have hxx : x * x ∈ Subgroup.zpowers a := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
  obtain ⟨s, hs'⟩ := Subgroup.mem_zpowers_iff.mp hxx
  have hs : x ^ 2 = a ^ s := by rw [pow_two, hs']
  obtain ⟨hk, h⟩ := conj_cases hak hidx hx hs hnab
  refine ⟨hk, ?_⟩
  have key : ∀ M : ℤ, x * a * x⁻¹ = a ^ M → M * s ≡ s [ZMOD 2 ^ k] :=
    fun M hM => modEq_of_zpow_eq hak (conj_s_aux hM hs)
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases h with hM | ⟨h3, hM⟩ | ⟨h3, hM⟩
  · -- the quaternion case
    have hk1 := key _ hM
    obtain ⟨w, hw⟩ := Int.modEq_iff_dvd.1 hk1
    have hsw : s = 2 ^ j * w := by
      rw [pow_succ] at hw; linarith
    obtain ⟨u, rfl | rfl⟩ := Int.even_or_odd' w
    · exfalso
      apply hno x hx
      rw [hs, ← zpow_zero a]
      apply zpow_congr_two hak
      exact Int.modEq_iff_dvd.2 ⟨-u, by rw [hsw]; ring⟩
    · have hx2 : x ^ 2 = a ^ (2 ^ j) := by
        rw [hs, ← zpow_natCast]
        apply zpow_congr_two hak
        push_cast
        exact Int.modEq_iff_dvd.2 ⟨-u, by rw [hsw]; ring⟩
      have hinv : x * a * x⁻¹ = a⁻¹ := by rw [hM, zpow_neg_one]
      have hc : orderOf a = 2 * 2 ^ j := by rw [hak, pow_succ']
      rw [Nat.add_sub_cancel]
      exact nonempty_mulEquiv_of_closure_eq_top (closure_pair_eq_top hidx hx)
        (nonempty_quaternion_closure hc (comm_of_conj_inv hinv) (by rw [← pow_two]; exact hx2) hx)
  · -- semidihedral: impossible
    exfalso
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
    have e : (2 : ℤ) ^ (j + 2 + 1 - 1) = 4 * 2 ^ j := by
      rw [show j + 2 + 1 - 1 = j + 2 by omega]; ring
    rw [e] at hM
    have hk1 := key _ hM
    have hp : (0 : ℤ) < 2 ^ j := by positivity
    have e8 : (2 : ℤ) ^ (j + 2 + 1) = 8 * 2 ^ j := by ring
    rw [e8] at hk1
    obtain ⟨w, hw⟩ := Int.modEq_iff_dvd.1 hk1
    have h4 : (4 * 2 ^ j : ℤ) ∣ (2 * 2 ^ j - 1) * s := ⟨-w, by linarith⟩
    have hcop : IsCoprime (4 * (2 : ℤ) ^ j) (2 * 2 ^ j - 1) :=
      ⟨2 ^ j, -(2 * 2 ^ j + 1), by ring⟩
    obtain ⟨t, ht⟩ := hcop.dvd_of_dvd_mul_left h4
    apply hno _ (zpow_mul_not_mem hx t)
    rw [sq_zpow_mul hM hs, ← zpow_zero a]
    apply zpow_congr_two hak
    rw [e8]
    exact Int.modEq_iff_dvd.2 ⟨-t, by rw [ht]; ring⟩
  · -- modular: impossible
    exfalso
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
    have e : (2 : ℤ) ^ (j + 2 + 1 - 1) = 4 * 2 ^ j := by
      rw [show j + 2 + 1 - 1 = j + 2 by omega]; ring
    rw [e] at hM
    have hk1 := key _ hM
    have hp : (0 : ℤ) < 2 ^ j := by positivity
    have e8 : (2 : ℤ) ^ (j + 2 + 1) = 8 * 2 ^ j := by ring
    rw [e8] at hk1
    obtain ⟨w, hw⟩ := Int.modEq_iff_dvd.1 hk1
    have h0 : (4 * 2 ^ j : ℤ) * (s + 2 * w) = 0 := by linarith
    have hsw : s = -2 * w := by
      rcases mul_eq_zero.1 h0 with h | h
      · exfalso; linarith
      · linarith
    apply hno _ (zpow_mul_not_mem hx (-w * (2 * 2 ^ j - 1)))
    rw [sq_zpow_mul hM hs, ← zpow_zero a]
    apply zpow_congr_two hak
    rw [e8]
    exact Int.modEq_iff_dvd.2 ⟨w * 2 ^ j, by rw [hsw]; ring⟩

end Quat

end CFSGOutside.GiuliettiKorchmaros.TwoGroups
