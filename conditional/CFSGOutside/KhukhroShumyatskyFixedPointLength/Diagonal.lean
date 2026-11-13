import CFSGOutside.KhukhroShumyatskyFixedPointLength.Coprime
import CFSGOutside.Common.UpperNonsolubleSeries

/-!
# Khukhro–Shumyatsky, fixed points: orbits of components and their diagonals

E. I. Khukhro and P. Shumyatsky, *On the length of finite groups and of fixed points*, Proc. Amer. Math. Soc.
**143** (2015), 3781–3790. For an automorphism `ψ` of prime order `p` of a group `Y` with `F(Y) = 1`, the orbit of a
component under `ψ`, the diagonal subgroup in `C_Y(ψ)` of a nontrivial orbit, and the algebraic core of
Lemma 3.5 (`le_of_star`).
-/

namespace CFSGOutside.KhukhroShumyatskyFixedPointLength

open Subgroup CFSGOutside.Corpus CFSGOutside.Corpus.LocalCores
open CFSGOutside.NonsolubleLength CFSGOutside.UpperNonsolubleSeries
open scoped commutatorElement

section Orbit

variable {Y : Type} [Group Y]

/-- `ψ^i(S)`. -/
def orb (ψ : MulAut Y) (S : Subgroup Y) (i : ℕ) : Subgroup Y := S.map (ψ ^ i).toMonoidHom

lemma orb_zero (ψ : MulAut Y) (S : Subgroup Y) : orb ψ S 0 = S := by
  ext x; simp [orb]

lemma orb_add (ψ : MulAut Y) (S : Subgroup Y) (i j : ℕ) :
    orb ψ S (j + i) = (orb ψ S i).map (ψ ^ j).toMonoidHom := by
  rw [orb, orb, map_map]
  congr 1
  ext x
  simp [pow_add, MulAut.mul_apply]

lemma mem_orb_of_mem (ψ : MulAut Y) {S : Subgroup Y} {a : Y} (ha : a ∈ S) (i : ℕ) :
    (ψ ^ i) a ∈ orb ψ S i := ⟨a, ha, rfl⟩

variable {p : ℕ} [hp : Fact p.Prime] {ψ : MulAut Y} (hψ : ψ ^ p = 1)
include hψ

lemma orb_mod (S : Subgroup Y) (n : ℕ) : orb ψ S n = orb ψ S (n % p) := by
  rw [orb, orb, pow_eq_pow_mod n hψ]

lemma orb_p (S : Subgroup Y) : orb ψ S p = S := by
  rw [orb_mod hψ, Nat.mod_self, orb_zero]

lemma orb_shift {S : Subgroup Y} {a b : ℕ} (h : orb ψ S a = orb ψ S b) (c : ℕ) :
    orb ψ S (c + a) = orb ψ S (c + b) := by
  rw [orb_add, orb_add, h]

lemma orb_mul_of_orb_eq {T : Subgroup Y} {k : ℕ} (hk : orb ψ T k = T) (a : ℕ) :
    orb ψ T (k * a) = T := by
  induction a with
  | zero => rw [mul_zero, orb_zero]
  | succ a ih => rw [Nat.mul_succ, add_comm, orb_add, ih, ← orb, hk]

lemma orb_one_of_orb_eq {T : Subgroup Y} {k : ℕ} (hk0 : 0 < k) (hkp : k < p)
    (hk : orb ψ T k = T) : orb ψ T 1 = T := by
  have hcop : Nat.Coprime k p :=
    (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2
      (Nat.not_dvd_of_pos_of_lt hk0 hkp)))
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.out.one_lt
  rw [← hm, ← orb_mod hψ, orb_mul_of_orb_eq hψ hk]

/-- In a nontrivial orbit the `ψ^i(S)`, `i < p`, are pairwise distinct. -/
lemma orb_injective {S : Subgroup Y} (hnt : orb ψ S 1 ≠ S) {i j : ℕ} (hi : i < p) (hj : j < p)
    (h : orb ψ S i = orb ψ S j) : i = j := by
  wlog hij : i ≤ j generalizing i j
  · exact (this hj hi h.symm (by omega)).symm
  by_contra hne
  have hk0 : 0 < j - i := by omega
  set T := orb ψ S i
  have hT : orb ψ T (j - i) = T := by
    rw [orb, show T.map (ψ ^ (j - i)).toMonoidHom = orb ψ S ((j - i) + i) from (orb_add _ _ _ _).symm,
      show j - i + i = j by omega, ← h]
  have h1 := orb_one_of_orb_eq hψ hk0 (by omega) hT
  -- `ψ^{i+1}(S) = ψ^i(S)`, so `ψ(S) = S`
  have h2 : orb ψ S (1 + i) = orb ψ S i := by rw [orb_add]; exact h1
  have h3 := orb_shift hψ h2 (p - i)
  rw [show p - i + (1 + i) = 1 + p by omega, show p - i + i = p by omega, orb_mod hψ,
    orb_mod hψ S p, Nat.add_mod_right, Nat.mod_self, Nat.mod_eq_of_lt hp.out.one_lt,
    orb_zero] at h3
  exact hnt h3

end Orbit


section Delta

variable {Y : Type} [Group Y] [Finite Y]

lemma list_prod_map_mul {α : Type*} (f g : α → Y) (l : List α) (hl : l.Nodup)
    (h : ∀ i ∈ l, ∀ j ∈ l, i ≠ j → Commute (f j) (g i)) :
    (l.map fun i => f i * g i).prod = (l.map f).prod * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.prod_cons]
    rw [ih hl.2 fun i hi j hj hij => h i (List.mem_cons_of_mem _ hi) j (List.mem_cons_of_mem _ hj) hij]
    have hc : Commute (g x) (l.map f).prod := by
      refine Commute.list_prod_right _ _ fun y hy => ?_
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
      exact (h x (List.mem_cons_self) j (List.mem_cons_of_mem _ hj)
        (fun hxj => hl.1 (hxj ▸ hj))).symm
    rw [mul_assoc, ← mul_assoc (g x), hc.eq, mul_assoc, mul_assoc]

/-- The diagonal map `a ↦ a·ψ(a)⋯ψ^{p-1}(a)`. -/
def deltaFun (ψ : MulAut Y) (p : ℕ) (a : Y) : Y := ((List.range p).map fun i => (ψ ^ i) a).prod

variable {p : ℕ} {ψ : MulAut Y}

lemma orb_orb (S : Subgroup Y) (j n : ℕ) : orb ψ (orb ψ S j) n = orb ψ S (n + j) := by
  rw [orb_add]; rfl

lemma mem_normalizer_of_conj_mem {H : Subgroup Y} {x : Y} (h : ∀ y ∈ H, x * y * x⁻¹ ∈ H) :
    x ∈ normalizer (H : Set Y) := by
  apply mem_normalizer_of_map_conj_eq
  have hle : H.map (MulAut.conj x).toMonoidHom ≤ H := by
    rintro _ ⟨y, hy, rfl⟩; exact h y hy
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective (MulAut.conj x).injective])

lemma pow_apply_of_fixed {x : Y} (hx : ψ x = x) (k : ℕ) : (ψ ^ k) x = x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, hx]

lemma conj_deltaFun {x : Y} (hx : ψ x = x) (a : Y) :
    x * deltaFun ψ p a * x⁻¹ = deltaFun ψ p (x * a * x⁻¹) := by
  unfold deltaFun
  have := map_list_prod (MulAut.conj x).toMonoidHom ((List.range p).map fun i => (ψ ^ i) a)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, List.map_map] at this
  rw [this]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [map_mul, map_inv, pow_apply_of_fixed hx]


lemma map_conj_orb {S : Subgroup Y} {x : Y} (hx : ψ x = x) (i : ℕ) :
    (orb ψ S i).map (MulAut.conj x).toMonoidHom = orb ψ (S.map (MulAut.conj x).toMonoidHom) i := by
  rw [orb, orb, map_map, map_map]
  congr 1
  ext y
  simp [map_mul, map_inv, pow_apply_of_fixed hx]



variable (hF : fittingSubgroup Y = ⊥) [hp : Fact p.Prime]
  (hψ : ψ ^ p = 1) {S : Subgroup Y} (hS : IsComponent S) (hnt : orb ψ S 1 ≠ S)
include hψ hS hnt

lemma isComponent_orb (i : ℕ) : IsComponent (orb ψ S i) :=
  isComponent_map_mulEquiv (ψ ^ i) hS

lemma commute_orb {a b : Y} (ha : a ∈ S) (hb : b ∈ S) {i j : ℕ} (hi : i < p) (hj : j < p)
    (hij : i ≠ j) : Commute ((ψ ^ i) a) ((ψ ^ j) b) :=
  component_commute (isComponent_orb hψ hS hnt i) (isComponent_orb hψ hS hnt j)
    (fun h => hij (orb_injective hψ hnt hi hj h)) _ (mem_orb_of_mem ψ ha i) _
    (mem_orb_of_mem ψ hb j)

lemma deltaFun_mul {a b : Y} (ha : a ∈ S) (hb : b ∈ S) :
    deltaFun ψ p (a * b) = deltaFun ψ p a * deltaFun ψ p b := by
  unfold deltaFun
  simp only [map_mul]
  refine list_prod_map_mul _ _ _ (List.nodup_range) fun i hi j hj hij => ?_
  exact commute_orb hψ hS hnt ha hb (List.mem_range.1 hj) (List.mem_range.1 hi) (Ne.symm hij)

lemma deltaFun_fixed {a : Y} (ha : a ∈ S) : ψ (deltaFun ψ p a) = deltaFun ψ p a := by
  obtain ⟨n, hn⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.out.one_lt; omega⟩
  unfold deltaFun
  rw [map_list_prod, List.map_map, hn]
  have e1 : ((List.range (n + 1)).map (⇑ψ ∘ fun i => (ψ ^ i) a)) =
      (List.range (n + 1)).map fun i => (ψ ^ (i + 1)) a := by
    congr 1; funext i; simp [pow_succ', MulAut.mul_apply]
  rw [e1, List.prod_range_succ (fun i => (ψ ^ (i + 1)) a), List.prod_range_succ' (fun i => (ψ ^ i) a)]
  have hpa : (ψ ^ (n + 1)) a = a := by rw [← hn, hψ]; rfl
  rw [hpa, pow_zero]
  change _ * a = a * _
  refine (Commute.list_prod_left _ _ fun y hy => ?_).eq
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
  have := commute_orb hψ hS hnt ha ha (i := i + 1) (j := 0) (by rw [hn]; simpa using hi)
    hp.out.pos (by omega)
  simpa using this

/-- The diagonal homomorphism `S → ψ`-fixed points. -/
def deltaHom : S →* Y where
  toFun a := deltaFun ψ p a
  map_one' := by simp [deltaFun]
  map_mul' a b := deltaFun_mul hψ hS hnt a.2 b.2

lemma deltaHom_apply (a : S) : deltaHom hψ hS hnt a = deltaFun ψ p a := rfl

lemma deltaHom_injective (hF : fittingSubgroup Y = ⊥) : Function.Injective (deltaHom hψ hS hnt) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  rw [MonoidHom.mem_ker, deltaHom_apply] at ha
  obtain ⟨n, hn⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.out.one_lt; omega⟩
  unfold deltaFun at ha
  rw [hn, List.prod_range_succ', pow_zero] at ha
  set w := ((List.range n).map fun i => (ψ ^ (i + 1)) (a : Y)).prod
  have hw : ∀ s ∈ S, Commute s w := by
    intro s hs
    refine Commute.list_prod_right _ _ fun y hy => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
    have := commute_orb hψ hS hnt hs a.2 (i := 0) (j := i + 1) hp.out.pos
      (by rw [hn]; simpa using hi) (by omega)
    simpa using this
  have haw : (a : Y) = w⁻¹ := eq_inv_of_mul_eq_one_left ha
  have hcen : a ∈ center S := by
    rw [mem_center_iff]
    intro s
    apply Subtype.ext
    simp only [coe_mul]
    rw [haw]
    exact ((hw s s.2).inv_right).eq
  rw [component_center_eq_bot hF hS, mem_bot] at hcen
  rw [mem_bot]; exact hcen

/-- The diagonal `D_S` of the orbit of `S`. -/
def diag : Subgroup Y := (deltaHom hψ hS hnt).range

lemma diag_le_fixedSub : diag hψ hS hnt ≤ fixedSub ψ := by
  rintro _ ⟨a, rfl⟩; exact deltaFun_fixed hψ hS hnt a.2

/-- A `ψ`-fixed element normalizing `S` normalizes the diagonal. -/
lemma mem_normalizer_diag {x : Y} (hx : ψ x = x) (hxS : x ∈ normalizer (S : Set Y)) :
    x ∈ normalizer ((diag hψ hS hnt : Subgroup Y) : Set Y) := by
  apply mem_normalizer_of_conj_mem
  rintro _ ⟨a, rfl⟩
  rw [deltaHom_apply, conj_deltaFun hx]
  exact ⟨⟨_, (mem_normalizer_iff.1 hxS a).1 a.2⟩, rfl⟩

/-- (O5) A `ψ`-fixed element of order prime to `p` which maps `S` into its `ψ`-orbit
normalizes `S`. -/
lemma conj_eq_of_mem_orb {x : Y} (hx : ψ x = x) (hord : (orderOf x).Coprime p) {j : ℕ}
    (hj : j < p) (hT : S.map (MulAut.conj x).toMonoidHom = orb ψ S j) :
    S.map (MulAut.conj x).toMonoidHom = S := by
  have key : ∀ n : ℕ, S.map (MulAut.conj (x ^ n)).toMonoidHom = orb ψ S (j * n) := by
    intro n
    induction n with
    | zero => rw [pow_zero, mul_zero, orb_zero]; ext y; simp
    | succ n ih =>
      have : S.map (MulAut.conj (x ^ (n + 1))).toMonoidHom =
          (S.map (MulAut.conj (x ^ n)).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
        rw [map_map, conj_comp_conj, pow_succ']
      rw [this, ih, map_conj_orb hx, hT, orb_orb, Nat.mul_succ]
  have h1 := key (orderOf x)
  rw [pow_orderOf_eq_one] at h1
  have h2 : S = orb ψ S ((j * orderOf x) % p) := by
    rw [← orb_mod hψ, ← h1]; ext y; simp
  by_cases hj0 : j = 0
  · subst hj0; rw [hT, orb_zero]
  · exfalso
    have hlt : (j * orderOf x) % p < p := Nat.mod_lt _ hp.out.pos
    have := orb_injective hψ hnt hlt hp.out.pos (by rw [← h2, orb_zero])
    rw [← Nat.dvd_iff_mod_eq_zero] at this
    rcases (Nat.Prime.dvd_mul hp.out).1 this with h | h
    · exact hj0 (Nat.eq_zero_of_dvd_of_lt h hj)
    · exact (Nat.Prime.coprime_iff_not_dvd hp.out).1 hord.symm h

lemma comm_orb_of_ne {i j : ℕ} (hi : i < p) (hj : j < p) (hij : i ≠ j) {a b : Y}
    (ha : a ∈ orb ψ S i) (hb : b ∈ orb ψ S j) : Commute a b :=
  component_commute (isComponent_orb hψ hS hnt i) (isComponent_orb hψ hS hnt j)
    (fun h => hij (orb_injective hψ hnt hi hj h)) _ ha _ hb

lemma mem_orb_one {a : Y} (ha : a ∈ S) : ψ a ∈ orb ψ S 1 := by
  have := mem_orb_of_mem ψ ha 1; rwa [pow_one] at this

lemma mem_orb_two {a : Y} (ha : a ∈ S) : ψ (ψ a) ∈ orb ψ S 2 := by
  have := mem_orb_of_mem ψ ha 2; rwa [pow_two, MulAut.mul_apply] at this

/-- The tail `ψ²(a)⋯ψ^{p-1}(a)` of the diagonal element. -/
def tailFun (a : Y) : Y := ((List.range (p - 2)).map fun i => (ψ ^ (i + 2)) a).prod

lemma deltaFun_eq_tail (hp3 : 3 ≤ p) (a : Y) : deltaFun ψ p a = a * ψ a * tailFun (ψ := ψ) (p := p) a := by
  unfold deltaFun tailFun
  obtain ⟨m, hm⟩ : ∃ m, p = m + 2 := ⟨p - 2, by omega⟩
  rw [hm, List.prod_range_succ', List.prod_range_succ', show m + 2 - 2 = m by omega]
  simp [pow_one, mul_assoc]

lemma commute_tail (hp3 : 3 ≤ p) {a : Y} (ha : a ∈ S) {k : ℕ} (hk : k < 2) {x : Y}
    (hx : x ∈ orb ψ S k) : Commute x (tailFun (ψ := ψ) (p := p) a) := by
  refine Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
  rw [List.mem_range] at hi
  exact comm_orb_of_ne hψ hS hnt (by omega) (by omega) (by omega) hx (mem_orb_of_mem ψ ha _)

lemma perfect_S : ⁅S, S⁆ = S := by
  have h := hS.1.1
  rw [Group.isPerfect_def] at h
  have := congrArg (Subgroup.map S.subtype) h
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at this
  exact this

/-- The multiplication map from `S × ψ(S) × ψ²(S)` (pairwise commuting). -/
def tripleHom {A B C : Subgroup Y} (cAB : ∀ a ∈ A, ∀ b ∈ B, Commute a b)
    (cAC : ∀ a ∈ A, ∀ c ∈ C, Commute a c) (cBC : ∀ b ∈ B, ∀ c ∈ C, Commute b c) :
    A × B × C →* Y :=
  MonoidHom.noncommCoprod A.subtype (MonoidHom.noncommCoprod B.subtype C.subtype
    fun b c => cBC b b.2 c c.2) fun a bc => by
      simp only [MonoidHom.noncommCoprod_apply, coe_subtype]
      exact (cAB a a.2 _ bc.1.2).mul_right (cAC a a.2 _ bc.2.2)

omit hψ hS hnt in
lemma tripleHom_apply {A B C : Subgroup Y} (cAB : ∀ a ∈ A, ∀ b ∈ B, Commute a b)
    (cAC : ∀ a ∈ A, ∀ c ∈ C, Commute a c) (cBC : ∀ b ∈ B, ∀ c ∈ C, Commute b c)
    (x : A × B × C) : tripleHom cAB cAC cBC x = (x.1 : Y) * ((x.2.1 : Y) * x.2.2) := rfl

omit hψ hS hnt in
lemma comm_sup {A B : Subgroup Y} {g : Y} (hA : ∀ a ∈ A, Commute g a) (hB : ∀ b ∈ B, Commute g b) :
    ∀ z ∈ A ⊔ B, Commute g z := by
  have : A ⊔ B ≤ centralizer {g} := sup_le (fun a ha => mem_centralizer_singleton_iff.2 (hA a ha).eq.symm)
    (fun b hb => mem_centralizer_singleton_iff.2 (hB b hb).eq.symm)
  intro z hz
  exact (mem_centralizer_singleton_iff.1 (this hz)).symm

/-- **The algebraic core of Lemma 3.5.**  Let `H` be a `ψ`-invariant subgroup such that whenever
`c ∈ S` and `c⁻¹ψ(c) ∉ H`, the conjugate `c⁻¹ D_S c` of the diagonal lies in `H`.  Then
`S ≤ H`. -/
lemma le_of_star (hF : fittingSubgroup Y = ⊥) (hp3 : 3 ≤ p) {H : Subgroup Y}
    (hHinv : ∀ h ∈ H, ψ h ∈ H)
    (hstar : ∀ c ∈ S, c⁻¹ * ψ c ∉ H → ∀ a ∈ S, c⁻¹ * deltaFun ψ p a * c ∈ H) : S ≤ H := by
  set S1 := orb ψ S 1
  set S2 := orb ψ S 2
  have c01 : ∀ x ∈ S, ∀ y ∈ S1, Commute x y := fun x hx y hy =>
    comm_orb_of_ne hψ hS hnt hp.out.pos (by omega) (by omega) (by rwa [orb_zero]) hy
  have c02 : ∀ x ∈ S, ∀ y ∈ S2, Commute x y := fun x hx y hy =>
    comm_orb_of_ne hψ hS hnt hp.out.pos (by omega) (by omega) (by rwa [orb_zero]) hy
  have c12 : ∀ x ∈ S1, ∀ y ∈ S2, Commute x y := fun x hx y hy =>
    comm_orb_of_ne hψ hS hnt (by omega) (by omega) (by omega) hx hy
  let T := tripleHom c01 c02 c12
  have m1 : ∀ {x : Y} (hx : x ∈ S), ψ x ∈ S1 := fun hx => mem_orb_one hψ hS hnt hx
  have m2 : ∀ {x : Y} (hx : x ∈ S), ψ (ψ x) ∈ S2 := fun hx => mem_orb_two hψ hS hnt hx
  -- atoms
  have t0 : ∀ {x : Y} (hx : x ∈ S), T (⟨x, hx⟩, 1, 1) = x := fun _ => by
    simp [T, tripleHom_apply]
  have t1 : ∀ {x : Y} (hx : x ∈ S1), T (1, ⟨x, hx⟩, 1) = x := fun _ => by
    simp [T, tripleHom_apply]
  have t2 : ∀ {x : Y} (hx : x ∈ S2), T (1, 1, ⟨x, hx⟩) = x := fun _ => by
    simp [T, tripleHom_apply]
  have hHk : ∀ k : ℕ, ∀ h ∈ H, (ψ ^ k) h ∈ H := by
    intro k
    induction k with
    | zero => intro h hh; exact hh
    | succ k ih => intro h hh; rw [pow_succ', MulAut.mul_apply]; exact hHinv _ (ih h hh)
  by_cases hA : ∀ c ∈ S, c⁻¹ * ψ c ∈ H
  · -- Case A: the commutators of `S` lie in `H`
    rw [← perfect_S hψ hS hnt]
    refine commutator_le.2 fun a ha b hb => ?_
    have key : ⁅a, b⁆ = (a * ψ a⁻¹) * (b * ψ b⁻¹) * ((a⁻¹ * b⁻¹)⁻¹ * ψ (a⁻¹ * b⁻¹))⁻¹ := by
      have ha' := inv_mem ha
      have hb' := inv_mem hb
      have h := congrArg T (show ((⟨a, ha⟩, 1, 1) : S × S1 × S2) * (⟨b, hb⟩, 1, 1) *
          (⟨a, ha⟩, 1, 1)⁻¹ * (⟨b, hb⟩, 1, 1)⁻¹ =
          (⟨a, ha⟩, ⟨ψ a⁻¹, m1 ha'⟩, 1) * (⟨b, hb⟩, ⟨ψ b⁻¹, m1 hb'⟩, 1) *
          (((⟨a⁻¹, ha'⟩, 1, 1) * (⟨b⁻¹, hb'⟩, 1, 1))⁻¹ *
            ((1, ⟨ψ a⁻¹, m1 ha'⟩, 1) * (1, ⟨ψ b⁻¹, m1 hb'⟩, 1)))⁻¹ by
        ext <;> simp <;> group)
      simp only [map_mul, map_inv, tripleHom_apply, T] at h
      simp only [OneMemClass.coe_one, mul_one, one_mul, coe_mul, coe_inv] at h
      rw [commutatorElement_def]
      simp only [map_mul, map_inv]
      convert h using 1 <;> group
    rw [key]
    refine mul_mem (mul_mem ?_ ?_) (inv_mem (hA _ (mul_mem (inv_mem ha) (inv_mem hb))))
    · simpa using hA _ (inv_mem ha)
    · simpa using hA _ (inv_mem hb)
  · push Not at hA
    obtain ⟨c, hcS, hcH⟩ := hA
    have hD := hstar c hcS hcH
    let K : Set Y := {e | e ∈ S ∧ e * (ψ e)⁻¹ ∈ H}
    -- Step 1
    have step1 : ∀ a ∈ S, c⁻¹ * a * c * a⁻¹ ∈ K := by
      intro a ha
      refine ⟨mul_mem (mul_mem (mul_mem (inv_mem hcS) ha) hcS) (inv_mem ha), ?_⟩
      have hu := hD a ha
      have hv : ψ c⁻¹ * deltaFun ψ p a * ψ c ∈ H := by
        have := hHinv _ hu
        rwa [map_mul, map_mul, deltaFun_fixed hψ hS hnt ha] at this
      set R := tailFun (ψ := ψ) (p := p) a
      have hcR : Commute c R := commute_tail hψ hS hnt hp3 ha (k := 0) (by omega) (by rwa [orb_zero])
      have hψcR : Commute (ψ c⁻¹) R := commute_tail hψ hS hnt hp3 ha (k := 1) (by omega)
        (m1 (inv_mem hcS))
      have hz := mul_mem hu (inv_mem hv)
      rw [deltaFun_eq_tail hψ hS hnt hp3] at hz
      have e1 : c⁻¹ * (a * ψ a * R) * c * (ψ c⁻¹ * (a * ψ a * R) * ψ c)⁻¹ =
          (c⁻¹ * a * ψ a * c) * (ψ c⁻¹ * a * ψ a * ψ c)⁻¹ := by
        have hcR' : Commute (ψ c⁻¹)⁻¹ R := hψcR.inv_left
        calc c⁻¹ * (a * ψ a * R) * c * (ψ c⁻¹ * (a * ψ a * R) * ψ c)⁻¹
            = c⁻¹ * a * ψ a * (R * c) * (ψ c)⁻¹ * R⁻¹ * (ψ a)⁻¹ * a⁻¹ * (ψ c⁻¹)⁻¹ := by
              simp only [mul_inv_rev, map_inv, inv_inv]; group
          _ = c⁻¹ * a * ψ a * c * ((R * (ψ c)⁻¹) * R⁻¹) * (ψ a)⁻¹ * a⁻¹ * (ψ c⁻¹)⁻¹ := by
              rw [← hcR.eq]; group
          _ = c⁻¹ * a * ψ a * c * (ψ c)⁻¹ * (ψ a)⁻¹ * a⁻¹ * (ψ c⁻¹)⁻¹ := by
              rw [show (ψ c)⁻¹ = (ψ c⁻¹)⁻¹⁻¹ by simp, ← hcR'.inv_left.eq]; group
          _ = _ := by simp only [mul_inv_rev, map_inv, inv_inv]; group
      rw [e1] at hz
      convert hz using 1
      have h := congrArg T (show ((⟨c, hcS⟩, 1, 1) : S × S1 × S2)⁻¹ * (⟨a, ha⟩, 1, 1) *
          (⟨c, hcS⟩, 1, 1) * (⟨a, ha⟩, 1, 1)⁻¹ *
          ((1, ⟨ψ c, m1 hcS⟩, 1)⁻¹ * (1, ⟨ψ a, m1 ha⟩, 1) * (1, ⟨ψ c, m1 hcS⟩, 1) *
            (1, ⟨ψ a, m1 ha⟩, 1)⁻¹)⁻¹ =
          ((⟨c, hcS⟩, 1, 1)⁻¹ * (⟨a, ha⟩, 1, 1) * (1, ⟨ψ a, m1 ha⟩, 1) * (⟨c, hcS⟩, 1, 1)) *
          ((1, ⟨ψ c, m1 hcS⟩, 1)⁻¹ * (⟨a, ha⟩, 1, 1) * (1, ⟨ψ a, m1 ha⟩, 1) *
            (1, ⟨ψ c, m1 hcS⟩, 1))⁻¹ by
        ext <;> simp <;> group)
      simp only [map_mul, map_inv, tripleHom_apply, T] at h
      simp only [OneMemClass.coe_one, mul_one, one_mul, coe_mul, coe_inv] at h
      simp only [map_mul, map_inv]
      convert h using 1 <;> group
    -- conjugation by the elements `w_b = ψ²(c⁻¹ δ(b) c) ∈ H`
    have hw : ∀ b ∈ S, ∃ w ∈ H, ∀ X ∈ S ⊔ S1, w⁻¹ * X * w = (b * ψ b)⁻¹ * X * (b * ψ b) := by
      intro b hb
      have hw0 := hHinv _ (hHinv _ (hD b hb))
      rw [map_mul, map_mul, map_mul, map_mul, deltaFun_fixed hψ hS hnt hb,
        deltaFun_fixed hψ hS hnt hb, deltaFun_eq_tail hψ hS hnt hp3] at hw0
      refine ⟨_, hw0, fun X hX => ?_⟩
      set g := ψ (ψ c)
      set R := tailFun (ψ := ψ) (p := p) b
      have hgS : ∀ x ∈ S, Commute g x := fun x hx => (c02 x hx g (m2 hcS)).symm
      have hgS1 : ∀ x ∈ S1, Commute g x := fun x hx => (c12 x hx g (m2 hcS)).symm
      have hRS : ∀ x ∈ S, Commute R x := fun x hx =>
        (commute_tail hψ hS hnt hp3 hb (k := 0) (by omega) (by rwa [orb_zero])).symm
      have hRS1 : ∀ x ∈ S1, Commute R x := fun x hx =>
        (commute_tail hψ hS hnt hp3 hb (k := 1) (by omega) hx).symm
      have hB : b * ψ b ∈ S ⊔ S1 := mul_mem (mem_sup_left hb) (mem_sup_right (m1 hb))
      set Y0 := (b * ψ b)⁻¹ * X * (b * ψ b)
      have hY0 : Y0 ∈ S ⊔ S1 := mul_mem (mul_mem (inv_mem hB) hX) hB
      have hgX := comm_sup hgS hgS1 X hX
      have hgY := comm_sup hgS hgS1 Y0 hY0
      have hRY := comm_sup hRS hRS1 Y0 hY0
      rw [map_inv, map_inv]
      calc (g⁻¹ * (b * ψ b * R) * g)⁻¹ * X * (g⁻¹ * (b * ψ b * R) * g)
          = g⁻¹ * R⁻¹ * (b * ψ b)⁻¹ * (g * X * g⁻¹) * (b * ψ b) * R * g := by group
        _ = g⁻¹ * (R⁻¹ * Y0 * R) * g := by
          rw [show g * X * g⁻¹ = X by rw [hgX.eq, mul_inv_cancel_right]]; simp only [Y0]; group
        _ = g⁻¹ * Y0 * g := by rw [show R⁻¹ * Y0 * R = Y0 by rw [mul_assoc, ← hRY.eq, inv_mul_cancel_left]]
        _ = Y0 := by rw [mul_assoc, ← hgY.eq, inv_mul_cancel_left]
    -- Step 2
    have step2 : ∀ e ∈ K, ∀ b ∈ S, b⁻¹ * e * b ∈ K := by
      rintro e ⟨heS, heH⟩ b hb
      refine ⟨mul_mem (mul_mem (inv_mem hb) heS) hb, ?_⟩
      obtain ⟨w, hwH, hwX⟩ := hw b hb
      have hX : e * (ψ e)⁻¹ ∈ S ⊔ S1 := mul_mem (mem_sup_left heS) (mem_sup_right (inv_mem (m1 heS)))
      have := mul_mem (mul_mem (inv_mem hwH) heH) hwH
      rw [hwX _ hX] at this
      convert this using 1
      have h := congrArg T (show ((⟨b, hb⟩, 1, 1) : S × S1 × S2)⁻¹ * (⟨e, heS⟩, 1, 1) * (⟨b, hb⟩, 1, 1) *
          ((1, ⟨ψ b, m1 hb⟩, 1)⁻¹ * (1, ⟨ψ e, m1 heS⟩, 1) * (1, ⟨ψ b, m1 hb⟩, 1))⁻¹ =
          ((⟨b, hb⟩, 1, 1) * (1, ⟨ψ b, m1 hb⟩, 1))⁻¹ * ((⟨e, heS⟩, 1, 1) * (1, ⟨ψ e, m1 heS⟩, 1)⁻¹) *
          ((⟨b, hb⟩, 1, 1) * (1, ⟨ψ b, m1 hb⟩, 1)) by
        ext <;> simp <;> group)
      simp only [map_mul, map_inv, tripleHom_apply, T] at h
      simp only [OneMemClass.coe_one, mul_one, one_mul, coe_mul, coe_inv] at h
      simp only [map_mul, map_inv]
      convert h using 1 <;> group
    -- `M = {s ∈ S | ψ s ∈ H}` is normalized by `S`
    have conjS1 : ∀ b ∈ S, ∀ s ∈ S, ψ s ∈ H → ψ (b⁻¹ * s * b) ∈ H := by
      intro b hb s hs hsH
      obtain ⟨w, hwH, hwX⟩ := hw b hb
      have := mul_mem (mul_mem (inv_mem hwH) hsH) hwH
      rw [hwX _ (mem_sup_right (m1 hs))] at this
      convert this using 1
      have h := congrArg T (show (1, ⟨ψ b, m1 hb⟩, 1)⁻¹ * (1, ⟨ψ s, m1 hs⟩, 1) * (1, ⟨ψ b, m1 hb⟩, 1) =
          ((⟨b, hb⟩, 1, 1) * (1, ⟨ψ b, m1 hb⟩, 1))⁻¹ * ((1, ⟨ψ s, m1 hs⟩, 1) : S × S1 × S2) *
          ((⟨b, hb⟩, 1, 1) * (1, ⟨ψ b, m1 hb⟩, 1)) by
        ext <;> simp <;> group)
      simp only [map_mul, map_inv, tripleHom_apply, T] at h
      simp only [OneMemClass.coe_one, mul_one, one_mul, coe_mul, coe_inv] at h
      simp only [map_mul, map_inv]
      convert h using 1 <;> group
    -- Step 3
    have step3 : ∀ e ∈ K, ∀ f ∈ K, ψ (f⁻¹ * e⁻¹ * f * e) ∈ H := by
      rintro e ⟨heS, heH⟩ f ⟨hfS, hfH⟩
      have hy := hHinv _ hfH
      have := mul_mem (mul_mem (mul_mem (inv_mem hy) heH) hy) (inv_mem heH)
      convert this using 1
      have h := congrArg T (show (1, ⟨ψ f, m1 hfS⟩, 1)⁻¹ * (1, ⟨ψ e, m1 heS⟩, 1)⁻¹ *
          (1, ⟨ψ f, m1 hfS⟩, 1) * ((1, ⟨ψ e, m1 heS⟩, 1) : S × S1 × S2) =
          ((1, ⟨ψ f, m1 hfS⟩, 1) * (1, 1, ⟨ψ (ψ f), m2 hfS⟩)⁻¹)⁻¹ *
            ((⟨e, heS⟩, 1, 1) * (1, ⟨ψ e, m1 heS⟩, 1)⁻¹) *
            ((1, ⟨ψ f, m1 hfS⟩, 1) * (1, 1, ⟨ψ (ψ f), m2 hfS⟩)⁻¹) *
            ((⟨e, heS⟩, 1, 1) * (1, ⟨ψ e, m1 heS⟩, 1)⁻¹)⁻¹ by
        ext <;> simp <;> group)
      simp only [map_mul, map_inv, tripleHom_apply, T] at h
      simp only [OneMemClass.coe_one, mul_one, one_mul, coe_mul, coe_inv] at h
      simp only [map_mul, map_inv]
      convert h using 1 <;> group
    -- conclusion
    haveI := component_isSimple hF hS
    let Mt : Subgroup S := (H.comap ψ.toMonoidHom).subgroupOf S
    haveI hMt : Mt.Normal := by
      refine ⟨fun x hx g => ?_⟩
      have h1 : ψ (((g : Y)⁻¹)⁻¹ * x * (g : Y)⁻¹) ∈ H := conjS1 _ (inv_mem g.2) _ x.2 hx
      simpa [Mt, mem_subgroupOf] using h1
    rcases hMt.eq_bot_or_eq_top with hbot | htop
    · exfalso
      have hcomm : ∀ e ∈ K, ∀ f ∈ K, Commute e f := by
        intro e he f hf
        have hmem : (⟨f⁻¹ * e⁻¹ * f * e, mul_mem (mul_mem (mul_mem (inv_mem hf.1) (inv_mem he.1)) hf.1)
            he.1⟩ : S) ∈ Mt := step3 e he f hf
        rw [hbot, mem_bot] at hmem
        have h1 : f⁻¹ * e⁻¹ * f * e = 1 := congrArg Subtype.val hmem
        have h2 : f * e = e * f := by
          have := congrArg (fun z => e * f * z) h1
          simp only [mul_one] at this
          rw [← this]; group
        exact h2.symm
      let Kt : Set S := {k | (k : Y) ∈ K}
      let J : Subgroup S := closure Kt
      haveI hJ : J.Normal := by
        refine ⟨fun x hx g => ?_⟩
        induction hx using closure_induction with
        | mem x hx =>
          apply Subgroup.subset_closure
          have := step2 _ hx _ (inv_mem g.2)
          simpa [Kt] using this
        | one => simp
        | mul a b _ _ ha hb =>
          have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
          rw [this]; exact mul_mem ha hb
        | inv a _ ha =>
          have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
          rw [this]; exact inv_mem ha
      -- a nontrivial element of `K`
      have hc1 : c ≠ 1 := by
        rintro rfl; apply hcH; simp
      obtain ⟨a0, ha0, hne⟩ : ∃ a0 ∈ S, c * a0 ≠ a0 * c := by
        by_contra hall
        push Not at hall
        have : (⟨c, hcS⟩ : S) ∈ center S := mem_center_iff.2 fun g => Subtype.ext (hall g g.2).symm
        rw [component_center_eq_bot hF hS, mem_bot] at this
        exact hc1 (congrArg Subtype.val this)
      have he0 := step1 a0 ha0
      have hJne : J ≠ ⊥ := by
        intro hJb
        have : (⟨_, he0.1⟩ : S) ∈ J := Subgroup.subset_closure he0
        rw [hJb, mem_bot] at this
        apply hne
        have h1 : c⁻¹ * a0 * c * a0⁻¹ = 1 := congrArg Subtype.val this
        have := congrArg (fun z => c * z * a0) h1
        simp only [mul_one] at this
        rw [← this]; group
      have hJtop : J = ⊤ := (hJ.eq_bot_or_eq_top).resolve_left hJne
      -- `J` is abelian
      have hcen1 : J ≤ centralizer Kt := by
        rw [closure_le]
        intro x hx y hy
        exact Subtype.ext (hcomm _ hy _ hx).eq
      have hcen2 : J ≤ centralizer (J : Set S) := by
        rw [closure_le]
        intro x hx y hy
        exact ((mem_centralizer_iff.1 (hcen1 hy)) x hx).symm
      obtain ⟨a, ha, b, hb, hab⟩ := component_nonab hF hS
      apply hab
      have := (mem_centralizer_iff.1 (hcen2 (hJtop ▸ mem_top (⟨a, ha⟩ : S))))
        ⟨b, hb⟩ (hJtop ▸ mem_top _)
      exact (congrArg Subtype.val this).symm
    · intro s hs
      have h1 : ψ s ∈ H := by
        have : (⟨s, hs⟩ : S) ∈ Mt := htop ▸ mem_top _
        exact this
      have := hHk (p - 1) _ h1
      rwa [← MulAut.mul_apply, ← pow_succ, show p - 1 + 1 = p by have := hp.out.one_lt; omega,
        hψ, MulAut.one_apply] at this

lemma diag_ne_bot (hF : fittingSubgroup Y = ⊥) : diag hψ hS hnt ≠ ⊥ := by
  haveI := component_isSimple hF hS
  obtain ⟨a, ha⟩ := exists_ne (1 : S)
  intro h
  have : deltaHom hψ hS hnt a ∈ diag hψ hS hnt := ⟨a, rfl⟩
  rw [h, mem_bot] at this
  exact ha (deltaHom_injective hψ hS hnt hF (by rw [this, map_one]))

lemma diag_perfect : ⁅diag hψ hS hnt, diag hψ hS hnt⁆ = diag hψ hS hnt := by
  have h := hS.1.1
  rw [Group.isPerfect_def, _root_.commutator_def] at h
  rw [diag, MonoidHom.range_eq_map, ← Subgroup.map_commutator, h]

lemma orb_ne_conj_of_fixed {x : Y} (hx : ψ x = x) :
    orb ψ (S.map (MulAut.conj x).toMonoidHom) 1 ≠ S.map (MulAut.conj x).toMonoidHom := by
  intro h
  apply hnt
  rw [← map_conj_orb hx] at h
  exact Subgroup.map_injective (MulAut.conj x).injective h

lemma conj_mem_diag {x : Y} (hx : ψ x = x) {d : Y} (hd : d ∈ diag hψ hS hnt) :
    x * d * x⁻¹ ∈ diag hψ (isComponent_map_mulEquiv (MulAut.conj x) hS)
      (orb_ne_conj_of_fixed hψ hS hnt hx) := by
  obtain ⟨a, rfl⟩ := hd
  rw [deltaHom_apply, conj_deltaFun hx]
  exact ⟨⟨x * a * x⁻¹, ⟨a, a.2, rfl⟩⟩, rfl⟩

/-- Diagonals of two different `ψ`-orbits of components commute elementwise. -/
lemma diag_commute {T : Subgroup Y} (hT : IsComponent T) (hntT : orb ψ T 1 ≠ T)
    (hdisj : ∀ k < p, orb ψ S k ≠ T) :
    ∀ d ∈ diag hψ hS hnt, ∀ e ∈ diag hψ hT hntT, Commute d e := by
  have hne : ∀ i < p, ∀ j < p, orb ψ S i ≠ orb ψ T j := by
    intro i hi j hj h
    apply hdisj ((p - j + i) % p) (Nat.mod_lt _ hp.out.pos)
    rw [← orb_mod hψ, orb_add, h, ← orb_add, show p - j + j = p by omega, orb_p hψ]
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [deltaHom_apply, deltaHom_apply]
  refine Commute.list_prod_left _ _ fun x hx => Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
  rw [List.mem_range] at hi hj
  exact component_commute (isComponent_orb hψ hS hnt i) (isComponent_orb hψ hT hntT j)
    (hne i hi j hj) _ (mem_orb_of_mem ψ a.2 i) _ (mem_orb_of_mem ψ b.2 j)

lemma diag_le_layer : diag hψ hS hnt ≤ layer Y := by
  rintro _ ⟨a, rfl⟩
  rw [deltaHom_apply]
  refine (layer Y).list_prod_mem fun y hy => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
  exact component_le_layer (isComponent_orb hψ hS hnt i) (mem_orb_of_mem ψ a.2 i)

end Delta

end CFSGOutside.KhukhroShumyatskyFixedPointLength
