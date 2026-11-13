
import CFSGOutside.Corpus.Schreier
import CFSGOutside.KimmerleKonovalov.Definitions

section

/-!
# Kimmerle–Konovalov, Corollary 2.6 (IJAC 27 (2017) 619–631)

W. Kimmerle and A. Konovalov, *On the Gruenberg–Kegel graph of integral group rings of finite
groups*, Internat. J. Algebra Comput. 27 (2017), no. 6, 619–631, DOI 10.1142/S0218196717500308,
arXiv:1612.05025.

Everything the corollary rests on is proved here from Mathlib, with only the Schreier conjecture
(the corpus theorem `CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds`, assumed as the class
`CFSGOutside.Corpus.Schreier` and fed by the classification hypothesis `hCFSG`) taken from the
AxiomMath/CFSG corpus:

* `berman_higman`: a torsion `u ≠ 1` of `ℤG` with augmentation one has `u_1 = 0`
  (trace of left multiplication on `ℂG`, eigenvalues and the minimal polynomial);
* `mrsw`: Marciniak–Ritter–Sehgal–Weiss, Theorem 2.7: `ε_x(u) = 0` when a prime divides `o(x)`
  but not `o(u)` (necklace expansion of `u ^ (r ^ t)` and rotation orbits, `pow_dvd_sum_pow`);
* `vertex_iff`: the vertex sets of `Π(V(ℤG))` and `Π(G)` agree;
* `prop22`: Proposition 2.2;
* `cor23`, `pq_of_solvable`: Corollary 2.3 and (PQ) for soluble groups;
* `cor26`, `cor26_abstract`: Corollary 2.6.
-/

noncomputable section

open MonoidAlgebra Finset

namespace KimmerleKonovalov

open scoped Classical

/-! ## Coefficients of powers: the necklace expansion -/

section Coeff

variable {G : Type*} [Group G] [Fintype G]

theorem aug_apply (a : MonoidAlgebra ℤ G) : aug G a = ∑ g, a.coeff g := by
  simp [aug, MonoidAlgebra.lift_apply, Finsupp.sum_fintype]

theorem coeff_mul_eq (x y : MonoidAlgebra ℤ G) (h : G) :
    (x * y).coeff h = ∑ g, x.coeff g * y.coeff (g⁻¹ * h) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]; simp

/-- The ordered product of a tuple. -/
def tprod {m : ℕ} (f : Fin m → G) : G := (List.ofFn f).prod

/-- The coefficient weight `∏ a_{f i}` of a tuple. -/
def wt (a : MonoidAlgebra ℤ G) {m : ℕ} (f : Fin m → G) : ℤ := ∏ i, a.coeff (f i)

theorem tprod_cons {m : ℕ} (g : G) (f : Fin m → G) :
    tprod (Fin.cons g f : Fin (m + 1) → G) = g * tprod f := by
  simp [tprod, List.ofFn_succ]

theorem wt_cons (a : MonoidAlgebra ℤ G) {m : ℕ} (g : G) (f : Fin m → G) :
    wt a (Fin.cons g f : Fin (m + 1) → G) = a.coeff g * wt a f := by
  simp [wt, Fin.prod_univ_succ]

theorem coeff_pow (a : MonoidAlgebra ℤ G) (m : ℕ) (h : G) :
    (a ^ m).coeff h = ∑ f : Fin m → G, if tprod f = h then wt a f else 0 := by
  induction m generalizing h with
  | zero =>
    simp [tprod, wt, MonoidAlgebra.one_def, MonoidAlgebra.single_apply, Finsupp.single_apply]
  | succ m ih =>
    rw [pow_succ', coeff_mul_eq, ← Equiv.sum_comp (Fin.consEquiv fun _ => G),
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    show _ = (if tprod (Fin.cons g f : Fin (m + 1) → G) = h then
      wt a (Fin.cons g f : Fin (m + 1) → G) else 0)
    rw [tprod_cons, wt_cons]
    by_cases hf : tprod f = g⁻¹ * h
    · rw [if_pos hf, if_pos (by rw [hf]; group)]
    · rw [if_neg hf, if_neg (fun h' => hf (by rw [← h']; group)), mul_zero]

theorem sum_pred_coeff_pow (P : G → Prop) [DecidablePred P] (a : MonoidAlgebra ℤ G) (m : ℕ) :
    (∑ h, if P h then (a ^ m).coeff h else 0) =
      ∑ f : Fin m → G, if P (tprod f) then wt a f else 0 := by
  simp_rw [coeff_pow]
  rw [show (∑ h, if P h then ∑ f : Fin m → G, (if tprod f = h then wt a f else 0) else 0) =
      ∑ h, ∑ f : Fin m → G, if tprod f = h then (if P h then wt a f else 0) else 0 from
    Finset.sum_congr rfl fun h _ => by split_ifs with hP <;> simp [hP]]
  rw [Finset.sum_comm]
  simp

end Coeff

/-! ## The rotation of tuples -/

section Rotation

open Fin.NatCast

variable {G : Type*} [Group G] {m : ℕ} [NeZero m]

/-- Cyclic rotation of an `m`-tuple. -/
def rot : Equiv.Perm (Fin m → G) where
  toFun f i := f (i + 1)
  invFun f i := f (i - 1)
  left_inv f := by funext i; simp
  right_inv f := by funext i; simp

theorem rot_apply (f : Fin m → G) (i : Fin m) : rot f i = f (i + 1) := rfl

theorem rot_pow_apply (k : ℕ) (f : Fin m → G) (i : Fin m) :
    ((rot : Equiv.Perm (Fin m → G)) ^ k) f i = f (i + (k : Fin m)) := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih, rot_apply, Nat.cast_succ, add_assoc]

theorem rot_pow_card : (rot : Equiv.Perm (Fin m → G)) ^ m = 1 := by
  ext f i
  rw [rot_pow_apply, Fin.natCast_self, add_zero]; rfl

theorem isPeriodicPt_rot (f : Fin m → G) :
    Function.IsPeriodicPt (rot : Equiv.Perm (Fin m → G)) m f := by
  show (⇑rot)^[m] f = f
  rw [Equiv.Perm.iterate_eq_pow, rot_pow_card]; rfl

theorem wt_rot [Fintype G] (a : MonoidAlgebra ℤ G) (f : Fin m → G) : wt a (rot f) = wt a f :=
  Equiv.prod_comp (Equiv.addRight (1 : Fin m)) (fun i => a.coeff (f i))

theorem tprod_rot (f : Fin m → G) : tprod (rot f) = (f 0)⁻¹ * tprod f * f 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by have := NeZero.ne m; omega⟩
  have h1 : tprod f = f 0 * tprod (fun i : Fin n => f i.succ) := by
    simp [tprod, List.ofFn_succ]
  have h2 : tprod (rot f) = tprod (fun i : Fin n => f i.succ) * f 0 := by
    simp only [tprod]
    rw [List.ofFn_succ']
    simp only [List.concat_eq_append, List.prod_append, List.prod_singleton, rot_apply,
      Fin.coeSucc_eq_succ, Fin.last_add_one]
  rw [h2, h1]; group

/-- A tuple fixed by `rot ^ k` is constant on residues mod `k`. -/
theorem periodic_apply {k : ℕ} (hk : 0 < k) (hkm : k ≤ m) (f : Fin m → G)
    (hf : ((rot : Equiv.Perm (Fin m → G)) ^ k) f = f) (i : Fin m) :
    f i = f ⟨i % k, lt_of_lt_of_le (Nat.mod_lt _ hk) hkm⟩ := by
  have step : ∀ j : Fin m, f (j + (k : Fin m)) = f j := fun j => by
    rw [← rot_pow_apply k f j, hf]
  have key : ∀ c j : ℕ, (h : j + k * c < m) → f ⟨j + k * c, h⟩ = f ⟨j, by omega⟩ := by
    intro c
    induction c with
    | zero => intro j h; rfl
    | succ c ih =>
      intro j h
      have hkc : k * (c + 1) = k * c + k := by ring
      have hlt : j + k * c < m := by omega
      have hkm' : k < m := by
        have : k ≤ k * (c + 1) := Nat.le_mul_of_pos_right k (Nat.succ_pos c)
        omega
      calc f ⟨j + k * (c + 1), h⟩ = f (⟨j + k * c, hlt⟩ + (k : Fin m)) := by
            congr 1
            ext
            simp only [Fin.val_add, Fin.val_natCast]
            rw [Nat.mod_eq_of_lt hkm', Nat.mod_eq_of_lt (show j + k * c + k < m by omega)]
            omega
        _ = f ⟨j + k * c, hlt⟩ := step _
        _ = f ⟨j, by omega⟩ := ih j hlt
  have hi : i.val % k + k * (i.val / k) = i.val := Nat.mod_add_div _ _
  have := key (i.val / k) (i.val % k) (by rw [hi]; exact i.isLt)
  rw [← this]
  congr 1
  ext; exact hi.symm

/-- A tuple fixed by `rot ^ k` with `l * k = m` has product an `l`-th power. -/
theorem tprod_eq_pow_of_periodic {k l : ℕ} (hkl : l * k = m) (f : Fin m → G)
    (hf : ((rot : Equiv.Perm (Fin m → G)) ^ k) f = f) : ∃ y : G, tprod f = y ^ l := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; omega
    · exact h
  have hl : 0 < l := by
    rcases Nat.eq_zero_or_pos l with h | h
    · subst h; omega
    · exact h
  have hkm : k ≤ m := by rw [← hkl]; exact Nat.le_mul_of_pos_left k hl
  let b : Fin k → G := fun j => f ⟨j, lt_of_lt_of_le j.isLt hkm⟩
  refine ⟨tprod b, ?_⟩
  have hrep : (fun i : Fin (l * k) => f (Fin.cast hkl i)) = Fin.repeat l b := by
    funext i
    rw [Fin.repeat_apply, periodic_apply hk hkm f hf]
    rfl
  simp only [tprod]
  rw [List.ofFn_congr hkl.symm f]
  have : (fun i : Fin (l * k) => f (Fin.cast hkl.symm.symm i)) = Fin.repeat l b := hrep
  rw [this, List.ofFn_fin_repeat, List.prod_flatten, List.map_replicate, List.prod_replicate]

end Rotation

/-! ## Sums over rotation-invariant sets -/

theorem dvd_sum_of_dvd_minimalPeriod {X : Type*} [Fintype X] (σ : Equiv.Perm X) (F : X → ℤ)
    (hF : ∀ x, F (σ x) = F x) (d : ℕ)
    (hd : ∀ x, F x ≠ 0 → d ∣ Function.minimalPeriod σ x) :
    (d : ℤ) ∣ ∑ x, F x := by
  have hzpow : ∀ (k : ℤ) (x : X), F ((σ ^ k) x) = F x := by
    intro k
    induction k using Int.induction_on with
    | zero => intro x; simp
    | succ k ih => intro x; rw [zpow_add_one, Equiv.Perm.mul_apply, ih, hF]
    | pred k ih =>
      intro x
      rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
      rw [← hF (σ⁻¹ x)]
      simp
  let Q := MulAction.orbitRel.Quotient (Subgroup.zpowers σ) X
  rw [← Finset.sum_fiberwise Finset.univ (fun x => (Quotient.mk'' x : Q)) F]
  apply Finset.dvd_sum
  intro c _
  induction c using Quotient.inductionOn' with
  | h x0 =>
  have hmem : ∀ x, (Quotient.mk'' x : Q) = Quotient.mk'' x0 ↔
      x ∈ MulAction.orbit (Subgroup.zpowers σ) x0 := fun x => by
    rw [Quotient.eq'']; exact MulAction.orbitRel_apply
  have hconst : ∀ x ∈ (Finset.univ.filter fun x => (Quotient.mk'' x : Q) = Quotient.mk'' x0),
      F x = F x0 := by
    intro x hx
    rw [Finset.mem_filter, hmem] at hx
    obtain ⟨⟨g, hg⟩, rfl⟩ := hx.2
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact hzpow k x0
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  by_cases h0 : F x0 = 0
  · simp [h0]
  apply Dvd.dvd.mul_right
  have hcard : (Finset.univ.filter fun x => (Quotient.mk'' x : Q) = Quotient.mk'' x0).card =
      Function.minimalPeriod σ x0 := by
    rw [show Function.minimalPeriod σ x0 = Function.minimalPeriod (fun x => σ • x) x0 from rfl,
      MulAction.minimalPeriod_eq_card, ← Set.toFinset_card]
    congr 1
    ext x
    simp [hmem]
  rw [hcard]
  exact_mod_cast hd x0 h0

/-! ## Conjugation-invariant predicates -/

section Conj

variable {G : Type*} [Group G]

/-- Conjugation-invariant predicates on `G`. -/
def ConjInv (P : G → Prop) : Prop := ∀ g c : G, P (c⁻¹ * g * c) ↔ P g

theorem orderOf_conj' (c g : G) : orderOf (c⁻¹ * g * c) = orderOf g := by
  have := orderOf_injective (MulAut.conj c⁻¹).toMonoidHom (MulEquiv.injective _) g
  simpa [MulAut.conj_apply] using this

theorem orderOf_eq_of_isConj {g x : G} (h : IsConj g x) : orderOf g = orderOf x := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  have := orderOf_conj' c⁻¹ g
  simpa using this.symm

theorem conjInv_isConj (x : G) : ConjInv (fun g => IsConj g x) := by
  intro g c
  have : IsConj (c⁻¹ * g * c) g := isConj_iff.2 ⟨c, by group⟩
  exact ⟨fun h => this.symm.trans h, fun h => this.trans h⟩

end Conj

/-! ## Necklace congruences and the theorem of Marciniak–Ritter–Sehgal–Weiss -/

section Necklace

open Fin.NatCast

variable {G : Type*} [Group G] [Fintype G]

theorem F_rot (P : G → Prop) [DecidablePred P] (hP : ConjInv P) (a : MonoidAlgebra ℤ G)
    {m : ℕ} [NeZero m]
    (f : Fin m → G) :
    (if P (tprod (rot f)) then wt a (rot f) else 0) = if P (tprod f) then wt a f else 0 := by
  have := hP (tprod f) (f 0)
  simp only [tprod_rot, this, wt_rot]

theorem tprod_const {m : ℕ} (g : G) : tprod (fun _ : Fin m => g) = g ^ m := by
  simp [tprod, List.ofFn_const, List.prod_replicate]

theorem wt_const (a : MonoidAlgebra ℤ G) {m : ℕ} (g : G) :
    wt a (fun _ : Fin m => g) = a.coeff g ^ m := by
  simp [wt]

/-- The congruence `ε_S(a^q) ≡ Σ_{g^q ∈ S} a_g (mod q)` for a prime `q` and a union `S` of
conjugacy classes. -/
theorem sum_pow_prime_modEq (q : ℕ) [hq : Fact q.Prime] (a : MonoidAlgebra ℤ G) (P : G → Prop)
    [DecidablePred P] (hP : ConjInv P) :
    (((∑ h, if P h then (a ^ q).coeff h else 0 : ℤ)) : ZMod q) =
      ∑ g, if P (g ^ q) then (a.coeff g : ZMod q) else 0 := by
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  rw [sum_pred_coeff_pow]
  let F : (Fin q → G) → ℤ := fun f => if P (tprod f) then wt a f else 0
  let C : (Fin q → G) → Prop := fun f => ∀ i, f i = f 0
  have hsplit : ∑ f, F f = ∑ f, (if C f then F f else 0) + ∑ f, (if C f then 0 else F f) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    split_ifs <;> simp
  have hCrot : ∀ f, C (rot f) ↔ C f := by
    intro f
    constructor
    · intro h i
      have h1 := h (i - 1)
      have h2 := h (0 - 1)
      simp only [rot_apply, sub_add_cancel] at h1 h2
      rw [h1, ← h2]
    · intro h i
      simp only [rot_apply]
      rw [h (i + 1), h (0 + 1)]
  have hnc : (q : ℤ) ∣ ∑ f, (if C f then 0 else F f) := by
    apply dvd_sum_of_dvd_minimalPeriod rot
    · intro f
      have := F_rot P hP a f
      by_cases hc : C f
      · rw [if_pos hc, if_pos ((hCrot f).2 hc)]
      · rw [if_neg hc, if_neg (fun h => hc ((hCrot f).1 h))]
        exact this
    · intro f hf
      have hnC : ¬ C f := by intro h; simp [h] at hf
      have hdvd : Function.minimalPeriod rot f ∣ q := (isPeriodicPt_rot f).minimalPeriod_dvd
      rcases (Nat.dvd_prime hq.out).1 hdvd with h1 | h1
      · exfalso
        apply hnC
        have hrf : ((rot : Equiv.Perm (Fin q → G)) ^ 1) f = f := by
          have := Function.isPeriodicPt_minimalPeriod rot f
          rw [h1] at this
          rw [pow_one]; exact this
        intro i
        rw [periodic_apply one_pos (Nat.one_le_iff_ne_zero.2 (NeZero.ne q)) f hrf i,
          periodic_apply one_pos (Nat.one_le_iff_ne_zero.2 (NeZero.ne q)) f hrf 0]
        congr 1
        exact Fin.ext (by simp [Nat.mod_one])
      · rw [h1]
  have hc : ∑ f, (if C f then F f else 0) = ∑ g, F (fun _ => g) := by
    rw [← Finset.sum_filter]
    have himg : Finset.univ.filter C = Finset.univ.image (fun g : G => fun _ : Fin q => g) := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro h; exact ⟨f 0, funext fun i => (h i).symm⟩
      · rintro ⟨g, rfl⟩ i; rfl
    rw [himg, Finset.sum_image]
    intro g _ g' _ h
    exact congrFun h 0
  show ((∑ f, F f : ℤ) : ZMod q) = _
  rw [hsplit, hc, Int.cast_add]
  obtain ⟨k, hk⟩ := hnc
  rw [hk]
  simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero, Int.cast_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [F, tprod_const, wt_const]
  split_ifs <;> simp [ZMod.pow_card]

theorem not_dvd_orderOf_pow_card {r : ℕ} (hr : r.Prime) (y : G) :
    ¬ r ∣ orderOf (y ^ (r ^ Fintype.card G)) := by
  intro hdiv
  have hN0 : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  obtain ⟨e, N', hN', hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 r hr.ne_one
  have he : e ≤ Fintype.card G := by
    have h1 : r ^ e ≤ Fintype.card G := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) ⟨N', hN⟩
    have h2 : e < r ^ e := Nat.lt_pow_self hr.one_lt
    omega
  have hpow : (y ^ (r ^ Fintype.card G)) ^ N' = 1 := by
    rw [← pow_mul]
    have h3 : r ^ e * N' ∣ r ^ Fintype.card G * N' :=
      Nat.mul_dvd_mul_right (Nat.pow_dvd_pow r he) N'
    rw [← hN] at h3
    obtain ⟨c, hc⟩ := h3
    rw [hc, pow_mul, pow_card_eq_one, one_pow]
  exact hN' (hdiv.trans (orderOf_dvd_of_pow_eq_one hpow))

/-- The `r`-adic congruence: if every element of the union `S` of classes has order divisible
by `r`, then `r ^ (t - |G|)` divides `ε_S(a ^ (r ^ t))`. -/
theorem pow_dvd_sum_pow {r : ℕ} (hr : r.Prime) (t : ℕ) (a : MonoidAlgebra ℤ G)
    (P : G → Prop)
    [DecidablePred P] (hP : ConjInv P) (hPr : ∀ h, P h → r ∣ orderOf h) :
    (r : ℤ) ^ (t - Fintype.card G) ∣ ∑ h, if P h then (a ^ (r ^ t)).coeff h else 0 := by
  haveI : NeZero (r ^ t) := ⟨pow_ne_zero _ hr.ne_zero⟩
  rw [sum_pred_coeff_pow]
  by_cases htN : t < Fintype.card G
  · rw [Nat.sub_eq_zero_of_le htN.le, pow_zero]; exact one_dvd _
  push Not at htN
  have key := dvd_sum_of_dvd_minimalPeriod (rot : Equiv.Perm (Fin (r ^ t) → G))
    (fun f => if P (tprod f) then wt a f else 0) (fun f => F_rot P hP a f)
    (r ^ (t - Fintype.card G)) ?_
  · exact_mod_cast key
  intro f hf
  have hPf : P (tprod f) := by by_contra h; simp [h] at hf
  obtain ⟨j, hj, hmp⟩ := (Nat.dvd_prime_pow hr).1 (isPeriodicPt_rot f).minimalPeriod_dvd
  rw [hmp]
  by_cases hjt : t - Fintype.card G ≤ j
  · exact Nat.pow_dvd_pow r hjt
  exfalso
  push Not at hjt
  have hper : ((rot : Equiv.Perm (Fin (r ^ t) → G)) ^ (r ^ (t - Fintype.card G))) f = f := by
    have h1 := (Function.isPeriodicPt_minimalPeriod rot f).mul_const
      (r ^ (t - Fintype.card G - j))
    rw [hmp, ← pow_add, show j + (t - Fintype.card G - j) = t - Fintype.card G by omega] at h1
    rw [← Equiv.Perm.iterate_eq_pow]; exact h1
  obtain ⟨y, hy⟩ := tprod_eq_pow_of_periodic (l := r ^ Fintype.card G)
    (by rw [← pow_add]; congr 1; omega) f hper
  exact not_dvd_orderOf_pow_card hr y (hy ▸ hPr _ hPf)

theorem partialAug_eq_sum (x : G) (a : MonoidAlgebra ℤ G) :
    partialAug G x a = ∑ g, if IsConj g x then a.coeff g else 0 := by
  rw [partialAug, Finset.sum_filter]

/-- **Marciniak–Ritter–Sehgal–Weiss, Theorem 2.7.** If `a ∈ ℤG` has finite order and a
prime divides `o(x)` but not `o(a)`, then the partial augmentation `ε_x(a)` vanishes. -/
theorem mrsw (a : MonoidAlgebra ℤ G) (ha : 0 < orderOf a) (x : G) {r : ℕ} (hr : r.Prime)
    (hrx : r ∣ orderOf x) (hra : ¬ r ∣ orderOf a) : partialAug G x a = 0 := by
  have hcop : r.Coprime (orderOf a) := (Nat.Prime.coprime_iff_not_dvd hr).2 hra
  have hfix : ∀ k, a ^ (r ^ ((orderOf a).totient * k)) = a := by
    intro k
    have hmod : r ^ ((orderOf a).totient * k) % orderOf a = 1 % orderOf a := by
      have := (Nat.ModEq.pow_totient hcop).pow k
      rw [← pow_mul, one_pow] at this; exact this
    rw [← pow_mod_orderOf, hmod, pow_mod_orderOf, pow_one]
  have ht : Fintype.card G + (partialAug G x a).natAbs + 1 ≤
      (orderOf a).totient * (Fintype.card G + (partialAug G x a).natAbs + 1) :=
    Nat.le_mul_of_pos_left _ (Nat.totient_pos.2 ha)
  have hdvd := pow_dvd_sum_pow hr ((orderOf a).totient *
    (Fintype.card G + (partialAug G x a).natAbs + 1)) a (fun g => IsConj g x) (conjInv_isConj x)
    (fun h hh => (orderOf_eq_of_isConj hh) ▸ hrx)
  rw [hfix] at hdvd
  rw [partialAug_eq_sum]
  refine Int.eq_zero_of_abs_lt_dvd (by convert hdvd) ?_
  rw [← partialAug_eq_sum]
  have h1 := Nat.lt_pow_self (n := (orderOf a).totient *
    (Fintype.card G + (partialAug G x a).natAbs + 1) - Fintype.card G) hr.one_lt
  have h2 : (partialAug G x a).natAbs < (orderOf a).totient *
      (Fintype.card G + (partialAug G x a).natAbs + 1) - Fintype.card G := by omega
  rw [Int.abs_eq_natAbs]
  exact_mod_cast lt_trans h2 h1

end Necklace

/-! ## The Berman–Higman theorem -/

section BermanHigman

variable {G : Type*} [Group G] [Fintype G]

theorem complex_eq_one_of_norm_re {z : ℂ} (hn : ‖z‖ = 1) (hre : z.re = 1) : z = 1 := by
  have h := Complex.normSq_eq_norm_sq z
  rw [Complex.normSq_apply, hn, hre] at h
  have : z.im * z.im = 0 := by linarith
  exact Complex.ext hre (mul_self_eq_zero.1 this)

theorem multiset_sum_re (M : Multiset ℂ) : (M.map Complex.re).sum = M.sum.re := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih => simp [ih]

/-- **Berman–Higman.** A torsion element `u ≠ 1` of `ℤG` with augmentation one has
coefficient zero at the identity. -/
theorem berman_higman (u : MonoidAlgebra ℤ G) (hu : 0 < orderOf u) (haug : aug G u = 1)
    (hne : u ≠ 1) : u.coeff 1 = 0 := by
  let ι : MonoidAlgebra ℤ G →+* MonoidAlgebra ℂ G :=
    MonoidAlgebra.mapRingHom G (Int.castRingHom ℂ)
  have hι : ∀ x g, (ι x).coeff g = (x.coeff g : ℂ) := fun x g =>
    MonoidAlgebra.mapRangeRingHom_apply _ _ _
  let T : Module.End ℂ (MonoidAlgebra ℂ G) := Algebra.lmul ℂ (MonoidAlgebra ℂ G) (ι u)
  have hT : ∀ x, T x = ι u * x := fun x => rfl
  have hTn : T ^ orderOf u = 1 := by
    show (Algebra.lmul ℂ (MonoidAlgebra ℂ G) (ι u)) ^ orderOf u = 1
    rw [← map_pow, ← map_pow, pow_orderOf_eq_one, map_one, map_one]
  -- the trace of left multiplication
  have htr : LinearMap.trace ℂ _ T = (Fintype.card G : ℂ) * (u.coeff 1 : ℂ) := by
    rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis G ℂ), Matrix.trace]
    have : ∀ g : G,
        (LinearMap.toMatrix (MonoidAlgebra.basis G ℂ) (MonoidAlgebra.basis G ℂ) T) g g =
          (u.coeff 1 : ℂ) := by
      intro g
      rw [LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply, hT]
      show (ι u * single g 1).coeff g = _
      rw [MonoidAlgebra.mul_single_apply, mul_inv_cancel, mul_one, hι]
    simp only [Matrix.diag, this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  set R := (LinearMap.charpoly T).roots with hR
  have hsplit := IsAlgClosed.splits (LinearMap.charpoly T)
  have hsum : (Fintype.card G : ℂ) * (u.coeff 1 : ℂ) = R.sum := by
    rw [← htr, Module.End.trace_eq_sum_roots_charpoly_of_splits hsplit]
  have hcard : R.card = Fintype.card G := by
    rw [hR, ← hsplit.natDegree_eq_card_roots, LinearMap.charpoly_natDegree,
      Module.finrank_eq_card_basis (MonoidAlgebra.basis G ℂ)]
  have hroot : ∀ μ ∈ R, μ ^ orderOf u = 1 := by
    intro μ hμ
    have hev : T.HasEigenvalue μ := (Module.End.hasEigenvalue_iff_isRoot_charpoly T μ).2
      (Polynomial.isRoot_of_mem_roots hμ)
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    have hpow : ∀ k : ℕ, (T ^ k) v = μ ^ k • v := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, Module.End.mul_apply, hv.apply_eq_smul, map_smul, ih, smul_smul, pow_succ,
          mul_comm]
    have h1 := hpow (orderOf u)
    rw [hTn, Module.End.one_apply] at h1
    have h2 : (μ ^ orderOf u - 1) • v = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    rcases smul_eq_zero.1 h2 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hv.2
  have hnorm : ∀ μ ∈ R, ‖μ‖ = 1 := fun μ hμ =>
    Complex.norm_eq_one_of_pow_eq_one (hroot μ hμ) hu.ne'
  set c := u.coeff 1 with hc
  have hD : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  -- real parts
  have hresum : ∀ s : ℤ, (R.map fun μ => ((s : ℂ) * μ).re).sum =
      (Fintype.card G : ℝ) * ((s * c : ℤ) : ℝ) := by
    intro s
    have hmm : (R.map fun μ => ((s : ℂ) * μ).re) =
        (R.map fun μ => (s : ℂ) * μ).map Complex.re := by
      rw [Multiset.map_map]; rfl
    rw [hmm, multiset_sum_re,
      Multiset.sum_map_mul_left, Multiset.map_id', ← hsum]
    simp [Complex.mul_re]
    ring
  have hrele : ∀ s : ℤ, |s| = 1 → ∀ μ ∈ R, ((s : ℂ) * μ).re ≤ 1 := by
    intro s hs μ hμ
    calc ((s : ℂ) * μ).re ≤ ‖(s : ℂ) * μ‖ := Complex.re_le_norm _
      _ = 1 := by
        rw [norm_mul, hnorm μ hμ, mul_one, Complex.norm_intCast]
        exact_mod_cast hs
  have hbound : ∀ s : ℤ, |s| = 1 → s * c ≤ 1 := by
    intro s hs
    have h1 : (R.map fun μ => ((s : ℂ) * μ).re).sum ≤ (R.map fun _ => (1 : ℝ)).sum :=
      Multiset.sum_map_le_sum_map _ _ (hrele s hs)
    rw [hresum, Multiset.map_const', Multiset.sum_replicate, hcard, nsmul_eq_mul, mul_one] at h1
    have h2 : ((s * c : ℤ) : ℝ) ≤ 1 := by
      by_contra h
      push Not at h
      nlinarith
    exact_mod_cast h2
  by_contra hc0
  have hc1 : |c| = 1 := by
    have h1 := hbound 1 (by simp)
    have h2 := hbound (-1) (by simp)
    rcases lt_trichotomy c 0 with h | h | h
    · rw [abs_of_neg h]; omega
    · exact absurd h hc0
    · rw [abs_of_pos h]; omega
  have hcc : c * c = 1 := by
    rcases abs_eq (zero_le_one) |>.1 hc1 with h | h <;> rw [h] <;> norm_num
  -- every eigenvalue equals `c`
  have hall : ∀ μ ∈ R, μ = (c : ℂ) := by
    by_contra hex
    push Not at hex
    obtain ⟨μ0, hμ0, hne0⟩ := hex
    have hlt : ((c : ℂ) * μ0).re < 1 := by
      rcases (hrele c hc1 μ0 hμ0).lt_or_eq with h | h
      · exact h
      · exfalso
        have h1 : (c : ℂ) * μ0 = 1 := complex_eq_one_of_norm_re
          (by rw [norm_mul, hnorm μ0 hμ0, mul_one, Complex.norm_intCast]; exact_mod_cast hc1) h
        apply hne0
        have hcc' : (c : ℂ) * c = 1 := by exact_mod_cast hcc
        calc μ0 = (c : ℂ) * ((c : ℂ) * μ0) := by rw [← mul_assoc, hcc', one_mul]
          _ = c := by rw [h1, mul_one]
    have h1 : (R.map fun μ => ((c : ℂ) * μ).re).sum < (R.map fun _ => (1 : ℝ)).sum :=
      Multiset.sum_lt_sum (fun μ hμ => hrele c hc1 μ hμ) ⟨μ0, hμ0, hlt⟩
    rw [hresum, Multiset.map_const', Multiset.sum_replicate, hcard, nsmul_eq_mul, mul_one, hcc]
      at h1
    simp at h1
  -- the minimal polynomial of `T` is `X - c`
  have hint : IsIntegral ℂ T := IsIntegral.of_finite ℂ T
  have hmin_dvd : minpoly ℂ T ∣ Polynomial.X ^ orderOf u - Polynomial.C 1 :=
    minpoly.dvd ℂ T (by simp [hTn])
  have hsep : (minpoly ℂ T).Separable :=
    (Polynomial.separable_X_pow_sub_C 1 (by exact_mod_cast hu.ne') one_ne_zero).of_dvd hmin_dvd
  have hmroots : ∀ ρ ∈ (minpoly ℂ T).roots, ρ = (c : ℂ) := by
    intro ρ hρ
    have hev : T.HasEigenvalue ρ :=
      Module.End.hasEigenvalue_of_isRoot (Polynomial.isRoot_of_mem_roots hρ)
    apply hall
    rw [hR, Polynomial.mem_roots (LinearMap.charpoly_monic T).ne_zero]
    exact (Module.End.hasEigenvalue_iff_isRoot_charpoly T ρ).1 hev
  have hrep : (minpoly ℂ T).roots = Multiset.replicate (minpoly ℂ T).roots.card (c : ℂ) :=
    Multiset.eq_replicate.2 ⟨rfl, hmroots⟩
  have hle : (minpoly ℂ T).roots.card ≤ 1 := by
    have hnd := Polynomial.nodup_roots hsep
    rw [Multiset.nodup_iff_count_le_one] at hnd
    have := hnd (c : ℂ)
    rwa [hrep, Multiset.count_replicate_self] at this
  have hpos : 0 < (minpoly ℂ T).roots.card := by
    rw [← (IsAlgClosed.splits (minpoly ℂ T)).natDegree_eq_card_roots]
    exact minpoly.natDegree_pos hint
  have hcard1 : (minpoly ℂ T).roots.card = 1 := by omega
  have hmin : minpoly ℂ T = Polynomial.X - Polynomial.C (c : ℂ) := by
    rw [(IsAlgClosed.splits (minpoly ℂ T)).eq_prod_roots_of_monic (minpoly.monic hint), hrep,
      hcard1]
    simp
  have hTc : T = algebraMap ℂ _ (c : ℂ) := by
    have := minpoly.aeval ℂ T
    rw [hmin] at this
    simpa [sub_eq_zero] using this
  -- hence `u = c • 1`, so `u = 1`
  have hu1 : ι u = (c : ℂ) • (1 : MonoidAlgebra ℂ G) := by
    have := LinearMap.congr_fun hTc 1
    rw [hT, mul_one, Module.algebraMap_end_apply] at this
    exact this
  have hcoeff : ∀ g, g ≠ 1 → u.coeff g = 0 := by
    intro g hg
    have := congrArg (fun x : MonoidAlgebra ℂ G => x.coeff g) hu1
    simp only [hι, MonoidAlgebra.coeff_smul, MonoidAlgebra.one_def, Finsupp.smul_apply,
      MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (Ne.symm hg), smul_zero] at this
    exact_mod_cast this
  have hcone : c = 1 := by
    rw [aug_apply, Finset.sum_eq_single 1 (fun g _ hg => hcoeff g hg) (by simp)] at haug
    exact haug
  apply hne
  apply MonoidAlgebra.ext
  ext g
  rw [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases hg : g = 1
  · subst hg; rw [if_pos rfl, ← hc, hcone]
  · rw [if_neg (Ne.symm hg), hcoeff g hg]

end BermanHigman

/-! ## Normalised units, partial augmentations and vertices -/

section Units

variable {G : Type*} [Group G]

/-- The underlying element of `ℤG` of a normalised unit. -/
def val (u : V G) : MonoidAlgebra ℤ G :=
  ((u : (MonoidAlgebra ℤ G)ˣ) : MonoidAlgebra ℤ G)

theorem mem_V {u : (MonoidAlgebra ℤ G)ˣ} :
    u ∈ V G ↔ aug G (u : MonoidAlgebra ℤ G) = 1 := by
  simp [V, MonoidHom.mem_ker, Units.ext_iff]

theorem orderOf_val (u : V G) : orderOf (val u) = orderOf u := by
  rw [val, orderOf_units, Subgroup.orderOf_coe]

theorem aug_val (u : V G) : aug G (val u) = 1 := mem_V.1 u.2

/-- The trivial units `G → V(ℤG)`. -/
def ofV : G →* V G :=
  (MonoidHom.toHomUnits (MonoidAlgebra.of ℤ G)).codRestrict (V G) (fun g => mem_V.2 (by
    simp [aug, MonoidAlgebra.of_apply, MonoidAlgebra.lift_single]))

theorem ofV_injective : Function.Injective (ofV (G := G)) := by
  intro g h hgh
  apply MonoidAlgebra.of_injective (R := ℤ)
  have := congrArg val hgh
  exact this

theorem hasEltOfOrder_V {n : ℕ} (h : HasEltOfOrder G n) : HasEltOfOrder (V G) n := by
  obtain ⟨g, hg⟩ := h
  exact ⟨ofV g, by rw [orderOf_injective _ ofV_injective, hg]⟩

theorem hasEltOfOrder_of_dvd [Finite G] {n : ℕ} (g : G) (h : n ∣ orderOf g) :
    HasEltOfOrder G n := by
  have hpos := orderOf_pos g
  have hn : 0 < n := Nat.pos_of_dvd_of_pos h hpos
  refine ⟨g ^ (orderOf g / n), ?_⟩
  rw [orderOf_pow_of_dvd (Nat.div_pos (Nat.le_of_dvd hpos h) hn).ne' (Nat.div_dvd_of_dvd h),
    Nat.div_div_self h hpos.ne']

theorem isConj_pred {P : G → Prop} (hP : ConjInv P) {g x : G} (h : IsConj g x) : P g ↔ P x := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  have := hP g c⁻¹
  rw [inv_inv] at this
  exact this.symm

theorem conjInv_orderOf (Φ : ℕ → Prop) : ConjInv (fun g : G => Φ (orderOf g)) := by
  intro g c; simp only [orderOf_conj']

theorem ConjInv.not {P : G → Prop} (hP : ConjInv P) : ConjInv (fun g => ¬ P g) := by
  intro g c; simp only [hP g c]

theorem ConjInv.and {P Q : G → Prop} (hP : ConjInv P) (hQ : ConjInv Q) :
    ConjInv (fun g => P g ∧ Q g) := by
  intro g c; simp only [hP g c, hQ g c]

theorem ConjInv.or {P Q : G → Prop} (hP : ConjInv P) (hQ : ConjInv Q) :
    ConjInv (fun g => P g ∨ Q g) := by
  intro g c; simp only [hP g c, hQ g c]

theorem ConjInv.comp {H : Type*} [Group H] {Q : H → Prop} (hQ : ConjInv Q) (φ : G →* H) :
    ConjInv (fun g => Q (φ g)) := by
  intro g c; simp only [map_mul, map_inv, hQ (φ g) (φ c)]

theorem exists_prime_dvd_orderOf {g : G} (hg : orderOf g ≠ 1) :
    ∃ s, s.Prime ∧ s ∣ orderOf g :=
  Nat.exists_prime_and_dvd hg

section Fin

variable [Fintype G]

/-- If all partial augmentations of `a` on a union `P` of classes vanish, then so does the sum
of the coefficients of `a` on `P`. -/
theorem sum_pred_eq_zero (a : MonoidAlgebra ℤ G) (P : G → Prop) [DecidablePred P]
    (hP : ConjInv P)
    (h0 : ∀ x, P x → partialAug G x a = 0) : ∑ g, (if P g then a.coeff g else 0) = 0 := by
  rw [← Finset.sum_fiberwise Finset.univ (ConjClasses.mk) _]
  refine Finset.sum_eq_zero fun c _ => ?_
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
  have hiff : ∀ g, ConjClasses.mk g = ConjClasses.mk x ↔ IsConj g x := fun g =>
    ConjClasses.mk_eq_mk_iff_isConj
  by_cases hx : P x
  · have h1 : ∀ g ∈ Finset.univ.filter (fun g => ConjClasses.mk g = ConjClasses.mk x),
        (if P g then a.coeff g else 0) = a.coeff g := by
      intro g hg
      rw [Finset.mem_filter, hiff] at hg
      rw [if_pos ((isConj_pred hP hg.2).2 hx)]
    rw [Finset.sum_congr rfl h1, ← h0 x hx, partialAug]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hiff]
  · refine Finset.sum_eq_zero fun g hg => ?_
    rw [Finset.mem_filter, hiff] at hg
    rw [if_neg (fun h => hx ((isConj_pred hP hg.2).1 h))]

/-- Support of the partial augmentations of a torsion unit (Berman–Higman + MRSW). -/
theorem pa_support (a : MonoidAlgebra ℤ G) (ha : 0 < orderOf a) (haug : aug G a = 1)
    (hne : a ≠ 1) (x : G) (hx : partialAug G x a ≠ 0) :
    orderOf x ≠ 1 ∧ ∀ r, r.Prime → r ∣ orderOf x → r ∣ orderOf a := by
  refine ⟨?_, fun r hr hrx => by_contra fun hra => hx (mrsw a ha x hr hrx hra)⟩
  intro hx1
  rw [orderOf_eq_one_iff] at hx1
  subst hx1
  apply hx
  rw [partialAug, show (Finset.univ.filter fun g : G => IsConj g 1) = {1} from ?_,
    Finset.sum_singleton]
  · exact berman_higman a ha haug hne
  · ext g; simp

end Fin

/-- The vertex sets of `Π(V(ℤG))` and `Π(G)` coincide, for every finite group `G`. -/
theorem vertex_iff [Finite G] (p : ℕ) : IsVertex (V G) p ↔ IsVertex G p := by
  have := Fintype.ofFinite G
  constructor
  · rintro ⟨hp, u, hu⟩
    refine ⟨hp, ?_⟩
    haveI := Fact.mk hp
    apply exists_prime_orderOf_dvd_card'
    by_contra hpG
    have ha : orderOf (val u) = p := by rw [orderOf_val, hu]
    have haug := aug_val u
    have hne : val u ≠ 1 := by
      intro h; rw [h, orderOf_one] at ha; exact hp.one_lt.ne ha
    have hsum := sum_pred_eq_zero (val u) (fun _ => True) (fun _ _ => Iff.rfl) ?_
    · simp only [if_true] at hsum
      rw [aug_apply, hsum] at haug; exact zero_ne_one haug
    intro x _
    by_contra hx
    obtain ⟨hx1, hpr⟩ := pa_support (val u) (by rw [ha]; exact hp.pos) haug hne x hx
    obtain ⟨s, hs, hsx⟩ := exists_prime_dvd_orderOf hx1
    have h1 := hpr s hs hsx
    rw [ha] at h1
    rw [(Nat.prime_dvd_prime_iff_eq hs hp).1 h1] at hsx
    exact hpG (hsx.trans (orderOf_dvd_natCard x))
  · rintro ⟨hp, h⟩; exact ⟨hp, hasEltOfOrder_V h⟩

end Units

/-! ## Change of group -/

section Map

variable {E H : Type*} [Group E] [Group H] [Fintype E] (φ : E →* H)

theorem coeff_map (a : MonoidAlgebra ℤ E) (y : H) :
    (mapDomainRingHom ℤ φ a).coeff y = ∑ g, if φ g = y then a.coeff g else 0 := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x x' hx hx' =>
    rw [map_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hx', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [MonoidAlgebra.coeff_add, Finsupp.add_apply]
    split_ifs <;> simp
  | single g r =>
    rw [mapDomainRingHom_apply, mapDomain_single, MonoidAlgebra.coeff_single,
      Finsupp.single_apply]
    rw [Finset.sum_eq_single g (fun b _ hb => by simp [MonoidAlgebra.coeff_single,
      Finsupp.single_apply, Ne.symm hb]) (by simp)]
    simp [MonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem sum_pred_map [Fintype H] (a : MonoidAlgebra ℤ E) (Q : H → Prop)
    [DecidablePred Q] :
    (∑ y, if Q y then (mapDomainRingHom ℤ φ a).coeff y else 0) =
      ∑ g, if Q (φ g) then a.coeff g else 0 := by
  simp_rw [coeff_map]
  rw [show (∑ y, if Q y then ∑ g, (if φ g = y then a.coeff g else 0) else 0) =
      ∑ y, ∑ g, if φ g = y then (if Q y then a.coeff g else 0) else 0 from
    Finset.sum_congr rfl fun y _ => by split_ifs with hQ <;> simp [hQ]]
  rw [Finset.sum_comm]
  simp

theorem aug_map [Fintype H] (a : MonoidAlgebra ℤ E) :
    aug H (mapDomainRingHom ℤ φ a) = aug E a := by
  have := sum_pred_map φ a (fun _ => True)
  simpa [aug_apply] using this

end Map

/-! ## Proposition 2.2 -/

section Prop22

variable {G : Type*} [Group G]

/-- `g` is an `r`-element: every prime divisor of `o(g)` is `r` (this includes `g = 1`). -/
def IsRElt (r : ℕ) (g : G) : Prop := ∀ s, s.Prime → s ∣ orderOf g → s = r

/-- `g` is a nontrivial `r`-element: `o(g)` is a positive power of `r`. -/
def IsNTElt (r : ℕ) (g : G) : Prop := orderOf g ≠ 1 ∧ IsRElt r g

theorem conjInv_isRElt (r : ℕ) : ConjInv (IsRElt (G := G) r) :=
  conjInv_orderOf (fun n => ∀ s, s.Prime → s ∣ n → s = r)

theorem conjInv_isNTElt (r : ℕ) : ConjInv (IsNTElt (G := G) r) :=
  conjInv_orderOf (fun n => n ≠ 1 ∧ ∀ s, s.Prime → s ∣ n → s = r)

theorem isRElt_pow_self {q : ℕ} (hq : q.Prime) (g : G) : IsRElt q (g ^ q) ↔ IsRElt q g := by
  constructor
  · intro h s hs hsg
    have hdvd : orderOf g ∣ q * orderOf (g ^ q) :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_mul, pow_orderOf_eq_one])
    rcases (Nat.Prime.dvd_mul hs).1 (hsg.trans hdvd) with h1 | h1
    · exact (Nat.prime_dvd_prime_iff_eq hs hq).1 h1
    · exact h s hs h1
  · intro h s hs hsg
    exact h s hs (hsg.trans (orderOf_pow_dvd q))

theorem isNTElt_disjoint {p q : ℕ} (hpq : q ≠ p) {g : G} (hp : IsNTElt p g) :
    ¬ IsNTElt q g := by
  rintro ⟨-, hq⟩
  obtain ⟨s, hs, hsg⟩ := exists_prime_dvd_orderOf hp.1
  exact hpq ((hq s hs hsg).symm.trans (hp.2 s hs hsg))

theorem conj_eq_one_iff' (a b : G) : a⁻¹ * b * a = 1 ↔ b = 1 := by
  constructor
  · intro h
    calc b = a * (a⁻¹ * b * a) * a⁻¹ := by group
      _ = 1 := by rw [h]; group
  · rintro rfl; group

/-- **Kimmerle–Konovalov, Proposition 2.2.** Let `N ⊴ E` with `Π(V(ℤ(E/N))) = Π(E/N)`, let
`q ∈ π(E) \ π(N)` and `p ∈ π(E)` with `q ≠ p`. Then `V(ℤE)` has elements of order `p q`
if and only if `E` has. -/
theorem prop22 {E : Type*} [Group E] [Finite E] (N : Subgroup E) [N.Normal] (hPQ : PQ (E ⧸ N))
    {p q : ℕ} (hq : q.Prime) (hqE : q ∣ Nat.card E) (hqN : ¬ q ∣ Nat.card N) (hp : p.Prime)
    (hpE : p ∣ Nat.card E) (hpq : q ≠ p) :
    HasEltOfOrder (V E) (p * q) ↔ HasEltOfOrder E (p * q) := by
  have := Fintype.ofFinite E
  refine ⟨fun hV => ?_, hasEltOfOrder_V⟩
  by_contra hE
  obtain ⟨u, hu⟩ := hV
  have ha : orderOf (val u) = p * q := by rw [orderOf_val, hu]
  have ha0 : 0 < orderOf (val u) := by rw [ha]; exact Nat.mul_pos hp.pos hq.pos
  have haug := aug_val u
  have hne : val u ≠ 1 := by
    intro h; rw [h, orderOf_one] at ha
    exact (Nat.one_lt_mul_iff.2 ⟨hp.pos, hq.pos, Or.inl hp.one_lt⟩).ne ha
  let φ : E →* E ⧸ N := QuotientGroup.mk' N
  let ψ : MonoidAlgebra ℤ E →+* MonoidAlgebra ℤ (E ⧸ N) := mapDomainRingHom ℤ φ
  have := Fintype.ofFinite (E ⧸ N)
  have hφ1 : ∀ g, φ g = 1 ↔ g ∈ N := fun g => QuotientGroup.eq_one_iff g
  -- torsion units of prime order `r` in the kernel of `ψ` force `r ∣ |N|`
  have hK : ∀ c : MonoidAlgebra ℤ E, ∀ r : ℕ, r.Prime → orderOf c = r → aug E c = 1 →
      ψ c = 1 → r ∣ Nat.card N := by
    intro c r hr hc hcaug hψ
    by_contra hrN
    have hne' : c ≠ 1 := by
      rintro rfl; rw [orderOf_one] at hc; exact hr.one_lt.ne hc
    have h1 : ∑ g, (if φ g = 1 then c.coeff g else 0) = 1 := by
      rw [← sum_pred_map φ c (fun y => y = 1)]
      change (∑ y, if y = 1 then (ψ c).coeff y else 0) = 1
      rw [hψ]
      simp [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    have h0 := sum_pred_eq_zero c (fun g => φ g = 1) ?_ ?_
    · rw [h1] at h0; exact one_ne_zero h0
    · intro g x
      show φ (x⁻¹ * g * x) = 1 ↔ φ g = 1
      rw [map_mul, map_mul, map_inv, conj_eq_one_iff']
    · intro x hx
      by_contra hpa
      obtain ⟨hx1, hpr⟩ := pa_support c (by rw [hc]; exact hr.pos) hcaug hne' x hpa
      obtain ⟨s, hs, hsx⟩ := exists_prime_dvd_orderOf hx1
      have hsr : s = r := (Nat.prime_dvd_prime_iff_eq hs hr).1 (hc ▸ hpr s hs hsx)
      exact hrN (hsr ▸ hsx.trans (Subgroup.orderOf_dvd_natCard N ((hφ1 x).1 hx)))
  -- the image of `u` in `V(ℤ(E/N))`
  let ub : (MonoidAlgebra ℤ (E ⧸ N))ˣ := Units.map ψ.toMonoidHom (u : (MonoidAlgebra ℤ E)ˣ)
  have hub : (ub : MonoidAlgebra ℤ (E ⧸ N)) = ψ (val u) := rfl
  have hbaug : aug (E ⧸ N) (ψ (val u)) = 1 := by rw [aug_map]; exact haug
  have hubV : ub ∈ V (E ⧸ N) := mem_V.2 (by rw [hub]; exact hbaug)
  have hbord : orderOf (⟨ub, hubV⟩ : V (E ⧸ N)) = orderOf (ψ (val u)) := by
    rw [← orderOf_val]; rfl
  have hodvd : orderOf (ψ (val u)) ∣ p * q := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  have hnotp : ¬ orderOf (ψ (val u)) ∣ p := by
    intro hdvd
    have h1 : ψ (val u ^ p) = 1 := by rw [map_pow]; exact orderOf_dvd_iff_pow_eq_one.1 hdvd
    have h2 : orderOf (val u ^ p) = q := by
      rw [orderOf_pow_of_dvd hp.ne_zero (ha ▸ dvd_mul_right p q), ha,
        Nat.mul_div_cancel_left _ hp.pos]
    exact hqN (hK _ q hq h2 (by rw [map_pow, haug, one_pow]) h1)
  have hnotpq : orderOf (ψ (val u)) ≠ p * q := by
    intro hpq'
    have hadj : IsAdj (V (E ⧸ N)) p q :=
      ⟨hp, hq, hpq.symm, ⟨⟨ub, hubV⟩, by rw [hbord, hpq']⟩⟩
    obtain ⟨-, -, -, ⟨gbar, hgbar⟩⟩ := (hPQ.2 p q).1 hadj
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N gbar
    exact hE (hasEltOfOrder_of_dvd g (hgbar ▸ orderOf_map_dvd φ g))
  have ho : orderOf (ψ (val u)) = q := by
    obtain ⟨y, z, hy, hz, hyz⟩ := Nat.dvd_mul.1 hodvd
    rcases (Nat.dvd_prime hp).1 hy with rfl | rfl <;> rcases (Nat.dvd_prime hq).1 hz with rfl | rfl
    · exfalso; apply hnotp; rw [← hyz, one_mul]; exact one_dvd p
    · rw [← hyz, one_mul]
    · exfalso; apply hnotp; rw [← hyz, mul_one]
    · exact absurd hyz.symm hnotpq
  -- vanishing of partial augmentations of `u` off `E(p) ∪ E(q)`
  have hvan : ∀ x, ¬ (IsNTElt p x ∨ IsNTElt q x) → partialAug E x (val u) = 0 := by
    intro x hx
    by_contra hpa
    obtain ⟨hx1, hpr⟩ := pa_support (val u) ha0 haug hne x hpa
    have hprimes : ∀ s, s.Prime → s ∣ orderOf x → s = p ∨ s = q := by
      intro s hs hsx
      have h1 := hpr s hs hsx
      rw [ha] at h1
      rcases (Nat.Prime.dvd_mul hs).1 h1 with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hs hp).1 h)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hs hq).1 h)
    have hqx : q ∣ orderOf x := by
      by_contra hqx
      apply hx; left
      refine ⟨hx1, fun s hs hsx => ?_⟩
      rcases hprimes s hs hsx with h | h
      · exact h
      · exact absurd (h ▸ hsx) hqx
    have hpx : p ∣ orderOf x := by
      by_contra hpx
      apply hx; right
      refine ⟨hx1, fun s hs hsx => ?_⟩
      rcases hprimes s hs hsx with h | h
      · exact absurd (h ▸ hsx) hpx
      · exact h
    exact hE (hasEltOfOrder_of_dvd x
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hp hq).2 hpq.symm) hpx hqx))
  have hNTp := conjInv_isNTElt (G := E) p
  have hNTq := conjInv_isNTElt (G := E) q
  -- (S1) the augmentation splits over `E(p)`, `E(q)` and the rest
  have hrest : ∑ g, (if ¬ (IsNTElt p g ∨ IsNTElt q g) then (val u).coeff g else 0) = 0 :=
    sum_pred_eq_zero _ _ (hNTp.or hNTq).not hvan
  have hsplit : aug E (val u) = (∑ g, if IsNTElt p g then (val u).coeff g else 0) +
      (∑ g, if IsNTElt q g then (val u).coeff g else 0) +
      ∑ g, (if ¬ (IsNTElt p g ∨ IsNTElt q g) then (val u).coeff g else 0) := by
    rw [aug_apply, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases h1 : IsNTElt p g
    · have h2 := isNTElt_disjoint hpq h1
      simp [h1, h2]
    · by_cases h2 : IsNTElt q g <;> simp [h1, h2]
  -- (S3) the coefficient sum over `E(p)` vanishes, via the image in `V(ℤ(E/N))`
  have hbne : ψ (val u) ≠ 1 := by
    intro h; rw [h, orderOf_one] at ho; exact hq.one_lt.ne ho
  have hpb1 : ∀ g, IsNTElt p g → ¬ IsNTElt q (φ g) := by
    intro g hg hgq
    obtain ⟨s, hs, hsg⟩ := exists_prime_dvd_orderOf hgq.1
    exact hpq ((hgq.2 s hs hsg).symm.trans (hg.2 s hs (hsg.trans (orderOf_map_dvd φ g))))
  have hpb2 : ∀ g, IsNTElt q g → IsNTElt q (φ g) := by
    intro g hg
    refine ⟨fun h1 => ?_, fun s hs hsg => hg.2 s hs (hsg.trans (orderOf_map_dvd φ g))⟩
    have hgN : g ∈ N := (hφ1 g).1 (orderOf_eq_one_iff.1 h1)
    obtain ⟨s, hs, hsg⟩ := exists_prime_dvd_orderOf hg.1
    have := hg.2 s hs hsg
    subst this
    exact hqN (hsg.trans (Subgroup.orderOf_dvd_natCard N hgN))
  have himg : ∑ y, (if ¬ IsNTElt q y then (ψ (val u)).coeff y else 0) = 0 := by
    apply sum_pred_eq_zero _ _ (conjInv_isNTElt q).not
    intro y hy
    by_contra hpa
    obtain ⟨hy1, hpr⟩ := pa_support (ψ (val u)) (by rw [ho]; exact hq.pos) hbaug hbne y hpa
    exact hy ⟨hy1, fun s hs hsy => (Nat.prime_dvd_prime_iff_eq hs hq).1 (ho ▸ hpr s hs hsy)⟩
  have hpull := sum_pred_map φ (val u) (fun y => ¬ IsNTElt q y)
  have hrest2 : ∑ g, (if (¬ IsNTElt q (φ g)) ∧ ¬ (IsNTElt p g ∨ IsNTElt q g) then
      (val u).coeff g else 0) = 0 :=
    sum_pred_eq_zero _ _ (((conjInv_isNTElt q).not.comp φ).and (hNTp.or hNTq).not)
      (fun x hx => hvan x hx.2)
  have hA : ∑ g, (if IsNTElt p g then (val u).coeff g else 0) = 0 := by
    have hdec : ∑ g, (if ¬ IsNTElt q (φ g) then (val u).coeff g else 0) =
        (∑ g, if IsNTElt p g then (val u).coeff g else 0) +
        ∑ g, (if (¬ IsNTElt q (φ g)) ∧ ¬ (IsNTElt p g ∨ IsNTElt q g) then
          (val u).coeff g else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun g _ => ?_
      by_cases h1 : IsNTElt p g
      · simp [h1, hpb1 g h1, isNTElt_disjoint hpq h1]
      · by_cases h2 : IsNTElt q g
        · simp [h1, h2, hpb2 g h2]
        · simp [h1, h2]
    rw [← hpull, himg, hrest2, add_zero] at hdec
    exact hdec.symm
  have hB : ∑ g, (if IsNTElt q g then (val u).coeff g else 0) = 1 := by
    rw [haug, hA, hrest, zero_add, add_zero] at hsplit
    exact hsplit.symm
  -- (S4) the coefficient sum of `u ^ q` over the `q`-elements vanishes
  have hcord : orderOf (val u ^ q) = p := by
    rw [orderOf_pow_of_dvd hq.ne_zero (ha ▸ dvd_mul_left q p), ha, Nat.mul_div_cancel _ hq.pos]
  have hcaug : aug E (val u ^ q) = 1 := by rw [map_pow, haug, one_pow]
  have hcne : val u ^ q ≠ 1 := by
    intro h; rw [h, orderOf_one] at hcord; exact hp.one_lt.ne hcord
  have hc0 : ∑ g, (if IsRElt q g then (val u ^ q).coeff g else 0) = 0 := by
    apply sum_pred_eq_zero _ _ (conjInv_isRElt q)
    intro x hx
    by_contra hpa
    obtain ⟨hx1, hpr⟩ := pa_support _ (by rw [hcord]; exact hp.pos) hcaug hcne x hpa
    obtain ⟨s, hs, hsx⟩ := exists_prime_dvd_orderOf hx1
    have h1 := hx s hs hsx
    have h2 := (Nat.prime_dvd_prime_iff_eq hs hp).1 (hcord ▸ hpr s hs hsx)
    exact hpq (h1.symm.trans h2)
  -- (S5) the congruence modulo `q`
  haveI := Fact.mk hq
  have hcong := sum_pow_prime_modEq q (val u) (IsRElt q) (conjInv_isRElt q)
  rw [hc0, Int.cast_zero] at hcong
  have h1u := berman_higman (val u) ha0 haug hne
  have hR : ∑ g, (if IsRElt q g then (val u).coeff g else 0) = 1 := by
    have : ∀ g, (if IsRElt q g then (val u).coeff g else 0) =
        (if IsNTElt q g then (val u).coeff g else 0) + (if g = 1 then (val u).coeff g else 0) := by
      intro g
      by_cases hg : g = 1
      · subst hg
        have h1 : IsRElt q (1 : E) := fun s hs hsx => by
          rw [orderOf_one] at hsx
          exact absurd (Nat.le_of_dvd one_pos hsx) (by have := hs.two_le; omega)
        simp [h1, IsNTElt, h1u]
      · have : orderOf g ≠ 1 := mt orderOf_eq_one_iff.1 hg
        simp [IsNTElt, this, hg]
    rw [Finset.sum_congr rfl fun g _ => this g, Finset.sum_add_distrib, hB]
    simp [h1u]
  have hfin : (0 : ZMod q) = 1 := by
    rw [hcong]
    simp only [isRElt_pow_self hq]
    have := congrArg (fun z : ℤ => (z : ZMod q)) hR
    simpa [Int.cast_sum, apply_ite] using this
  exact zero_ne_one hfin

end Prop22

/-! ## Corollary 2.3 and the soluble case -/

section Soluble

universe u

/-- The prime graph `Π(H)` is a complete graph. -/
def PrimeGraphComplete (H : Type*) [Monoid H] : Prop :=
  ∀ p q, IsVertex H p → IsVertex H q → p ≠ q → HasEltOfOrder H (p * q)

theorem dvd_card_of_adj_V {G : Type*} [Group G] [Finite G] {p q : ℕ} (h : IsAdj (V G) p q) :
    p ∣ Nat.card G ∧ q ∣ Nat.card G := by
  obtain ⟨hp, hq, -, u, hu⟩ := h
  have hpq0 : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  have hv : ∀ r, r.Prime → r ∣ p * q → IsVertex (V G) r := by
    intro r hr hrd
    refine ⟨hr, u ^ (p * q / r), ?_⟩
    rw [orderOf_pow_of_dvd (Nat.div_pos (Nat.le_of_dvd hpq0 hrd) hr.pos).ne'
      (by rw [hu]; exact Nat.div_dvd_of_dvd hrd), hu, Nat.div_div_self hrd hpq0.ne']
  obtain ⟨-, x, hx⟩ := (vertex_iff p).1 (hv p hp (dvd_mul_right p q))
  obtain ⟨-, y, hy⟩ := (vertex_iff q).1 (hv q hq (dvd_mul_left q p))
  exact ⟨hx ▸ orderOf_dvd_natCard x, hy ▸ orderOf_dvd_natCard y⟩

/-- **Kimmerle–Konovalov, Corollary 2.3.** If `N ⊴ G`, `Π(N)` is complete and
`Π(V(ℤ(G/N))) = Π(G/N)`, then `Π(V(ℤG)) = Π(G)`. -/
theorem cor23 {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hN : PrimeGraphComplete N) (hQ : PQ (G ⧸ N)) : PQ G := by
  refine ⟨vertex_iff, fun p q => ⟨fun h => ?_, fun ⟨hp, hq, hpq, hG⟩ =>
    ⟨hp, hq, hpq, hasEltOfOrder_V hG⟩⟩⟩
  obtain ⟨hpG, hqG⟩ := dvd_card_of_adj_V h
  obtain ⟨hp, hq, hpq, hV⟩ := h
  refine ⟨hp, hq, hpq, ?_⟩
  by_cases hqN : q ∣ Nat.card N
  · by_cases hpN : p ∣ Nat.card N
    · haveI := Fact.mk hp
      haveI := Fact.mk hq
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) p hpN
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := N) q hqN
      obtain ⟨z, hz⟩ := hN p q ⟨hp, x, hx⟩ ⟨hq, y, hy⟩ hpq
      exact ⟨z, by rw [Subgroup.orderOf_coe, hz]⟩
    · have := (prop22 N hQ hp hpG hpN hq hqG hpq).1 (by rwa [mul_comm])
      rwa [mul_comm] at this
  · exact (prop22 N hQ hq hqG hqN hp hpG (Ne.symm hpq)).1 hV

theorem complete_of_comm {H : Type*} [Group H] (hc : ∀ a b : H, a * b = b * a) :
    PrimeGraphComplete H := by
  rintro p q ⟨hp, x, hx⟩ ⟨hq, y, hy⟩ hpq
  refine ⟨x * y, ?_⟩
  rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime (hc x y)
    (by rw [hx, hy]; exact (Nat.coprime_primes hp hq).2 hpq), hx, hy]

theorem exists_abelian_normal {G : Type*} [Group G] [Nontrivial G] [Group.IsSolvable G] :
    ∃ A : Subgroup G, A.Normal ∧ A ≠ ⊥ ∧ ∀ a b : A, a * b = b * a := by
  have hex : ∃ n, derivedSeries G n = ⊥ := (isSolvable_def G).1 inferInstance
  have hk : derivedSeries G (Nat.find hex) = ⊥ := Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, derivedSeries_zero] at hk
    exact top_ne_bot hk
  refine ⟨derivedSeries G (Nat.find hex - 1), derivedSeries_normal G _,
    Nat.find_min hex (by omega), ?_⟩
  intro a b
  have hmem := Subgroup.commutator_mem_commutator a.2 b.2
  rw [← derivedSeries_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0), hk] at hmem
  exact Subtype.ext ((commutatorElement_eq_one_iff_mul_comm).1 ((Subgroup.mem_bot).1 hmem))

theorem pq_of_solvable_aux (n : ℕ) : ∀ (G : Type u) [Group G] [Finite G] [Group.IsSolvable G],
    Nat.card G = n → PQ G := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ _ hn
  rcases subsingleton_or_nontrivial G with hG | hG
  · refine ⟨vertex_iff, fun p q => ⟨fun h => ?_, fun ⟨hp, hq, hpq, hG'⟩ =>
      ⟨hp, hq, hpq, hasEltOfOrder_V hG'⟩⟩⟩
    obtain ⟨hpG, -⟩ := dvd_card_of_adj_V h
    have h1 : Nat.card G = 1 := Nat.card_eq_one_iff_unique.2 ⟨hG, ⟨1⟩⟩
    rw [h1] at hpG
    exact absurd (Nat.le_of_dvd one_pos hpG) (by have := h.1.two_le; omega)
  · obtain ⟨A, hAn, hA, hAc⟩ := exists_abelian_normal (G := G)
    have hlt : Nat.card (G ⧸ A) < n := by
      rw [← hn, Subgroup.card_eq_card_quotient_mul_card_subgroup A]
      have h1 : 1 < Nat.card A := (Subgroup.one_lt_card_iff_ne_bot A).2 hA
      have h2 : 0 < Nat.card (G ⧸ A) := Nat.card_pos
      nlinarith
    haveI : Group.IsSolvable (G ⧸ A) := solvable_of_surjective (QuotientGroup.mk'_surjective A)
    exact cor23 A (complete_of_comm hAc) (ih _ hlt (G ⧸ A) rfl)

/-- The prime graph question has a positive answer for finite soluble groups. -/
theorem pq_of_solvable (G : Type u) [Group G] [Finite G] [Group.IsSolvable G] : PQ G :=
  pq_of_solvable_aux _ G rfl

end Soluble

/-! ## Corollary 2.6 -/

section Cor26

open CFSGOutside.Corpus.ComponentClassification.OuterAutomorphisms

theorem conj_injective_of_simple {S : Type*} [Group S] [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) : Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  have hc : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hS
      apply hab
      have : a ∈ Subgroup.center S := h ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.1 this b).symm
  rw [eq_bot_iff, ← hc]
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 : x * g * x⁻¹ = g := by
    have := DFunLike.congr_fun (MonoidHom.mem_ker.1 hx) g
    simpa [MulAut.conj_apply] using this
  calc g * x = x * g * x⁻¹ * x := by rw [h1]
    _ = x * g := by group

/-- **Prime graphs of integral group rings.** Let S be a finite nonabelian simple group, G a subgroup of Aut(S)
containing Inn(S), q a prime dividing |G| but not |S|, and p a prime dividing |S|. Then the group V(ℤG) of units of
augmentation 1 in the integral group ring ℤG has an element of order pq if and only if G has one.

Source: W. Kimmerle and A. Konovalov, On the Gruenberg–Kegel graph of integral group rings of finite groups,
Internat. J. Algebra Comput. 27 (2017), 619–631, Corollary 2.6. https://doi.org/10.1142/S0218196717500308

This version takes the corpus theorems it uses as instance arguments; the version in `unconditional/` supplies them
from the CFSG corpus. -/
theorem cor26 [CFSGOutside.Corpus.Schreier]
    (hCFSG : TauCeti.ClassificationStatement.{0}) {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a) (G : Subgroup (MulAut S))
    (hG : CFSGOutside.Corpus.ComponentClassification.OuterAutomorphisms.inner S ≤ G) {q : ℕ}
    (hq : q.Prime)
    (hqG : q ∣ Nat.card G) (hqS : ¬ q ∣ Nat.card S) {p : ℕ} (hp : p.Prime)
    (hpS : p ∣ Nat.card S) :
    IsAdj (V G) p q ↔ IsAdj G p q := by
  haveI : Finite (MulAut S) := Finite.of_injective (fun f : MulAut S => (f : S → S))
    (fun f g h => MulEquiv.ext (congrFun h))
  haveI : Group.IsSolvable (Outer S) :=
    CFSGOutside.Corpus.Schreier.schreierFor_inCatalog_holds S hS
      (TauCeti.classificationStatement_iff.1 hCFSG S)
  let f : G →* Outer S :=
    (QuotientGroup.mk'
      (CFSGOutside.Corpus.ComponentClassification.OuterAutomorphisms.inner S)).comp G.subtype
  haveI : Group.IsSolvable (G ⧸ f.ker) :=
    solvable_of_solvable_injective (QuotientGroup.kerLift_injective f)
  have hker : f.ker =
      (CFSGOutside.Corpus.ComponentClassification.OuterAutomorphisms.inner S).subgroupOf G := by
    ext x
    simp [f, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hcardN : Nat.card f.ker = Nat.card S := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hG).toEquiv]
    exact (Nat.card_congr (MonoidHom.ofInjective (conj_injective_of_simple hS)).toEquiv).symm
  have hpG : p ∣ Nat.card G :=
    (hcardN ▸ hpS : p ∣ Nat.card f.ker).trans (Subgroup.card_subgroup_dvd_card _)
  have hqN : ¬ q ∣ Nat.card f.ker := hcardN ▸ hqS
  have hpq : q ≠ p := fun h => hqS (h ▸ hpS)
  have key := prop22 f.ker (pq_of_solvable (G ⧸ f.ker)) hq hqG hqN hp hpG hpq
  exact ⟨fun ⟨_, _, h1, h2⟩ => ⟨hp, hq, h1, key.1 h2⟩, fun ⟨_, _, h1, h2⟩ =>
    ⟨hp, hq, h1, key.2 h2⟩⟩

/-- **Corollary 2.6, abstract form.** The same statement for a finite group `G` with a nonabelian
simple normal subgroup `S` whose centralizer is trivial (equivalently, `S ≤ G ≲ Aut(S)` via
conjugation). -/
theorem cor26_abstract [CFSGOutside.Corpus.Schreier]
    (hCFSG : TauCeti.ClassificationStatement.{0}) {G : Type} [Group G]
    [Finite G] (S : Subgroup G) [S.Normal] [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a)
    (hC : Subgroup.centralizer (S : Set G) = ⊥) {q : ℕ} (hq : q.Prime) (hqG : q ∣ Nat.card G)
    (hqS : ¬ q ∣ Nat.card S) {p : ℕ} (hp : p.Prime) (hpS : p ∣ Nat.card S) :
    IsAdj (V G) p q ↔ IsAdj G p q := by
  haveI : Group.IsSolvable (Outer S) :=
    CFSGOutside.Corpus.Schreier.schreierFor_inCatalog_holds S hS
      (TauCeti.classificationStatement_iff.1 hCFSG S)
  let f : G →* Outer S :=
    (QuotientGroup.mk'
      (CFSGOutside.Corpus.ComponentClassification.OuterAutomorphisms.inner S)).comp
      (MulAut.conjNormal (H := S))
  have hker : f.ker = S := by
    ext g
    simp only [f, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨s, hs⟩
      have hcen : (s : G)⁻¹ * g ∈ Subgroup.centralizer (S : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro n hn
        have := congrArg (fun φ : MulAut S => ((φ ⟨n, hn⟩ : S) : G)) hs
        simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
          Subgroup.coe_inv] at this
        calc n * ((s : G)⁻¹ * g) = (s : G)⁻¹ * ((s : G) * n * (s : G)⁻¹) * g := by group
          _ = (s : G)⁻¹ * (g * n * g⁻¹) * g := by rw [this]
          _ = (s : G)⁻¹ * g * n := by group
      rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hcen
      rw [← hcen]; exact s.2
    · intro hg
      refine ⟨⟨g, hg⟩, ?_⟩
      ext n
      simp [MulAut.conj_apply, MulAut.conjNormal_apply]
  haveI : Group.IsSolvable (G ⧸ f.ker) :=
    solvable_of_solvable_injective (QuotientGroup.kerLift_injective f)
  haveI : Group.IsSolvable (G ⧸ S) :=
    solvable_of_surjective (f := (QuotientGroup.quotientMulEquivOfEq hker).toMonoidHom)
      (QuotientGroup.quotientMulEquivOfEq hker).surjective
  have hpG : p ∣ Nat.card G := hpS.trans (Subgroup.card_subgroup_dvd_card _)
  have hpq : q ≠ p := fun h => hqS (h ▸ hpS)
  have key := prop22 S (pq_of_solvable (G ⧸ S)) hq hqG hqS hp hpG hpq
  exact ⟨fun ⟨_, _, h1, h2⟩ => ⟨hp, hq, h1, key.1 h2⟩, fun ⟨_, _, h1, h2⟩ =>
    ⟨hp, hq, h1, key.2 h2⟩⟩

end Cor26

end KimmerleKonovalov
