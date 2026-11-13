import CFSGOutside.Corpus.HallPaige.LieExcChevalley

/-!
# Double cosets of a maximal parabolic subgroup of a finite Weyl group

Let `W` be the Weyl group of a finite-type Cartan matrix `A`, acting on the root lattice
`I → ℤ` by `weylAction`. Let `λ` be a dominant vector (`⟨α_i^∨, λ⟩ ≥ 0` for all `i`) and
`J = {i | ⟨α_i^∨, λ⟩ = 0}`. If `O` is a set of vectors containing `λ`, closed under the simple
reflections, all of whose elements are `≤ λ` coordinatewise, then the stabilizer of `λ` is the
standard parabolic subgroup `W_J` (`CFSGOutside.HallPaige.Exc.mem_parabolic_of_weylAction_eq`); the proof
uses only the corpus fact that `w α_i ≤ 0` for a right descent `i` of `w`.

If moreover every element of `O` can be moved by `W_J` to `t λ` with `t` an involution, then
every double coset `W_J w W_J` contains an involution (`CFSGOutside.HallPaige.Exc.exists_involution`).

The finite checks are done by computation on lists (`CFSGOutside.HallPaige.Exc.reflL` etc.).
-/

namespace CFSGOutside.HallPaige.Exc

open CFSGOutside.Corpus.Exc

section Generic

variable {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)

theorem reflection_apply' (i : I) (v : I → ℤ) :
    reflection A i v = v - (∑ j, A i j * v j) • Pi.single i 1 := by
  simp [reflection, coroot]

section
variable [h0 : Corpus.Exc.Liftable]
include h0

theorem weylAction_simple (i : I) :
    weylAction hA ((coxeterMatrix hA).toCoxeterSystem.simple i) = reflection A i :=
  (coxeterMatrix hA).toCoxeterSystem.lift_apply_simple (Corpus.Exc.Liftable.isLiftable hA) i

theorem weylAction_simple_apply (i : I) (v : I → ℤ) :
    weylAction hA ((coxeterMatrix hA).toCoxeterSystem.simple i) v =
      v - (∑ j, A i j * v j) • Pi.single i 1 := by
  rw [weylAction_simple, reflection_apply']

theorem weylAction_mul_apply' (w w' : (coxeterMatrix hA).Group) (v : I → ℤ) :
    weylAction hA (w * w') v = weylAction hA w (weylAction hA w' v) := by
  rw [map_mul, Module.End.mul_apply]

/-- A set of vectors closed under the simple reflections is `W`-stable. -/
theorem weylAction_mem_of_closed {O : Set (I → ℤ)}
    (hO : ∀ μ ∈ O, ∀ i, μ - (∑ j, A i j * μ j) • Pi.single i 1 ∈ O)
    (w : (coxeterMatrix hA).Group) {μ : I → ℤ} (hμ : μ ∈ O) : weylAction hA w μ ∈ O := by
  induction w using (coxeterMatrix hA).toCoxeterSystem.simple_induction_left with
  | one => simpa using hμ
  | mul_simple_left w i ih =>
    rw [weylAction_mul_apply', weylAction_simple_apply]
    exact hO _ ih i

end

section
variable [h0 : Corpus.Exc.Liftable] [h1 : Corpus.Exc.Descent]
include h0 h1

/-- **The stabilizer of a dominant vector is the parabolic subgroup** of the simple reflections
fixing it, provided the orbit is bounded above by the vector (as it is for a dominant vector). -/
theorem mem_parabolic_of_weylAction_eq {O : Set (I → ℤ)} {lam : I → ℤ}
    (hO : ∀ w : (coxeterMatrix hA).Group, weylAction hA w lam ∈ O) (hle : ∀ μ ∈ O, μ ≤ lam)
    (hdom : ∀ i, 0 ≤ ∑ j, A i j * lam j) (w : (coxeterMatrix hA).Group)
    (hw : weylAction hA w lam = lam) :
    w ∈ (coxeterMatrix hA).toCoxeterSystem.parabolic {i | ∑ j, A i j * lam j = 0} := by
  set cs := (coxeterMatrix hA).toCoxeterSystem
  obtain ⟨n, hn⟩ : ∃ n, cs.length w = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    by_cases h1 : w = 1
    · rw [h1]; exact one_mem _
    obtain ⟨i, hi⟩ := cs.exists_rightDescent_of_ne_one h1
    have hlen : cs.length (w * cs.simple i) < n := hn ▸ hi
    by_cases hJ : ∑ j, A i j * lam j = 0
    · have hfix : weylAction hA (w * cs.simple i) lam = lam := by
        rw [weylAction_mul_apply', weylAction_simple_apply, hJ, zero_smul, sub_zero, hw]
      have := ih _ hlen (w * cs.simple i) hfix rfl
      have hs : cs.simple i ∈ cs.parabolic {i | ∑ j, A i j * lam j = 0} :=
        cs.simple_mem_parabolic hJ
      simpa using mul_mem this hs
    · exfalso
      have hpos : 0 < ∑ j, A i j * lam j := lt_of_le_of_ne (hdom i) (Ne.symm hJ)
      have hneg := Corpus.Exc.Descent.nonpos_of_isRightDescent hA hi
      have hne : weylAction hA w (Pi.single i 1) ≠ 0 := by
        intro h0
        have h' : weylAction hA w (Pi.single i 1) = weylAction hA w 0 := by rw [h0, map_zero]
        have := congrArg (weylAction hA w⁻¹) h'
        rw [← weylAction_mul_apply', ← weylAction_mul_apply', inv_mul_cancel, map_one] at this
        simpa using congrFun this i
      have heq : weylAction hA (w * cs.simple i) lam =
          lam - (∑ j, A i j * lam j) • weylAction hA w (Pi.single i 1) := by
        rw [weylAction_mul_apply', weylAction_simple_apply, map_sub, map_zsmul, hw]
      have hle' := hle _ (hO (w * cs.simple i))
      rw [heq] at hle'
      obtain ⟨k, hk⟩ : ∃ k, weylAction hA w (Pi.single i 1) k ≠ 0 := by
        by_contra h
        push Not at h
        exact hne (funext h)
      have h1 := hle' k
      have h2 := hneg k
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 h2
      have h3 : weylAction hA w (Pi.single i 1) k < 0 := lt_of_le_of_ne h2 hk
      nlinarith

/-- **Every double coset of the stabilizer contains an involution**, given an orbit certificate:
each `μ ∈ O` is moved by `W_J` to `t λ` for an involution `t`. -/
theorem exists_involution {O : Set (I → ℤ)} {lam : I → ℤ}
    (hO : ∀ w : (coxeterMatrix hA).Group, weylAction hA w lam ∈ O) (hle : ∀ μ ∈ O, μ ≤ lam)
    (hdom : ∀ i, 0 ≤ ∑ j, A i j * lam j)
    (hcert : ∀ μ ∈ O, ∃ x ∈ (coxeterMatrix hA).toCoxeterSystem.parabolic
        {i | ∑ j, A i j * lam j = 0}, ∃ t : (coxeterMatrix hA).Group, t * t = 1 ∧
          weylAction hA x μ = weylAction hA t lam)
    (w : (coxeterMatrix hA).Group) :
    ∃ x ∈ (coxeterMatrix hA).toCoxeterSystem.parabolic {i | ∑ j, A i j * lam j = 0},
      ∃ y ∈ (coxeterMatrix hA).toCoxeterSystem.parabolic {i | ∑ j, A i j * lam j = 0},
        (x * w * y) * (x * w * y) = 1 := by
  obtain ⟨x, hx, t, ht, hxt⟩ := hcert _ (hO w)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hstab : weylAction hA (t * x * w) lam = lam := by
    rw [weylAction_mul_apply', weylAction_mul_apply', hxt, ← weylAction_mul_apply', ht, map_one,
      Module.End.one_apply]
  have hy := mem_parabolic_of_weylAction_eq hA hO hle hdom _ hstab
  refine ⟨x, hx, (t * x * w)⁻¹, inv_mem hy, ?_⟩
  have : x * w * (t * x * w)⁻¹ = t := by
    rw [mul_inv_rev, mul_inv_rev, htinv]; group
  rw [this, ht]

end

section
variable [h0 : Corpus.Exc.Liftable]
include h0

/-- The simple reflections fixing `λ` generate a subgroup fixing `λ`. -/
theorem weylAction_eq_of_mem_parabolic {lam : I → ℤ} {w : (coxeterMatrix hA).Group}
    (hw : w ∈ (coxeterMatrix hA).toCoxeterSystem.parabolic {i | ∑ j, A i j * lam j = 0}) :
    weylAction hA w lam = lam := by
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    rw [weylAction_simple_apply, show ∑ j, A i j * lam j = 0 from hi, zero_smul, sub_zero]
  | one => simp
  | mul a b _ _ ha hb => rw [weylAction_mul_apply', hb, ha]
  | inv a _ ha =>
    conv_lhs => rw [← ha]
    rw [← weylAction_mul_apply', inv_mul_cancel, map_one, Module.End.one_apply]

/-- A simple reflection moving `λ` is not in the parabolic subgroup. -/
theorem simple_not_mem_parabolic {lam : I → ℤ} {r : I} (hr : ∑ j, A r j * lam j ≠ 0) :
    (coxeterMatrix hA).toCoxeterSystem.simple r ∉
      (coxeterMatrix hA).toCoxeterSystem.parabolic {i | ∑ j, A i j * lam j = 0} := by
  intro h
  have := weylAction_eq_of_mem_parabolic hA h
  rw [weylAction_simple_apply] at this
  have h' := congrFun this r
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
    sub_eq_self] at h'
  exact hr h'

end

end Generic

/-! ### Computation on lists -/

section Lists

/-- Dot product of two lists. -/
def dotL : List ℤ → List ℤ → ℤ
  | a :: as, b :: bs => a * b + dotL as bs
  | _, _ => 0

/-- The simple reflection `s_i` on a vector given as a list, for a Cartan matrix given by rows. -/
def reflL (rows : List (List ℤ)) (i : ℕ) (l : List ℤ) : List ℤ :=
  l.set i (l.getD i 0 - dotL (rows.getD i []) l)

/-- Apply the word `s_{i₁} ⋯ s_{iₘ}` (rightmost first). -/
def applyL (rows : List (List ℤ)) (ω : List ℕ) (l : List ℤ) : List ℤ :=
  ω.foldr (reflL rows) l

/-- The vector of `Fin r → ℤ` given by a list. -/
def vecL {r : ℕ} (l : List ℤ) : Fin r → ℤ := fun j => l.getD j 0

theorem dotL_eq_sum (a l : List ℤ) :
    dotL a l = ∑ j : Fin l.length, a.getD j 0 * l.getD j 0 := by
  induction l generalizing a with
  | nil => cases a <;> simp [dotL]
  | cons b l ih =>
    cases a with
    | nil =>
      simp only [dotL, List.getD_nil, zero_mul, Finset.sum_const_zero]
    | cons a as =>
      show _ = ∑ j : Fin (l.length + 1), _
      rw [Fin.sum_univ_succ]
      simp [dotL, ih as]

theorem vecL_reflL {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} (rows : List (List ℤ))
    (hrows : ∀ i j : Fin r, A i j = (rows.getD i []).getD j 0) (i : Fin r) {l : List ℤ}
    (hl : l.length = r) :
    vecL (reflL rows i l) = vecL l - (∑ j, A i j * vecL l j) • Pi.single i 1 := by
  subst hl
  funext k
  have hdot : dotL (rows.getD i []) l = ∑ j, A i j * vecL l j := by
    rw [dotL_eq_sum]; simp [vecL, hrows]
  simp only [vecL, reflL, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, hdot]
  by_cases hki : k = i
  · subst hki
    simp [List.getD_eq_getElem?_getD, List.getElem?_set_self, k.isLt]
  · have : (k : ℕ) ≠ i := fun h => hki (Fin.ext h)
    simp [hki, List.getD_eq_getElem?_getD, List.getElem?_set, Ne.symm this]

theorem length_reflL (rows : List (List ℤ)) (i : ℕ) (l : List ℤ) :
    (reflL rows i l).length = l.length := by
  simp [reflL]

theorem length_applyL (rows : List (List ℤ)) (ω : List ℕ) (l : List ℤ) :
    (applyL rows ω l).length = l.length := by
  induction ω with
  | nil => rfl
  | cons i ω ih => simp only [applyL, List.foldr_cons] at ih ⊢; rw [length_reflL, ih]

variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} (hA : TauCeti.IsFiniteType A)

section
variable [h0 : Corpus.Exc.Liftable]
include h0

theorem vecL_applyL (rows : List (List ℤ))
    (hrows : ∀ i j : Fin r, A i j = (rows.getD i []).getD j 0) (ω : List (Fin r)) {l : List ℤ}
    (hl : l.length = r) :
    vecL (applyL rows (ω.map (·.val)) l) =
      weylAction hA ((coxeterMatrix hA).toCoxeterSystem.wordProd ω) (vecL l) := by
  induction ω with
  | nil => simp [applyL, CoxeterSystem.wordProd]
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, weylAction_mul_apply', weylAction_simple_apply, ← ih]
    simp only [applyL, List.map_cons, List.foldr_cons]
    exact vecL_reflL rows hrows i ((length_applyL rows _ l).trans hl)

end

/-- The unit vector `e_j` of length `r` as a list. -/
def unitL (r j : ℕ) : List ℤ := (List.range r).map fun k => if k = j then 1 else 0

theorem length_unitL (r j : ℕ) : (unitL r j).length = r := by simp [unitL]

theorem vecL_unitL (j : Fin r) : vecL (unitL r j) = Pi.single j 1 := by
  funext k
  simp [vecL, unitL, Pi.single_apply, List.getD_eq_getElem?_getD, k.isLt, Fin.ext_iff]

theorem dotL_eq_sum' (a l : List ℤ) (hl : l.length = r) :
    dotL a l = ∑ j : Fin r, a.getD j 0 * l.getD j 0 := by
  subst hl
  exact dotL_eq_sum a l

section
variable [h0 : Corpus.Exc.Liftable] [h1 : Corpus.Exc.Descent]
include h0 h1

theorem wordProd_mul_self_of_lists (rows : List (List ℤ))
    (hrows : ∀ i j : Fin r, A i j = (rows.getD i []).getD j 0) (t : List (Fin r))
    (h : ∀ j : Fin r, applyL rows ((t ++ t).map (·.val)) (unitL r j) = unitL r j) :
    (coxeterMatrix hA).toCoxeterSystem.wordProd t *
      (coxeterMatrix hA).toCoxeterSystem.wordProd t = 1 := by
  apply Corpus.Exc.Descent.weylAction_injective hA
  rw [map_one, ← CoxeterSystem.wordProd_append]
  refine LinearMap.pi_ext fun j x => ?_
  have hj := vecL_applyL hA rows hrows (t ++ t) (length_unitL r j)
  rw [h j, vecL_unitL] at hj
  have hx : (Pi.single j x : Fin r → ℤ) = x • Pi.single j 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [hx, map_zsmul, ← hj, Module.End.one_apply]

end

theorem sum_mul_vecL_eq_dotL (rows : List (List ℤ))
    (hrows : ∀ i j : Fin r, A i j = (rows.getD i []).getD j 0) {lam : List ℤ}
    (hlam : lam.length = r) (i : Fin r) :
    ∑ j, A i j * vecL lam j = dotL (rows.getD i []) lam := by
  rw [dotL_eq_sum' _ _ hlam]
  simp [vecL, hrows]

section
variable [h0 : Corpus.Exc.Liftable] [h1 : Corpus.Exc.Descent]
include h0 h1

/-- **The list certificate for the double cosets of `W_J`.** -/
theorem cover_of_lists (rows : List (List ℤ))
    (hrows' : ∀ p : Fin r × Fin r, A p.1 p.2 = (rows.getD p.1 []).getD p.2 0) (lam : List ℤ)
    (hlam : lam.length = r) (T : List (List ℤ × List (Fin r) × ℕ)) (tw : List (List (Fin r)))
    (hlen : ∀ p ∈ T, p.1.length = r) (hlamT : lam ∈ T.map (·.1))
    (hcl : ∀ p ∈ T, ∀ i : Fin r, reflL rows i p.1 ∈ T.map (·.1))
    (hle : ∀ p ∈ T, ∀ j : Fin r, p.1.getD j 0 ≤ lam.getD j 0)
    (hdom : ∀ i : Fin r, 0 ≤ dotL (rows.getD i []) lam)
    (hinv : ∀ t ∈ tw, ∀ j : Fin r, applyL rows ((t ++ t).map (·.val)) (unitL r j) = unitL r j)
    (hcert : ∀ p ∈ T, (∀ i ∈ p.2.1, dotL (rows.getD i []) lam = 0) ∧ p.2.2 < tw.length ∧
      applyL rows (p.2.1.map (·.val)) p.1 = applyL rows ((tw.getD p.2.2 []).map (·.val)) lam)
    (w : (coxeterMatrix hA).Group) :
    ∃ x ∈ (coxeterMatrix hA).toCoxeterSystem.parabolic {i | ∑ j, A i j * vecL lam j = 0},
      ∃ y ∈ (coxeterMatrix hA).toCoxeterSystem.parabolic {i | ∑ j, A i j * vecL lam j = 0},
        (x * w * y) * (x * w * y) = 1 := by
  have hrows : ∀ i j : Fin r, A i j = (rows.getD i []).getD j 0 := fun i j => hrows' (i, j)
  have hdotlam : ∀ i : Fin r, dotL (rows.getD i []) lam = ∑ j, A i j * vecL lam j :=
    fun i => (sum_mul_vecL_eq_dotL rows hrows hlam i).symm
  let O : Set (Fin r → ℤ) := {μ | ∃ p ∈ T, μ = vecL p.1}
  have hO : ∀ w : (coxeterMatrix hA).Group, weylAction hA w (vecL lam) ∈ O := by
    intro w
    refine weylAction_mem_of_closed hA ?_ w ?_
    · rintro _ ⟨p, hp, rfl⟩ i
      obtain ⟨q, hq, hqe⟩ := List.mem_map.1 (hcl p hp i)
      exact ⟨q, hq, by rw [hqe, vecL_reflL rows hrows i (hlen p hp)]⟩
    · obtain ⟨q, hq, hqe⟩ := List.mem_map.1 hlamT
      exact ⟨q, hq, by rw [hqe]⟩
  refine exists_involution hA hO ?_ (fun i => by rw [← hdotlam]; exact hdom i) ?_ w
  · rintro _ ⟨p, hp, rfl⟩ j
    exact hle p hp j
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨hJ, hk, happ⟩ := hcert p hp
    refine ⟨(coxeterMatrix hA).toCoxeterSystem.wordProd p.2.1,
      CoxeterSystem.wordProd_mem_parabolic _ fun i hi => ?_,
      (coxeterMatrix hA).toCoxeterSystem.wordProd (tw.getD p.2.2 []), ?_, ?_⟩
    · show ∑ j, A i j * vecL lam j = 0
      rw [← hdotlam]; exact hJ i hi
    · refine wordProd_mul_self_of_lists hA rows hrows _ (hinv _ ?_)
      rw [List.getD_eq_getElem _ _ hk]
      exact List.getElem_mem hk
    · rw [← vecL_applyL hA rows hrows _ (hlen p hp), ← vecL_applyL hA rows hrows _ hlam, happ]

end

end Lists

end CFSGOutside.HallPaige.Exc
