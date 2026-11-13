import Mathlib

/-!
# Fixed points of a free coordinate permutation on a product of perfect groups are perfect

Used for Guralnick–Shumyatsky, Lemma 3.7: if `b` permutes the simple direct factors of `G`
without fixed factors and `b^q = 1`, then `C_G(b)` is perfect.
-/

namespace CFSGOutside.GuralnickShumyatsky


theorem perfect_of_inj_aux {G K : Type*} [Group G] [Group K] (ρ : G →* K) (Δ : Subgroup G)
    (hsurj : ∀ k, ∃ d ∈ Δ, ρ d = k) (hinj : ∀ d ∈ Δ, ρ d = 1 → d = 1)
    (hK : commutator K = ⊤) : Δ ≤ ⁅Δ, Δ⁆ := by
  intro d hd
  have hmap : Subgroup.map ρ Δ = ⊤ := by
    rw [eq_top_iff]
    intro k _
    obtain ⟨e, he, rfl⟩ := hsurj k
    exact ⟨e, he, rfl⟩
  have h1 : ρ d ∈ Subgroup.map ρ ⁅Δ, Δ⁆ := by
    rw [Subgroup.map_commutator, hmap]
    have := hK
    rw [commutator_def] at this
    rw [this]; trivial
  obtain ⟨c, hc, hcd⟩ := h1
  have hcΔ : c ∈ Δ := by
    have : ⁅Δ, Δ⁆ ≤ Δ := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact Δ.mul_mem (Δ.mul_mem (Δ.mul_mem ha hb) (Δ.inv_mem ha)) (Δ.inv_mem hb)
    exact this hc
  have : c⁻¹ * d = 1 := hinj _ (Δ.mul_mem (Δ.inv_mem hcΔ) hd) (by rw [map_mul, map_inv, hcd]; simp)
  have hd' : d = c := by
    have := congrArg (c * ·) this
    simpa using this
  rw [hd']; exact hc

/-- Let `τ` be an endomorphism of `∏ᵢ Hᵢ` moving coordinate `i` to coordinate `σ i` via `φ i`, with
`σ` fixed-point free and `τ^q = id` (`q` prime). If all `Hᵢ` are perfect, so is the group of
`τ`-fixed points. -/
theorem fixed_le_commutator {ι : Type*} [Fintype ι] [DecidableEq ι] {H : ι → Type*}
    [∀ i, Group (H i)] (hperf : ∀ i, commutator (H i) = ⊤)
    (σ : Equiv.Perm ι) (φ : ∀ i, H i →* H (σ i)) (τ : (∀ i, H i) →* (∀ i, H i))
    (hτ : ∀ (y : ∀ i, H i) (i : ι), τ y (σ i) = φ i (y i))
    {q : ℕ} (hq : q.Prime) (hσ : ∀ i, σ i ≠ i) (hτq : ∀ y, τ^[q] y = y) :
    MonoidHom.eqLocus τ (MonoidHom.id _) ≤
      ⁅MonoidHom.eqLocus τ (MonoidHom.id _), MonoidHom.eqLocus τ (MonoidHom.id _)⁆ := by
  classical
  set F := MonoidHom.eqLocus τ (MonoidHom.id (∀ i, H i)) with hF
  have hmemF : ∀ x, x ∈ F ↔ τ x = x := fun x => Iff.rfl
  have hiter : ∀ (k : ℕ) (x : ∀ i, H i) (i : ι), τ^[k+1] x (σ i) = φ i (τ^[k] x i) := by
    intro k x i
    rw [Function.iterate_succ_apply']
    exact hτ _ _
  have hsupp : ∀ (j : ι) (z : H j) (k : ℕ) (m : ι), m ≠ σ^[k] j →
      τ^[k] (Pi.mulSingle j z : ∀ i, H i) m = 1 := by
    intro j z k
    induction k with
    | zero =>
      intro m hm
      simp only [Function.iterate_zero, id] at hm ⊢
      exact Pi.mulSingle_eq_of_ne hm z
    | succ k ih =>
      intro m hm
      obtain ⟨i, rfl⟩ := σ.surjective m
      have hi : i ≠ σ^[k] j := by
        intro h
        apply hm
        rw [Function.iterate_succ_apply', h]
      rw [hiter k _ i, ih i hi, map_one]
  have hinv : ∀ (j : ι) (x x' : ∀ i, H i), x j = x' j → ∀ (k : ℕ) (m : ι), σ^[k] j = m →
      τ^[k] x m = τ^[k] x' m := by
    intro j x x' h k
    induction k with
    | zero =>
      intro m hm
      simp only [Function.iterate_zero, id] at hm ⊢
      subst hm
      exact h
    | succ k ih =>
      intro m hm
      rw [Function.iterate_succ_apply'] at hm
      subst hm
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hτ, hτ, ih _ rfl]
  have horb : ∀ (j : ι) (z0 : H j), z0 ≠ 1 →
      σ^[q] j = j ∧ ∀ k, 0 < k → k < q → σ^[k] j ≠ j := by
    intro j z0 hz0
    have h1 : σ^[q] j = j := by
      by_contra h
      have h1 := hsupp j z0 q j (Ne.symm h)
      rw [hτq] at h1
      simp at h1
      exact hz0 h1
    refine ⟨h1, ?_⟩
    intro k hk0 hkq h
    have hp1 : Function.IsPeriodicPt σ k j := h
    have hp2 : Function.IsPeriodicPt σ q j := h1
    have h3 := hp2.gcd hp1
    have hcop : Nat.Coprime q k := (Nat.Prime.coprime_iff_not_dvd hq).2
      (Nat.not_dvd_of_pos_of_lt hk0 hkq)
    rw [hcop.gcd_eq_one] at h3
    exact hσ j h3
  have hcomm : ∀ (x x' : ∀ i, H i), (∀ m, x m = 1 ∨ x' m = 1) → Commute x x' := by
    intro x x' h
    show x * x' = x' * x
    funext m
    rcases h m with h | h <;> simp [h]
  have hlist : ∀ (m : ι) (L : List (∀ i, H i)), (∀ a ∈ L, a m = 1) → L.prod m = 1 := by
    intro m L h
    induction L with
    | nil => rfl
    | cons a L ih =>
      simp only [List.prod_cons, Pi.mul_apply]
      rw [h a (by simp), ih (fun b hb => h b (by simp [hb])), one_mul]
  have hnorm : ∀ (j : ι) (z : H j), z ≠ 1 → ∃ x : (∀ i, H i), τ x = x ∧ x j = z ∧
      ∀ m, (¬∃ k, σ^[k] j = m) → x m = 1 := by
    intro j z hz
    obtain ⟨hq1, hq2⟩ := horb j z hz
    obtain ⟨r, hr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by have := hq.pos; omega⟩
    set u : ∀ i, H i := Pi.mulSingle j z with hu
    set R : ∀ i, H i := ((List.range r).map (fun k => τ^[k+1] u)).prod with hR
    have e1 : ((List.range (r+1)).map (fun k => τ^[k] u)).prod = u * R := by
      rw [List.range_succ_eq_map]
      simp [hR, Function.comp_def]
    have e2 : τ (((List.range (r+1)).map (fun k => τ^[k] u)).prod) = R * u := by
      rw [map_list_prod, List.map_map, List.range_succ]
      have : τ^[r+1] u = u := by rw [← hr]; exact hτq u
      simp only [List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
        List.prod_nil, mul_one, Function.comp_def, hR]
      rw [← Function.iterate_succ_apply' τ, this]
      simp only [← Function.iterate_succ_apply' τ]
    have hcu : Commute u R := by
      apply Commute.list_prod_right
      intro a ha
      simp only [List.mem_map, List.mem_range] at ha
      obtain ⟨k, hk, rfl⟩ := ha
      apply hcomm
      intro m
      by_cases hm : m = j
      · right
        subst hm
        exact hsupp m z (k+1) m (Ne.symm (hq2 (k+1) (by omega) (by omega)))
      · left
        exact Pi.mulSingle_eq_of_ne hm z
    refine ⟨((List.range (r+1)).map (fun k => τ^[k] u)).prod, ?_, ?_, ?_⟩
    · rw [e2, e1]; exact (hcu.eq).symm
    · rw [e1, Pi.mul_apply]
      have : R j = 1 := by
        apply hlist
        intro a ha
        simp only [List.mem_map, List.mem_range] at ha
        obtain ⟨k, hk, rfl⟩ := ha
        exact hsupp j z (k+1) j (Ne.symm (hq2 (k+1) (by omega) (by omega)))
      rw [this, mul_one]
      simp [hu]
    · intro m hm
      apply hlist
      intro a ha
      simp only [List.mem_map, List.mem_range] at ha
      obtain ⟨k, hk, rfl⟩ := ha
      exact hsupp j z k m (fun h => hm ⟨k, h.symm⟩)
  have hperfj : ∀ (j : ι) (y : ∀ i, H i), y ∈ F → y j ≠ 1 → ∃ w : (∀ i, H i),
      w ∈ ⁅F, F⁆ ∧ τ w = w ∧ w j = y j ∧ ∀ m, w m = 1 ∨ w m = y m := by
    intro j y hy hyj
    let Δ : Subgroup (∀ i, H i) :=
      { carrier := {x | τ x = x ∧ ∀ m, (¬∃ k, σ^[k] j = m) → x m = 1}
        mul_mem' := by
          rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
          exact ⟨by rw [map_mul, ha1, hb1], fun m hm => by simp [ha2 m hm, hb2 m hm]⟩
        one_mem' := ⟨map_one τ, fun m _ => rfl⟩
        inv_mem' := by
          rintro a ⟨ha1, ha2⟩
          exact ⟨by rw [map_inv, ha1], fun m hm => by simp [ha2 m hm]⟩ }
    have hΔF : Δ ≤ F := fun x hx => hx.1
    have hΔ : Δ ≤ ⁅Δ, Δ⁆ := by
      apply perfect_of_inj_aux (Pi.evalMonoidHom H j) Δ
      · intro k
        by_cases hk : k = 1
        · exact ⟨1, Δ.one_mem, by simp [hk]⟩
        · obtain ⟨x, hx1, hx2, hx3⟩ := hnorm j k hk
          exact ⟨x, ⟨hx1, hx3⟩, hx2⟩
      · rintro d ⟨hd1, hd2⟩ hd
        funext m
        by_cases hm : ∃ k, σ^[k] j = m
        · obtain ⟨k, hk⟩ := hm
          have := hinv j d 1 (by simpa using hd) k m hk
          rw [Function.iterate_fixed hd1, Function.iterate_fixed (map_one τ)] at this
          exact this
        · exact hd2 m hm
      · exact hperf j
    obtain ⟨w, hw, hwj⟩ : ∃ w ∈ Δ, w j = y j := by
      obtain ⟨x, hx1, hx2, hx3⟩ := hnorm j (y j) hyj
      exact ⟨x, ⟨hx1, hx3⟩, hx2⟩
    refine ⟨w, (Subgroup.commutator_mono hΔF hΔF) (hΔ hw), hw.1, hwj, fun m => ?_⟩
    by_cases hm : ∃ k, σ^[k] j = m
    · obtain ⟨k, hk⟩ := hm
      right
      have := hinv j w y hwj k m hk
      rwa [Function.iterate_fixed hw.1, Function.iterate_fixed ((hmemF y).1 hy)] at this
    · left; exact hw.2 m hm
  suffices ∀ n, ∀ y ∈ F, (Finset.univ.filter fun i => y i ≠ 1).card ≤ n → y ∈ ⁅F, F⁆ by
    intro y hy; exact this _ y hy le_rfl
  intro n
  induction n with
  | zero =>
    intro y hy hc
    have : y = 1 := by
      funext i
      by_contra h
      have : i ∈ Finset.univ.filter fun i => y i ≠ 1 := by simpa using h
      have := Finset.card_pos.2 ⟨i, this⟩
      omega
    rw [this]; exact Subgroup.one_mem _
  | succ n ih =>
    intro y hy hc
    by_cases h1 : ∃ j, y j ≠ 1
    · obtain ⟨j, hj⟩ := h1
      obtain ⟨w, hw, hwτ, hwj, hwm⟩ := hperfj j y hy hj
      have hwF : w ∈ F := hwτ
      have hy' : y * w⁻¹ ∈ F := F.mul_mem hy (F.inv_mem hwF)
      have hsub : (Finset.univ.filter fun i => (y * w⁻¹) i ≠ 1) ⊆
          (Finset.univ.filter fun i => y i ≠ 1).erase j := by
        intro m hm
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.mul_apply, Pi.inv_apply] at hm
        simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, ?_⟩
        · rintro rfl
          apply hm
          rw [hwj, mul_inv_cancel]
        · intro h
          apply hm
          rcases hwm m with h' | h' <;> simp [h, h']
      have hjmem : j ∈ Finset.univ.filter fun i => y i ≠ 1 := by simpa using hj
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hjmem] at hcard
      have := ih (y * w⁻¹) hy' (by omega)
      have hyw : y = (y * w⁻¹) * w := by simp
      rw [hyw]
      exact Subgroup.mul_mem _ this hw
    · push Not at h1
      have : y = 1 := funext h1
      rw [this]; exact Subgroup.one_mem _

end CFSGOutside.GuralnickShumyatsky
