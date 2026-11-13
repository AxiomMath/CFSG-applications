import CFSGOutside.GuralnickShumyatsky.Step

/-!
# Counting tools for Theorem 3.6: cyclic subgroups of `A` and a product bound
-/

namespace CFSGOutside.GuralnickShumyatsky

open Subgroup

variable {X : Type*} [Group X]

/-- The set of nontrivial cyclic subgroups of `A`. -/
noncomputable def cycSubs [Finite X] (A : Subgroup X) : Finset (Subgroup X) :=
  ((Set.toFinite ((A : Set X) \ {1})).image (fun a => zpowers a)).toFinset

theorem mem_cycSubs [Finite X] {A B : Subgroup X} :
    B ∈ cycSubs A ↔ ∃ a ∈ A, a ≠ 1 ∧ zpowers a = B := by
  unfold cycSubs
  simp only [Set.Finite.mem_toFinset, Set.mem_image, Set.mem_diff, SetLike.mem_coe,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, ⟨h1, h2⟩, h3⟩; exact ⟨a, h1, h2, h3⟩
  · rintro ⟨a, h1, h2, h3⟩; exact ⟨a, ⟨h1, h2⟩, h3⟩

/-- An elementary abelian group of order `q³` has `q² + q + 1` nontrivial cyclic subgroups. -/
theorem card_cycSubs [Finite X] {q : ℕ} {G A : Subgroup X} (hA : CopAct q G A)
    (hA3 : Nat.card A = q ^ 3) : (cycSubs A).card = q ^ 2 + q + 1 := by
  classical
  have hq := hA.prime
  haveI : Fact q.Prime := ⟨hq⟩
  have hord : ∀ a ∈ A, a ≠ 1 → orderOf a = q := fun a ha h1 =>
    orderOf_eq_prime (hA.exp a ha) h1
  set Sf := (Set.toFinite ((A : Set X) \ {1})).toFinset with hSf
  have hSfc : Sf.card = q ^ 3 - 1 := by
    have h1 : (Sf.card) = ((A : Set X) \ {1}).ncard :=
      (Set.ncard_eq_toFinset_card _ (Set.toFinite _)).symm
    rw [h1, Set.ncard_diff_singleton_of_mem (by exact A.one_mem), ← hA3]
    rfl
  have hfib : ∀ B ∈ cycSubs A, (Sf.filter (fun b => zpowers b = B)).card = q - 1 := by
    intro B hB
    obtain ⟨a, ha, ha1, rfl⟩ := mem_cycSubs.1 hB
    have hset : ((Sf.filter (fun b => zpowers b = zpowers a) : Finset X) : Set X)
        = (zpowers a : Set X) \ {1} := by
      ext b
      simp only [Finset.coe_filter, hSf, Set.Finite.mem_toFinset, Set.mem_diff, SetLike.mem_coe,
        Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨⟨_, hb1⟩, hb⟩
        exact ⟨hb ▸ mem_zpowers b, hb1⟩
      · rintro ⟨hb, hb1⟩
        have hbA : b ∈ A := by
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
          exact A.zpow_mem ha n
        refine ⟨⟨hbA, hb1⟩, ?_⟩
        apply Subgroup.eq_of_le_of_card_ge
        · rw [zpowers_le]; exact hb
        · rw [Nat.card_zpowers, Nat.card_zpowers, hord a ha ha1, hord b hbA hb1]
    rw [← Set.ncard_coe_finset, hset, Set.ncard_diff_singleton_of_mem (one_mem _)]
    have : Nat.card (zpowers a) = q := by rw [Nat.card_zpowers, hord a ha ha1]
    rw [← this]
    rw [← Nat.card_coe_set_eq]; rfl
  have hsum : Sf.card = (cycSubs A).card * (q - 1) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun b => zpowers b) (t := cycSubs A)]
    · rw [Finset.sum_congr rfl hfib]; simp
    · intro b hb
      simp only [hSf, Set.Finite.mem_toFinset, Set.mem_diff, SetLike.mem_coe,
        Set.mem_singleton_iff] at hb
      exact mem_cycSubs.2 ⟨b, hb.1, hb.2, rfl⟩
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by have := hq.pos; omega⟩
  have hr : 0 < r := by have := hq.two_le; omega
  rw [hSfc] at hsum
  simp only [Nat.add_sub_cancel] at hsum
  have h3 : (r + 1) ^ 3 - 1 = (r ^ 2 + 3 * r + 3) * r := by
    have : (r + 1) ^ 3 = (r ^ 2 + 3 * r + 3) * r + 1 := by ring
    omega
  rw [h3] at hsum
  have := Nat.eq_of_mul_eq_mul_right hr hsum
  rw [← this]; ring

theorem cen_eq_cenS (H : Subgroup X) (a : X) : cen H a = cenS H (zpowers a) := by
  unfold cen cenS
  rw [zpowers_eq_closure, centralizer_closure]

/-- The generators of `gens` only depend on the cyclic subgroup `⟨a⟩`. -/
theorem gens_eq_iSup_cycSubs [Finite X] (P G A : Subgroup X) :
    gens P G A = ⨆ B ∈ cycSubs A, P ⊓ ⁅cenS G B, cenS G B⁆ := by
  apply le_antisymm
  · unfold gens
    refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
    refine le_iSup_of_le (zpowers a) (le_iSup_of_le (mem_cycSubs.2 ⟨a, ha, ha1, rfl⟩) ?_)
    rw [cen_eq_cenS]
  · refine iSup_le fun B => iSup_le fun hB => ?_
    obtain ⟨a, ha, ha1, rfl⟩ := mem_cycSubs.1 hB
    refine le_iSup_of_le a (le_iSup_of_le ha (le_iSup_of_le ha1 ?_))
    rw [cen_eq_cenS]

theorem iSup_eq_iSup_cycSubs [Finite X] (N G A : Subgroup X) :
    (⨆ (a : X) (_ : a ∈ A) (_ : a ≠ 1), ⁅cen N a, cen G a⁆) =
      ⨆ B ∈ cycSubs A, ⁅cenS N B, cenS G B⁆ := by
  apply le_antisymm
  · refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
    refine le_iSup_of_le (zpowers a) (le_iSup_of_le (mem_cycSubs.2 ⟨a, ha, ha1, rfl⟩) ?_)
    rw [cen_eq_cenS, cen_eq_cenS]
  · refine iSup_le fun B => iSup_le fun hB => ?_
    obtain ⟨a, ha, ha1, rfl⟩ := mem_cycSubs.1 hB
    refine le_iSup_of_le a (le_iSup_of_le ha (le_iSup_of_le ha1 ?_))
    rw [cen_eq_cenS, cen_eq_cenS]

/-- Product formula for subgroups when `F` normalizes `M`. -/
theorem card_sup_mul_card_inf [Finite X] {M F : Subgroup X} (hF : F ≤ normalizer (M : Set X)) :
    Nat.card (M ⊔ F : Subgroup X) * Nat.card (M ⊓ F : Subgroup X) =
      Nat.card M * Nat.card F := by
  have e : M.relIndex F = M.relIndex (F ⊔ M) := by
    haveI := Subgroup.normal_subgroupOf_of_le_normalizer hF
    haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hF
    exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient F M hF).toEquiv
  have h1 := Subgroup.relIndex_mul_card M F
  have h2 := Subgroup.relIndex_mul_card M (F ⊔ M)
  rw [inf_eq_left.mpr le_sup_right] at h2
  rw [sup_comm, ← h2, ← h1, e]
  ring

/-- If `L` is generated modulo a normal subgroup `W` by subgroups `F i` that commute modulo `W`,
then `|L : W| ≤ ∏ |F i : F i ∩ W|`. -/
theorem card_mul_prod_le [Finite X] {ι : Type*} (s : Finset ι) (F : ι → Subgroup X)
    {L W : Subgroup X} (hWL : W ≤ L) (hWn : L ≤ normalizer (W : Set X))
    (hFL : ∀ i ∈ s, F i ≤ L) (hL : L ≤ W ⊔ ⨆ i ∈ s, F i)
    (hcomm : ∀ i ∈ s, ∀ j ∈ s, ⁅F i, F j⁆ ≤ W) :
    Nat.card L * ∏ i ∈ s, Nat.card (F i ⊓ W : Subgroup X) ≤
      Nat.card W * ∏ i ∈ s, Nat.card (F i) := by
  classical
  have key : ∀ t : Finset ι, t ⊆ s →
      Nat.card (W ⊔ ⨆ i ∈ t, F i : Subgroup X) * ∏ i ∈ t, Nat.card (F i ⊓ W : Subgroup X) ≤
        Nat.card W * ∏ i ∈ t, Nat.card (F i) := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro _; simp
    | insert j t hj ih =>
      intro hts
      have htj : j ∈ s := hts (Finset.mem_insert_self _ _)
      have hts' : t ⊆ s := fun x hx => hts (Finset.mem_insert_of_mem hx)
      have ih := ih hts'
      set M : Subgroup X := W ⊔ ⨆ i ∈ t, F i with hM
      have hconj : ∀ f ∈ F j, ∀ x ∈ M, f * x * f⁻¹ ∈ M := by
        intro f hf
        have hfW : f ∈ normalizer (W : Set X) := hWn (hFL j htj hf)
        have : M ≤ M.comap (MulAut.conj f).toMonoidHom := by
          refine sup_le ?_ (iSup₂_le fun i hi => ?_)
          · intro x hx
            have := (mem_normalizer_iff.1 hfW x).1 hx
            show f * x * f⁻¹ ∈ M
            exact (le_sup_left : W ≤ M) this
          · intro x hx
            have hc : (f * x * f⁻¹ * x⁻¹) ∈ W := hcomm j htj i (hts' hi) (Subgroup.commutator_mem_commutator hf hx)
            have : f * x * f⁻¹ = (f * x * f⁻¹ * x⁻¹) * x := by simp [mul_assoc]
            show f * x * f⁻¹ ∈ M
            rw [this]
            exact M.mul_mem ((le_sup_left : W ≤ M) hc)
              ((le_iSup₂ (f := fun i (_ : i ∈ t) => F i) i hi).trans (le_sup_right : _ ≤ M) hx)
        intro x hx
        exact this hx
      have hFj : F j ≤ normalizer (M : Set X) := by
        intro f hf
        rw [mem_normalizer_iff]
        intro x
        refine ⟨hconj f hf x, fun h => ?_⟩
        have := hconj f⁻¹ (inv_mem hf) _ h
        simpa [mul_assoc] using this
      have hsup : (W ⊔ ⨆ i ∈ insert j t, F i : Subgroup X) = M ⊔ F j := by
        rw [Finset.iSup_insert, hM]
        ac_rfl
      rw [hsup, Finset.prod_insert hj, Finset.prod_insert hj]
      have h1 := card_sup_mul_card_inf hFj
      have h2 : Nat.card (F j ⊓ W : Subgroup X) ≤ Nat.card (M ⊓ F j : Subgroup X) :=
        Subgroup.card_le_of_le (le_inf (inf_le_right.trans le_sup_left) inf_le_left)
      calc Nat.card (M ⊔ F j : Subgroup X) *
            (Nat.card (F j ⊓ W : Subgroup X) * ∏ i ∈ t, Nat.card (F i ⊓ W : Subgroup X))
          = (Nat.card (M ⊔ F j : Subgroup X) * Nat.card (F j ⊓ W : Subgroup X)) *
            ∏ i ∈ t, Nat.card (F i ⊓ W : Subgroup X) := by ring
        _ ≤ (Nat.card (M ⊔ F j : Subgroup X) * Nat.card (M ⊓ F j : Subgroup X)) *
            ∏ i ∈ t, Nat.card (F i ⊓ W : Subgroup X) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2)
        _ = Nat.card (F j) * (Nat.card M * ∏ i ∈ t, Nat.card (F i ⊓ W : Subgroup X)) := by
            rw [h1]; ring
        _ ≤ Nat.card (F j) * (Nat.card W * ∏ i ∈ t, Nat.card (F i)) :=
            Nat.mul_le_mul_left _ ih
        _ = _ := by ring
  have hLeq : L = W ⊔ ⨆ i ∈ s, F i :=
    le_antisymm hL (sup_le hWL (iSup₂_le hFL))
  rw [hLeq]
  exact key s subset_rfl
end CFSGOutside.GuralnickShumyatsky
