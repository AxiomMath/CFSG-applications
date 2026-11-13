import CFSGOutside.AOVTame.BlockTools

/-!
# AOV tameness: splitting `κ` for a product of powers (AOV Theorem 3.6)

Let `G = ∏_{i < n} H_i^{ι_i}` with Sylow subgroup `∏_i S_i^{ι_i}`, `S_i ≠ 1`, and `κ_{H_i}` split.
Assume every `α ∈ Aut_typ^I(L(G))` permutes the coordinate subgroups within each block
(`StableAll`). Then `κ_G` splits. The proof is by induction on `n`, writing
`G = H_0^{ι_0} × ∏_{i ≥ 1} H_i^{ι_i}` and using `split_two` with the wreath case `wreath_split`
for the first factor; the hypotheses for the factors come from `Φ(α, Id)` and `Φ(Id, γ)`.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

attribute [local instance] Nat.fact_prime_two

/-- A block `H^ι` with a Sylow subgroup `S` of `H`. -/
structure Blk where
  ι : Type
  [fι : Fintype ι]
  [dι : DecidableEq ι]
  H : Type
  [gH : Group H]
  [fH : Finite H]
  S : Sylow 2 H

attribute [instance] Blk.fι Blk.dι Blk.gH Blk.fH

namespace Blk

/-- `H^ι`. -/
abbrev K (b : Blk) : Type := b.ι → b.H

/-- `S^ι`. -/
noncomputable abbrev T (b : Blk) : Sylow 2 b.K := piSylow b.ι b.S

end Blk

/-- `∏_i H_i^{ι_i}`. -/
abbrev PG {n : ℕ} (bs : Fin n → Blk) : Type := ∀ i, (bs i).K

/-- `∏_i S_i^{ι_i}`. -/
noncomputable abbrev PT {n : ℕ} (bs : Fin n → Blk) : Sylow 2 (PG bs) := piSylowD (fun i => (bs i).T)

variable {n : ℕ}

lemma mem_PT {bs : Fin n → Blk} {t : PG bs} :
    t ∈ (PT bs : Subgroup (PG bs)) ↔ ∀ i x, t i x ∈ ((bs i).S : Subgroup (bs i).H) := by
  rw [mem_piSylowD]
  simp only [Blk.T, coe_piSylow, mem_piSub]

lemma single_mem (bs : Fin n → Blk) (i : Fin n) (x : (bs i).ι) {s : (bs i).H}
    (hs : s ∈ ((bs i).S : Subgroup (bs i).H)) :
    (Pi.mulSingle i (Pi.mulSingle x s) : PG bs) ∈ (PT bs : Subgroup (PG bs)) := by
  rw [mem_PT]
  intro j y
  by_cases hj : j = i
  · subst hj
    by_cases hy : y = x
    · subst hy; simpa using hs
    · simp [Pi.mulSingle_eq_of_ne hy]
  · simp [Pi.mulSingle_eq_of_ne hj]

/-- Every `α` permutes the coordinate subgroups within each block. -/
def StableAll (bs : Fin n → Blk) : Prop :=
  ∀ (α : LAut 2 (PT bs : Subgroup (PG bs))) (hα : α ∈ autTypI 2 (PT bs : Subgroup (PG bs)))
    (i : Fin n) (x : (bs i).ι), ∃ x' : (bs i).ι, ∀ (s : (bs i).H)
      (hs : s ∈ ((bs i).S : Subgroup (bs i).H)), ∃ s' : (bs i).H,
        ((betaFun hα ⟨_, single_mem bs i x hs⟩ : _) : PG bs) = Pi.mulSingle i (Pi.mulSingle x' s')

/-- `β(α)` preserves the support condition `t_j = 1` for `j ∉ I`. -/
lemma stable_supp {bs : Fin n → Blk} (hst : StableAll bs) {α : LAut 2 (PT bs : Subgroup (PG bs))}
    (hα : α ∈ autTypI 2 (PT bs : Subgroup (PG bs))) (I : Set (Fin n)) {t : PG bs}
    (ht : t ∈ (PT bs : Subgroup (PG bs))) (hI : ∀ j ∉ I, t j = 1) :
    ∀ j ∉ I, ((betaFun hα ⟨t, ht⟩ : _) : PG bs) j = 1 := by
  let D : Subgroup (PG bs) := Subgroup.pi Iᶜ (fun _ => ⊥)
  let K' : Subgroup (PT bs : Subgroup (PG bs)) :=
    D.comap ((PT bs : Subgroup (PG bs)).subtype.comp (beta hα).toMonoidHom)
  let K : Subgroup (PG bs) := K'.map (PT bs : Subgroup (PG bs)).subtype
  have memK : ∀ (u : PG bs) (hu : u ∈ (PT bs : Subgroup (PG bs))),
      (∀ j ∉ I, ((betaFun hα ⟨u, hu⟩ : _) : PG bs) j = 1) → u ∈ K := by
    intro u hu h
    refine ⟨⟨u, hu⟩, ?_, rfl⟩
    exact (mem_pi _).2 fun j hj => (mem_bot).2 (h j hj)
  have hgen : ∀ (j : Fin n) (x : (bs j).ι) (s : (bs j).H)
      (hs : s ∈ ((bs j).S : Subgroup (bs j).H)), j ∈ I →
        (Pi.mulSingle j (Pi.mulSingle x s) : PG bs) ∈ K := by
    intro j x s hs hj
    obtain ⟨x', hx'⟩ := hst α hα j x
    obtain ⟨s', hs'⟩ := hx' s hs
    refine memK _ (single_mem bs j x hs) fun k hk => ?_
    rw [hs']
    have : k ≠ j := fun e => hk (e ▸ hj)
    simp [Pi.mulSingle_eq_of_ne this]
  have htK : t ∈ K := by
    rw [← Finset.noncommProd_mulSingle t]
    apply Subgroup.noncommProd_mem
    intro j _
    by_cases hj : j ∈ I
    · have hc : t j ∈ K.comap (MonoidHom.mulSingle (fun i => (bs i).K) j) := by
        rw [← Finset.noncommProd_mulSingle (t j)]
        apply Subgroup.noncommProd_mem
        intro x _
        exact hgen j x (t j x) ((mem_PT.1 ht) j x) hj
      exact hc
    · rw [hI j hj, Pi.mulSingle_one]; exact one_mem _
  obtain ⟨t', ht', e⟩ := htK
  have : t' = ⟨t, ht⟩ := Subtype.ext e
  subst this
  intro j hj
  exact (mem_bot).1 ((mem_pi _).1 ht' j hj)

section Cons
variable (bs : Fin (n + 1) → Blk)

/-- `H_0^{ι_0} × ∏_{i ≥ 1} H_i^{ι_i} ≃ ∏_i H_i^{ι_i}`. -/
def consMul : (bs 0).K × PG (fun i => bs i.succ) ≃* PG bs where
  toEquiv := Fin.consEquiv (fun i => (bs i).K)
  map_mul' x y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Fin.consEquiv]
    · simp [Fin.consEquiv]

lemma consMul_apply (x : (bs 0).K × PG (fun i => bs i.succ)) :
    consMul bs x = Fin.cons x.1 x.2 := rfl

lemma consMul_zero (x : (bs 0).K × PG (fun i => bs i.succ)) : consMul bs x 0 = x.1 := by
  simp [consMul_apply]

lemma consMul_succ (x : (bs 0).K × PG (fun i => bs i.succ)) (j : Fin n) :
    consMul bs x j.succ = x.2 j := by
  simp [consMul_apply]

lemma consMul_inl (a : (bs 0).K) : consMul bs (a, 1) = Pi.mulSingle 0 a := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [consMul_zero, Pi.mulSingle_eq_same]
  · rw [consMul_succ, Pi.mulSingle_eq_of_ne (Fin.succ_ne_zero j)]; rfl

lemma consMul_inr {i : Fin n} (b : (bs i.succ).K) :
    consMul bs (1, Pi.mulSingle i b) = Pi.mulSingle i.succ b := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · rw [consMul_zero, Pi.mulSingle_eq_of_ne (Fin.succ_ne_zero i).symm]
  · rw [consMul_succ]
    dsimp only
    by_cases hj : j = i
    · subst hj; rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne (fun h => hj (Fin.succ_injective _ h))]

lemma map_consMul : ((prodSylow (bs 0).T (PT (fun i => bs i.succ)) : Sylow 2 _) :
    Subgroup ((bs 0).K × PG (fun i => bs i.succ))).map (consMul bs).toMonoidHom = PT bs := by
  ext t
  constructor
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    rw [mem_piSylowD]
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change consMul bs (a, b) 0 ∈ _
      rw [consMul_zero]; exact ha
    · change consMul bs (a, b) j.succ ∈ _
      rw [consMul_succ]; exact (mem_piSylowD.1 hb) j
  · intro ht
    refine ⟨(consMul bs).symm t, ⟨?_, ?_⟩, by simp⟩
    · have := (mem_piSylowD.1 ht) 0
      rwa [← (consMul bs).apply_symm_apply t, consMul_zero] at this
    · show _ ∈ ((PT (fun i => bs i.succ) : Sylow 2 _) : Subgroup (PG (fun i => bs i.succ)))
      rw [mem_piSylowD]
      intro j
      have := (mem_piSylowD.1 ht) j.succ
      rwa [← (consMul bs).apply_symm_apply t, consMul_succ] at this

lemma consMul_mem {x : (bs 0).K × PG (fun i => bs i.succ)}
    (hx : x ∈ ((prodSylow (bs 0).T (PT (fun i => bs i.succ)) : Sylow 2 _) :
      Subgroup ((bs 0).K × PG (fun i => bs i.succ)))) :
    consMul bs x ∈ (PT bs : Subgroup (PG bs)) :=
  map_consMul bs ▸ ⟨x, hx, rfl⟩

end Cons

section Step
variable {bs : Fin (n + 1) → Blk} (hst : StableAll bs)
include hst

/-- `β(α)` preserves the two factors of `H_0^{ι_0} × ∏_{i ≥ 1} H_i^{ι_i}`. -/
lemma presFactors_of_stable {α : LAut 2 ((prodSylow (bs 0).T (PT (fun i => bs i.succ)) :
      Sylow 2 _) : Subgroup ((bs 0).K × PG (fun i => bs i.succ)))}
    (hα : α ∈ autTypI 2 ((prodSylow (bs 0).T (PT (fun i => bs i.succ)) : Sylow 2 _) :
      Subgroup ((bs 0).K × PG (fun i => bs i.succ)))) : PresFactors hα := by
  have hα' := conjIso_mem (consMul bs) (map_consMul bs) hα
  constructor
  · intro a ha
    have hx := mem_prodSylow (SB := PT (fun i => bs i.succ)) ha (one_mem _)
    have h1 := betaFun_conjIso (consMul bs) (map_consMul bs) hα ⟨_, hx⟩ (consMul_mem bs hx)
    have hsupp : ∀ j ∉ ({0} : Set (Fin (n + 1))), consMul bs (a, 1) j = 1 := by
      intro j hj
      rw [consMul_inl, Pi.mulSingle_eq_of_ne (by simpa using hj)]
    have h2 := stable_supp hst hα' {0} (consMul_mem bs hx) hsupp
    funext j
    have := h2 j.succ (by simp [Fin.succ_ne_zero])
    rw [h1, consMul_succ] at this
    exact this
  · intro b hb
    have hx := mem_prodSylow (SA := (bs 0).T) (one_mem _) hb
    have h1 := betaFun_conjIso (consMul bs) (map_consMul bs) hα ⟨_, hx⟩ (consMul_mem bs hx)
    have hsupp : ∀ j ∉ {j : Fin (n + 1) | j ≠ 0}, consMul bs (1, b) j = 1 := by
      intro j hj
      simp only [Set.mem_setOf_eq, not_not] at hj
      subst hj
      rw [consMul_zero]
    have h2 := stable_supp hst hα' {j | j ≠ 0} (consMul_mem bs hx) hsupp
    have := h2 0 (by simp)
    rw [h1, consMul_zero] at this
    exact this

/-- `β(α₀)` maps each coordinate subgroup of the first block into a coordinate subgroup. -/
lemma coord_spec {α₀ : LAut 2 (((bs 0).T : Sylow 2 (bs 0).K) : Subgroup (bs 0).K)}
    (hα₀ : α₀ ∈ autTypI 2 (((bs 0).T : Sylow 2 (bs 0).K) : Subgroup (bs 0).K)) (x : (bs 0).ι) :
    ∃ x' : (bs 0).ι, ∀ (s : (bs 0).H) (hs : s ∈ ((bs 0).S : Subgroup (bs 0).H)), ∃ s',
      betaPi hα₀ (Pi.mulSingle x s) (mulSingle_mem_piSub hs) = Pi.mulSingle x' s' := by
  have hα₁ := phiAut_mem (SB := PT (fun i => bs i.succ)) hα₀
  have hα' := conjIso_mem (consMul bs) (map_consMul bs) hα₁
  obtain ⟨x', hx'⟩ := hst _ hα' 0 x
  refine ⟨x', fun s hs => ?_⟩
  obtain ⟨s', hs'⟩ := hx' s hs
  refine ⟨s', ?_⟩
  have hmA : Pi.mulSingle x s ∈ (((bs 0).T : Sylow 2 (bs 0).K) : Subgroup (bs 0).K) :=
    mulSingle_mem_piSub hs
  have hx := mem_prodSylow (SB := PT (fun i => bs i.succ)) hmA (one_mem _)
  have h1 := betaFun_conjIso (consMul bs) (map_consMul bs) hα₁ ⟨_, hx⟩ (consMul_mem bs hx)
  have h2 := betaFun_phiAut (SB := PT (fun i => bs i.succ)) hα₀ hmA (one_mem _)
  have h3 : ((betaFun hα' ⟨_, single_mem bs 0 x hs⟩ : _) : PG bs) =
      consMul bs ((betaFun hα₀ ⟨Pi.mulSingle x s, hmA⟩ : (bs 0).K), 1) := by
    calc ((betaFun hα' ⟨_, single_mem bs 0 x hs⟩ : _) : PG bs) =
        ((betaFun hα' ⟨consMul bs (Pi.mulSingle x s, 1), consMul_mem bs hx⟩ : _) : PG bs) :=
          congrArg (fun z => ((betaFun hα' z : _) : PG bs))
            (Subtype.ext (consMul_inl bs (Pi.mulSingle x s)).symm)
      _ = _ := h1
      _ = _ := by rw [h2]
  rw [hs', consMul_inl] at h3
  have := congrFun h3 0
  simp only [Pi.mulSingle_eq_same] at this
  exact this.symm

/-- **`hperm` for the first block.** -/
lemma hperm_of_stable (hS : ((bs 0).S : Subgroup (bs 0).H) ≠ ⊥)
    (α₀ : LAut 2 (((bs 0).T : Sylow 2 (bs 0).K) : Subgroup (bs 0).K))
    (hα₀ : α₀ ∈ autTypI 2 (((bs 0).T : Sylow 2 (bs 0).K) : Subgroup (bs 0).K)) :
    ∃ σ, PermBy hα₀ σ := by
  obtain ⟨⟨s₀, hs₀⟩, hs₁⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hS
  have hs₁' : s₀ ≠ 1 := fun h => hs₁ (Subtype.ext h)
  choose f hf using coord_spec hst hα₀
  choose g hg using coord_spec hst (inv_mem hα₀)
  -- `β⁻¹ β = id` pins down the coordinates
  have key : ∀ (α₁ α₂ : LAut 2 (((bs 0).T : Sylow 2 (bs 0).K) : Subgroup (bs 0).K))
      (h₁ : α₁ ∈ autTypI 2 _) (h₂ : α₂ ∈ autTypI 2 _)
      (hinv : ∀ y, betaFun h₂ (betaFun h₁ y) = y)
      (f₁ f₂ : (bs 0).ι → (bs 0).ι)
      (hf₁ : ∀ x, ∀ (s : (bs 0).H) (hs : s ∈ ((bs 0).S : Subgroup (bs 0).H)), ∃ s',
        betaPi h₁ (Pi.mulSingle x s) (mulSingle_mem_piSub hs) = Pi.mulSingle (f₁ x) s')
      (hf₂ : ∀ x, ∀ (s : (bs 0).H) (hs : s ∈ ((bs 0).S : Subgroup (bs 0).H)), ∃ s',
        betaPi h₂ (Pi.mulSingle x s) (mulSingle_mem_piSub hs) = Pi.mulSingle (f₂ x) s'),
      ∀ x, f₂ (f₁ x) = x := by
    intro α₁ α₂ h₁ h₂ hinv f₁ f₂ hf₁ hf₂ x
    obtain ⟨s', hs'⟩ := hf₁ x s₀ hs₀
    have hs'S : s' ∈ ((bs 0).S : Subgroup (bs 0).H) := by
      have := (mem_piSub _ _).1 (betaFun h₁ ⟨_, mulSingle_mem_piSub (i := x) hs₀⟩).2 (f₁ x)
      unfold betaPi at hs'
      rw [hs', Pi.mulSingle_eq_same] at this
      exact this
    obtain ⟨s'', hs''⟩ := hf₂ (f₁ x) s' hs'S
    have e1 : betaPi h₂ (Pi.mulSingle (f₁ x) s') (mulSingle_mem_piSub hs'S) = Pi.mulSingle x s₀ := by
      unfold betaPi at hs' ⊢
      have : (⟨Pi.mulSingle (f₁ x) s', mulSingle_mem_piSub hs'S⟩ :
          (((bs 0).T : Sylow 2 (bs 0).K) : Subgroup (bs 0).K)) =
          betaFun h₁ ⟨_, mulSingle_mem_piSub hs₀⟩ := Subtype.ext hs'.symm
      rw [this, hinv]
    rw [e1] at hs''
    by_contra hne
    have := congrFun hs'' x
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (Ne.symm hne)] at this
    exact hs₁' this
  have hgf := key α₀ α₀⁻¹ hα₀ (inv_mem hα₀) (betaFun_inv_aut hα₀) f g hf hg
  have hfg := key α₀⁻¹ α₀ (inv_mem hα₀) hα₀ (betaFun_inv_aut' hα₀) g f hg hf
  exact ⟨⟨f, g, hgf, hfg⟩, fun i x hx => hf i x hx⟩

/-- `StableAll` for the remaining blocks. -/
lemma stableAll_tail : StableAll (fun i => bs i.succ) := by
  intro γ hγ i x
  have hα₁ := phiBAut_mem (SA := (bs 0).T) hγ
  have hα' := conjIso_mem (consMul bs) (map_consMul bs) hα₁
  obtain ⟨x', hx'⟩ := hst _ hα' i.succ x
  refine ⟨x', fun s hs => ?_⟩
  obtain ⟨s', hs'⟩ := hx' s hs
  refine ⟨s', ?_⟩
  have hmB := single_mem (fun i => bs i.succ) i x hs
  have hx := mem_prodSylow (SA := (bs 0).T) (one_mem _) hmB
  have h1 := betaFun_conjIso (consMul bs) (map_consMul bs) hα₁ ⟨_, hx⟩ (consMul_mem bs hx)
  have h2 := betaFun_phiBAut (SA := (bs 0).T) hγ (one_mem _) hmB
  have h3 : ((betaFun hα' ⟨_, single_mem bs i.succ x hs⟩ : _) : PG bs) =
      consMul bs (1, (betaFun hγ ⟨_, hmB⟩ : PG (fun i => bs i.succ))) := by
    calc ((betaFun hα' ⟨_, single_mem bs i.succ x hs⟩ : _) : PG bs) =
        ((betaFun hα' ⟨consMul bs (1, Pi.mulSingle i (Pi.mulSingle x s)), consMul_mem bs hx⟩ :
          _) : PG bs) :=
          congrArg (fun z => ((betaFun hα' z : _) : PG bs))
            (Subtype.ext (consMul_inr bs (i := i) (Pi.mulSingle x s)).symm)
      _ = _ := h1
      _ = _ := by rw [h2]
  rw [hs', ← consMul_inr bs (i := i)] at h3
  have := congrArg Prod.snd ((consMul bs).injective h3)
  exact this.symm

end Step

/-- **The splitting of `κ` for a product of powers.** -/
theorem pi_split : ∀ (n : ℕ) (bs : Fin n → Blk), (∀ i, ((bs i).S : Subgroup (bs i).H) ≠ ⊥) →
    (∀ i, ∃ s : OutTyp 2 ((bs i).S : Subgroup (bs i).H) →* Out (bs i).H,
      (kappa 2 (bs i).S).comp s = MonoidHom.id _) → StableAll bs →
    ∃ s : OutTyp 2 (PT bs : Subgroup (PG bs)) →* Out (PG bs),
      (kappa 2 (PT bs)).comp s = MonoidHom.id _
  | 0, bs, _, _, _ => kappa_split_subsingleton _
  | n + 1, bs, hS, hsp, hst => by
    obtain ⟨sB, hsB⟩ := pi_split n (fun i => bs i.succ) (fun i => hS i.succ) (fun i => hsp i.succ)
      (stableAll_tail hst)
    obtain ⟨s0, hs0⟩ := hsp 0
    have hsA := wreath_split (hS 0) (hperm_of_stable hst (hS 0)) s0 hs0
    have h2 := split_two (fun α hα => presFactors_of_stable hst hα) hsA hsB
    exact kappa_split_mulEquiv (consMul bs) (map_consMul bs) h2

end AndersenOliverVentura.Tame
