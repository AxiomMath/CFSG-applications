import CFSGOutside.Corpus.Proposition116B
import CFSGOutside.GuralnickShumyatsky.Coprime

/-!
# Generation by centralizers (Guralnick–Shumyatsky, Lemmas 2.2 and 2.3)
-/

namespace CFSGOutside.GuralnickShumyatsky

open Subgroup
open scoped Pointwise commutatorElement

variable {X : Type} [Group X]

theorem CopAct.le_normalizer_of_le {q : ℕ} {G A : Subgroup X} (hA : CopAct q G A)
    {Y : Subgroup X} (hY : Y ≤ A) {b : X} (hb : b ∈ A) : b ∈ normalizer (Y : Set X) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : b * y * b⁻¹ = y := by
      rw [mul_inv_eq_iff_eq_mul]; exact hA.comm b hb y (hY hy)
    rwa [this]
  · intro hy
    have hy' := hY hy
    have hbA : b⁻¹ ∈ A := A.inv_mem hb
    have h2 : b⁻¹ * (b * y * b⁻¹) = (b * y * b⁻¹) * b⁻¹ := hA.comm _ hbA _ hy'
    have : y = b * y * b⁻¹ := by
      calc y = b⁻¹ * (b * y * b⁻¹) * b := by group
        _ = _ := by rw [h2]; group
    rwa [this]

theorem CycQuot.card_le [Finite X] {q : ℕ} {G A : Subgroup X} (hA : CopAct q G A) {Y : Subgroup X}
    (hY : CycQuot A Y) : Nat.card A ≤ q * Nat.card Y := by
  obtain ⟨hYA, g, hg, hAg⟩ := hY
  have hgn : zpowers g ≤ normalizer (Y : Set X) := by
    rw [zpowers_le]; exact hA.le_normalizer_of_le hYA hg
  have hset : (↑(zpowers g ⊔ Y) : Set X) = (zpowers g : Set X) * (Y : Set X) :=
    coe_mul_of_left_le_normalizer_right _ _ hgn
  have hsub : (A : Set X) ⊆ (zpowers g : Set X) * (Y : Set X) := by
    rw [← hset]; intro x hx; rw [sup_comm] at hAg; exact hAg hx
  have hq : 0 < q := hA.prime.pos
  have h1 : Nat.card A ≤ Nat.card ((zpowers g : Set X) * (Y : Set X)) :=
    Nat.card_mono (Set.toFinite _) hsub
  have h2 := Set.natCard_mul_le (s := (zpowers g : Set X)) (t := (Y : Set X))
  have h3 : Nat.card (zpowers g) ≤ q := by
    rw [Nat.card_zpowers]; exact orderOf_le_of_pow_eq_one hq (hA.exp g hg)
  have h4 : Nat.card ((zpowers g : Set X)) ≤ q := h3
  calc Nat.card A ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ q * Nat.card Y := Nat.mul_le_mul_right _ h4

theorem CycQuot.exists_ne_one_inf [Finite X] {q : ℕ} {G A : Subgroup X} (hA : CopAct q G A)
    (hA3 : q ^ 3 ≤ Nat.card A) {Y Y' : Subgroup X} (hY : CycQuot A Y) (hY' : CycQuot A Y') :
    ∃ a ∈ Y ⊓ Y', a ≠ 1 := by
  by_contra hcon
  have hbot : ∀ a ∈ Y ⊓ Y', a = 1 := fun a ha => by
    by_contra hne; exact hcon ⟨a, ha, hne⟩
  have h1 := hY.card_le hA
  have h1' := hY'.card_le hA
  have hinj : Function.Injective
      (fun p : Y × Y' => (⟨(p.1 : X) * p.2, mul_mem (hY.1 p.1.2) (hY'.1 p.2.2)⟩ : A)) := by
    rintro ⟨⟨y1, h1y⟩, ⟨z1, h1z⟩⟩ ⟨⟨y2, h2y⟩, ⟨z2, h2z⟩⟩ h
    simp only [Subtype.mk.injEq] at h
    have e1 : y2⁻¹ * y1 = z2 * z1⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, h]; group
    have hm : y2⁻¹ * y1 ∈ Y ⊓ Y' :=
      ⟨mul_mem (Y.inv_mem h2y) h1y, e1 ▸ mul_mem h2z (Y'.inv_mem h1z)⟩
    have := hbot _ hm
    have hy : y1 = y2 := by
      rw [inv_mul_eq_one] at this; exact this.symm
    have hz : z1 = z2 := by
      subst hy
      have := mul_left_cancel h
      exact this.symm ▸ rfl
    subst hy; subst hz; rfl
  have h2 := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod] at h2
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hq2 := hA.prime.two_le
  have : Nat.card A * Nat.card A ≤ q ^ 2 * Nat.card A := by
    calc Nat.card A * Nat.card A ≤ (q * Nat.card Y) * (q * Nat.card Y') :=
          Nat.mul_le_mul h1 h1'
      _ = q ^ 2 * (Nat.card Y * Nat.card Y') := by ring
      _ ≤ q ^ 2 * Nat.card A := Nat.mul_le_mul_left _ h2
  have h5 : Nat.card A ≤ q ^ 2 := Nat.le_of_mul_le_mul_right this hApos
  have : q ^ 2 < q ^ 3 := Nat.pow_lt_pow_right hq2 (by norm_num)
  omega

/-- Conjugation action of a subgroup normalizing `H` on `H`. -/
def conjAction {H A : Subgroup X} (h : A ≤ normalizer (H : Set X)) :
    MulDistribMulAction ↥A ↥H where
  smul a b := ⟨a * b * a⁻¹, (mem_normalizer_iff.mp (h a.2) b).mp b.2⟩
  one_smul b := Subtype.ext (by
    show ((1 : ↥A) : X) * b.1 * ((1 : ↥A) : X)⁻¹ = b.1
    simp)
  mul_smul x y b := Subtype.ext (by
    show ((x * y : ↥A) : X) * b.1 * ((x * y : ↥A) : X)⁻¹ = x.1 * (y.1 * b.1 * y.1⁻¹) * x.1⁻¹
    simp [mul_assoc])
  smul_mul r x y := Subtype.ext (by
    show r.1 * (x.1 * y.1) * r.1⁻¹ = r.1 * x.1 * r.1⁻¹ * (r.1 * y.1 * r.1⁻¹)
    group)
  smul_one r := Subtype.ext (by
    show r.1 * (1 : X) * r.1⁻¹ = 1
    simp)

/-- Guralnick–Shumyatsky, Lemma 2.2: `H = ⟨C_H(Y) | A/Y cyclic⟩`. -/
theorem iSup_cenS_eq [CFSGOutside.Corpus.Proposition116B.{0, 0}] [Finite X] {q : ℕ}
    {H A : Subgroup X} (hA : CopAct q H A)
    (hA2 : q ^ 2 ≤ Nat.card A) : (⨆ (Y : Subgroup X) (_ : CycQuot A Y), cenS H Y) = H := by
  apply le_antisymm
  · exact iSup₂_le fun Y _ => inf_le_left
  haveI : Fact q.Prime := ⟨hA.prime⟩
  letI cg : CommGroup ↥A :=
    { (inferInstance : Group ↥A) with mul_comm := fun a b => Subtype.ext (hA.comm _ a.2 _ b.2) }
  letI act : MulDistribMulAction ↥A ↥H := conjAction hA.norm
  haveI : Fact (IsPGroup q ↥A) := ⟨fun g => ⟨1, Subtype.ext (by
    simpa using hA.exp g.1 g.2)⟩⟩
  have hcop : Nat.Coprime q (Nat.card H) := (hA.prime.coprime_iff_not_dvd).2 hA.coprime
  have hncyc : ¬ IsCyclic ↥A := by
    intro hc
    obtain ⟨g, hg⟩ := hc.exists_generator
    have h1 := orderOf_eq_card_of_forall_mem_zpowers hg
    have h2 : orderOf g ≤ q := orderOf_le_of_pow_eq_one hA.prime.pos (Subtype.ext (by
      simpa using hA.exp g.1 g.2))
    have : q < q ^ 2 := by nlinarith [hA.prime.two_le]
    omega
  have key := CFSGOutside.Corpus.Proposition116B.proposition_1_16_b (G := ↥H) (A := ↥A) q hcop hncyc
  have hH : (⊤ : Subgroup ↥H).map H.subtype = H := by rw [Subgroup.map_top, H.range_subtype]
  refine hH.symm.le.trans ?_
  rw [← key, Subgroup.map_iSup]
  refine iSup_le fun Y => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hY => ?_
  have hcq : CycQuot A (Y.map A.subtype) := by
    refine ⟨Subgroup.map_subtype_le Y, ?_⟩
    obtain ⟨c, hc⟩ := hY.exists_generator
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    refine ⟨g.1, g.2, fun x hx => ?_⟩
    obtain ⟨k, hk⟩ := hc (QuotientGroup.mk ⟨x, hx⟩)
    have hk' : (QuotientGroup.mk (g ^ (k : ℤ)) : ↥A ⧸ Y) = QuotientGroup.mk ⟨x, hx⟩ := by
      rw [← hk]; simp
    rw [QuotientGroup.eq] at hk'
    have hxe : x = g.1 ^ k * ((g ^ (k : ℤ))⁻¹ * ⟨x, hx⟩ : ↥A).1 := by
      simp
    rw [hxe, sup_comm]
    exact mul_mem_sup (zpow_mem_zpowers _ _) (mem_map.2 ⟨_, hk', rfl⟩)
  refine le_iSup₂_of_le (Y.map A.subtype) hcq ?_
  rintro _ ⟨h, hfix, rfl⟩
  refine ⟨h.2, mem_centralizer_iff.mpr ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have := congrArg Subtype.val (MulAction.mem_fixedPoints.mp hfix ⟨y, hy⟩)
  change y.1 * h.1 = h.1 * y.1
  change y.1 * h.1 * y.1⁻¹ = h.1 at this
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this

theorem cenS_le_cen {Y : Subgroup X} {a : X} (ha : a ∈ Y) (K : Subgroup X) :
    cenS K Y ≤ cen K a :=
  inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.2 ha))

theorem comm_cenS_le [Finite X] {q : ℕ} {G A : Subgroup X} (hA : CopAct q G A)
    (hA3 : q ^ 3 ≤ Nat.card A) {Y Y' : Subgroup X} (hY : CycQuot A Y) (hY' : CycQuot A Y')
    (N G' : Subgroup X) :
    ⁅cenS N Y, cenS G' Y'⁆ ≤ ⨆ (a : X) (_ : a ∈ A) (_ : a ≠ 1), ⁅cen N a, cen G' a⁆ := by
  obtain ⟨a, ha, hne⟩ := CycQuot.exists_ne_one_inf hA hA3 hY hY'
  have haA : a ∈ A := hY.1 (mem_inf.1 ha).1
  exact (commutator_mono (cenS_le_cen (mem_inf.1 ha).1 N) (cenS_le_cen (mem_inf.1 ha).2 G')).trans
    (le_iSup₂_of_le a haA (le_iSup_of_le hne le_rfl))

theorem conj_mem_cen {A K : Subgroup X} (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {b a x : X}
    (hb : b ∈ A) (ha : a ∈ A) (hbK : b ∈ normalizer (K : Set X)) (hx : x ∈ cen K a) :
    b * x * b⁻¹ ∈ cen K a := by
  refine ⟨(mem_normalizer_iff.1 hbK x).1 hx.1, mem_centralizer_iff.2 ?_⟩
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  have e1 : h * x = x * h := mem_centralizer_iff.1 hx.2 h rfl
  have hab : Commute h b := hcomm h ha b hb
  have e2 : Commute h b⁻¹ := hab.inv_right
  calc h * (b * x * b⁻¹) = (h * b) * x * b⁻¹ := by group
    _ = b * (h * x) * b⁻¹ := by rw [hab.eq]; group
    _ = b * x * (h * b⁻¹) := by rw [e1]; group
    _ = b * x * (b⁻¹ * h) := by rw [e2.eq]
    _ = b * x * b⁻¹ * h := by group

theorem comm_mul_right (x g h : X) : ⁅x, g * h⁆ = ⁅x, g⁆ * (g * ⁅x, h⁆ * g⁻¹) := by
  simp only [commutatorElement_def]; group
theorem comm_inv_right (x g : X) : ⁅x, g⁻¹⁆ = g⁻¹ * ⁅x, g⁆⁻¹ * (g⁻¹)⁻¹ := by
  simp only [commutatorElement_def]; group
theorem comm_mul_left (x y g : X) : ⁅x * y, g⁆ = ⁅x, y * g * y⁻¹⁆ * ⁅y, g⁆ := by
  simp only [commutatorElement_def]; group
theorem comm_inv_left (x g : X) : ⁅x⁻¹, g⁆ = (⁅x, x⁻¹ * g * (x⁻¹)⁻¹⁆)⁻¹ := by
  simp only [commutatorElement_def]; group
theorem comm_one_right (x : X) : ⁅x, (1 : X)⁆ = 1 := by
  simp only [commutatorElement_def]; group
theorem comm_one_left (x : X) : ⁅(1 : X), x⁆ = 1 := by
  simp only [commutatorElement_def]; group

/-- Guralnick–Shumyatsky, Lemma 2.3 (first part): `[N, G] = ⟨[C_N(a), C_G(a)] | a ∈ A#⟩`. -/
theorem commutator_eq_iSup [CFSGOutside.Corpus.Proposition116B.{0, 0}]
    [Finite X] {q : ℕ} {G A : Subgroup X} (hA : CopAct q G A)
    (hA3 : q ^ 3 ≤ Nat.card A) {N : Subgroup X} (hNG : N ≤ G)
    (hGN : G ≤ normalizer (N : Set X)) (hAN : A ≤ normalizer (N : Set X)) :
    ⁅N, G⁆ = ⨆ (a : X) (_ : a ∈ A) (_ : a ≠ 1), ⁅cen N a, cen G a⁆ := by
  set S : Subgroup X := ⨆ (a : X) (_ : a ∈ A) (_ : a ≠ 1), ⁅cen N a, cen G a⁆ with hS
  have hq3 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right hA.prime.pos (by norm_num)
  have hA2 : q ^ 2 ≤ Nat.card A := hq3.trans hA3
  have hNN : ⁅N, G⁆ ≤ N := by
    rw [← le_normalizer_iff_commutator_le_left]; exact hGN
  have hSle : S ≤ ⁅N, G⁆ :=
    iSup_le fun a => iSup_le fun _ => iSup_le fun _ => commutator_mono inf_le_left inf_le_left
  apply le_antisymm _ hSle
  have hSG : S ≤ G := hSle.trans (commutator_le_of_le hNG le_rfl)
  have hSN : S ≤ N := hSle.trans hNN
  -- A normalizes S
  have hfwd : ∀ b ∈ A, ∀ s ∈ S, b * s * b⁻¹ ∈ S := by
    intro b hb
    have hbN : b ∈ normalizer (N : Set X) := hAN hb
    have hbG : b ∈ normalizer (G : Set X) := hA.norm hb
    have : S.map (MulAut.conj b).toMonoidHom ≤ S := by
      rw [hS]
      simp only [Subgroup.map_iSup]
      refine iSup_le fun a => iSup_le fun ha => iSup_le fun hne => ?_
      rw [Subgroup.map_commutator]
      refine le_iSup₂_of_le a ha (le_iSup_of_le hne (commutator_mono ?_ ?_))
      · rintro _ ⟨x, hx, rfl⟩
        exact conj_mem_cen hA.comm hb ha hbN hx
      · rintro _ ⟨x, hx, rfl⟩
        exact conj_mem_cen hA.comm hb ha hbG hx
    intro s hs
    exact this ⟨s, hs, rfl⟩
  have hAS : A ≤ normalizer (S : Set X) := by
    intro b hb
    rw [mem_normalizer_iff]
    intro s
    refine ⟨fun hs => hfwd b hb s hs, fun h => ?_⟩
    have := hfwd b⁻¹ (A.inv_mem hb) _ h
    simpa [mul_assoc] using this
  have hcopS : CopAct q S A :=
    ⟨hA.prime, hAS, fun hd => hA.coprime (hd.trans (Subgroup.card_dvd_of_le hSG)), hA.comm,
      hA.exp⟩
  have hcopN : CopAct q N A :=
    ⟨hA.prime, hAN, fun hd => hA.coprime (hd.trans (Subgroup.card_dvd_of_le hNG)), hA.comm,
      hA.exp⟩
  have hSgen := iSup_cenS_eq hcopS hA2
  have hGgen := iSup_cenS_eq hA hA2
  have hNgen := iSup_cenS_eq hcopN hA2
  -- G normalizes S
  have hGS : G ≤ normalizer (S : Set X) := by
    refine hGgen.symm.le.trans (iSup₂_le fun Y' hY' => ?_)
    intro x hx
    have hxG : x ∈ G := hx.1
    have hfw : ∀ x ∈ cenS G Y', ∀ s ∈ S, x * s * x⁻¹ ∈ S := by
      intro x hx
      have : S ≤ S.comap (MulAut.conj x).toMonoidHom := by
        refine hSgen.symm.le.trans (iSup₂_le fun Y hY => ?_)
        intro s hs
        have hs' : s ∈ S := hs.1
        have hc : ⁅x, s⁆ ∈ S := by
          have h1 : ⁅x, s⁆ ∈ ⁅cenS G Y', cenS N Y⁆ :=
            commutator_mem_commutator hx ⟨hSN hs.1, hs.2⟩
          rw [commutator_comm] at h1
          exact comm_cenS_le hA hA3 hY hY' N G h1
        show x * s * x⁻¹ ∈ S
        have : x * s * x⁻¹ = ⁅x, s⁆ * s := by simp only [commutatorElement_def]; group
        rw [this]; exact mul_mem hc hs'
      intro s hs
      exact this hs
    rw [mem_normalizer_iff]
    intro s
    refine ⟨fun hs => hfw x hx s hs, fun h => ?_⟩
    have hx' : x⁻¹ ∈ cenS G Y' := (cenS G Y').inv_mem hx
    have := hfw x⁻¹ hx' _ h
    simpa [mul_assoc] using this
  -- final
  have hA1 : ∀ Y, CycQuot A Y → ∀ x ∈ cenS N Y, ∀ g ∈ G, ⁅x, g⁆ ∈ S := by
    intro Y hY x hx
    let Q : Subgroup X :=
      { carrier := {g | g ∈ G ∧ ⁅x, g⁆ ∈ S}
        mul_mem' := by
          rintro g h ⟨hgG, hg⟩ ⟨hhG, hh⟩
          refine ⟨mul_mem hgG hhG, ?_⟩
          rw [comm_mul_right x g h]
          exact mul_mem hg ((mem_normalizer_iff.1 (hGS hgG) _).1 hh)
        one_mem' := ⟨one_mem _, by rw [comm_one_right]; exact one_mem _⟩
        inv_mem' := by
          rintro g ⟨hgG, hg⟩
          refine ⟨inv_mem hgG, ?_⟩
          rw [comm_inv_right x g]
          exact (mem_normalizer_iff.1 (hGS (inv_mem hgG)) _).1 (inv_mem hg) }
    have hGQ : G ≤ Q := by
      refine hGgen.symm.le.trans (iSup₂_le fun Y' hY' => ?_)
      intro g hg
      exact ⟨hg.1, comm_cenS_le hA hA3 hY hY' N G (commutator_mem_commutator hx hg)⟩
    intro g hg
    exact (hGQ hg).2
  let R : Subgroup X :=
    { carrier := {x | x ∈ N ∧ ∀ g ∈ G, ⁅x, g⁆ ∈ S}
      mul_mem' := by
        rintro x y ⟨hxN, hx⟩ ⟨hyN, hy⟩
        refine ⟨mul_mem hxN hyN, fun g hg => ?_⟩
        rw [comm_mul_left x y g]
        exact mul_mem (hx _ (mul_mem (mul_mem (hNG hyN) hg) (inv_mem (hNG hyN)))) (hy g hg)
      one_mem' := ⟨one_mem _, fun g _ => by rw [comm_one_left]; exact one_mem _⟩
      inv_mem' := by
        rintro x ⟨hxN, hx⟩
        refine ⟨inv_mem hxN, fun g hg => ?_⟩
        rw [comm_inv_left x g]
        exact inv_mem (hx _ (mul_mem (mul_mem (inv_mem (hNG hxN)) hg) (inv_mem (inv_mem (hNG hxN))))) }
  have hNR : N ≤ R := by
    refine hNgen.symm.le.trans (iSup₂_le fun Y hY => ?_)
    intro x hx
    exact ⟨hx.1, hA1 Y hY x hx⟩
  exact commutator_le.2 fun n hn g hg => (hNR hn).2 g hg

end CFSGOutside.GuralnickShumyatsky
