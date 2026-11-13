import CFSGOutside.AOVTame.Centric
import CFSGOutside.AndersenOliverVentura.GroupLemmas

/-!
# AOV tameness: Sylow lemmas behind the saturation of `F_T(G)` (BLO2, Proposition 1.3)
-/

namespace AndersenOliverVentura.Tame

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

/-- `exists_conj_le_of_le_sup` relative to a subgroup `M` in which `N` is normal. -/
lemma exists_conj_le_of_le_sup_rel {M N Q R : Subgroup G} (hNM : N ≤ M) (hQM : Q ≤ M)
    (hRM : R ≤ M) (hN : (N.subgroupOf M).Normal) (hQ : IsPGroup p Q) (hR : IsPGroup p R)
    (hidx : ¬ p ∣ Q.relIndex N) (hRQ : R ≤ Q ⊔ N) : ∃ n ∈ N, ∀ r ∈ R, n⁻¹ * r * n ∈ Q := by
  have hidx' : ¬ p ∣ (Q.subgroupOf M).relIndex (N.subgroupOf M) := by
    rw [relIndex_subgroupOf hNM]; exact hidx
  have hRQ' : R.subgroupOf M ≤ Q.subgroupOf M ⊔ N.subgroupOf M := by
    rw [← subgroupOf_sup hQM hNM]
    intro x hx
    exact hRQ hx
  obtain ⟨n, hn, h⟩ := exists_conj_le_of_le_sup (N := N.subgroupOf M) hQ.comap_subtype
    hR.comap_subtype hidx' hRQ'
  refine ⟨n, hn, fun r hr => ?_⟩
  have := h ⟨r, hRM hr⟩ hr
  exact this

/-- `A` is a Sylow `p`-subgroup of `H`. -/
def IsSylowIn (p : ℕ) (A H : Subgroup G) : Prop := A ≤ H ∧ IsPGroup p A ∧ ¬ p ∣ A.relIndex H

/-- A `p`-subgroup `A ≤ H` such that no larger `p`-subgroup of `H` containing `A` has larger order
is Sylow in `H`. -/
lemma isSylowIn_of_card_le {A H : Subgroup G} (hAH : A ≤ H) (hA : IsPGroup p A)
    (h : ∀ U : Subgroup G, U ≤ H → IsPGroup p U → A ≤ U → Nat.card U ≤ Nat.card A) :
    IsSylowIn p A H := by
  refine ⟨hAH, hA, ?_⟩
  obtain ⟨V, hV⟩ := (hA.comap_subtype (K := H)).exists_le_sylow
  have hVA : (V : Subgroup H).map H.subtype ≤ A := by
    have hle : A ≤ (V : Subgroup H).map H.subtype := fun x hx => ⟨⟨x, hAH hx⟩, hV hx, rfl⟩
    have hc := h _ (map_subtype_le _) (V.isPGroup'.map _) hle
    have : (V : Subgroup H).map H.subtype = A := by
      apply le_antisymm _ hle
      intro x hx
      by_contra hxA
      have hlt : A < (V : Subgroup H).map H.subtype := lt_of_le_of_ne hle (fun e => hxA (e ▸ hx))
      have := Subgroup.card_lt_of_lt hlt
      omega
    rw [this]
  have hAV : A.subgroupOf H = V := by
    apply le_antisymm (fun x hx => hV hx)
    intro x hx
    exact hVA ⟨x, hx, rfl⟩
  change ¬ p ∣ (A.subgroupOf H).index
  rw [hAV]
  exact V.not_dvd_index

/-- A `p`-subgroup of `H` has order at most that of a Sylow subgroup of `H`. -/
lemma card_le_of_isSylowIn {A H U : Subgroup G} (hA : IsSylowIn p A H) (hUH : U ≤ H)
    (hU : IsPGroup p U) : Nat.card U ≤ Nat.card A := by
  let A' : Sylow p H := hA.2.1.comap_subtype.toSylow hA.2.2
  obtain ⟨V, hV⟩ := (hU.comap_subtype (K := H)).exists_le_sylow
  have h1 : Nat.card (U.subgroupOf H) ≤ Nat.card V := Subgroup.card_le_of_le hV
  have h2 : Nat.card V = Nat.card A' := by
    rw [V.card_eq_multiplicity, A'.card_eq_multiplicity]
  have h3 : Nat.card (U.subgroupOf H) = Nat.card U :=
    Nat.card_congr (subgroupOfEquivOfLe hUH).toEquiv
  have h4 : Nat.card A' = Nat.card A := Nat.card_congr (subgroupOfEquivOfLe hA.1).toEquiv
  omega

lemma exists_conjSub_le (T : Sylow p G) {U : Subgroup G} (hU : IsPGroup p U) :
    ∃ g : G, conjSub g U ≤ T := by
  obtain ⟨V, hV⟩ := hU.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G V T
  refine ⟨g, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [← hg, Sylow.coe_subgroup_smul]
  exact ⟨x, hV hx, rfl⟩

lemma card_conjSub (g : G) (U : Subgroup G) : Nat.card (conjSub g U) = Nat.card U :=
  Nat.card_congr (equivMapOfInjective U _ (MulAut.conj g).injective).toEquiv.symm

lemma conjSub_mono {g : G} {U V : Subgroup G} (h : U ≤ V) : conjSub g U ≤ conjSub g V := map_mono h

lemma conjSub_normalizer (g : G) (R : Subgroup G) :
    conjSub g (normalizer (R : Set G)) = normalizer (conjSub g R : Set G) := by
  ext y
  rw [mem_conjSub, mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h x
    rw [mem_conjSub, mem_conjSub]
    have := h (g⁻¹ * x * g)
    simp only [mul_assoc, mul_inv_cancel_left] at this ⊢
    convert this using 2 <;> group
  · intro h x
    have := h (g * x * g⁻¹)
    rw [mem_conjSub, mem_conjSub] at this
    convert this using 2 <;> group

lemma conjSub_centralizer (g : G) (R : Subgroup G) :
    conjSub g (centralizer (R : Set G)) = centralizer (conjSub g R : Set G) := by
  ext y
  rw [mem_conjSub, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h x hx
    rw [SetLike.mem_coe, mem_conjSub] at hx
    have := h _ hx
    calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [this]
      _ = y * x := by group
  · intro h x hx
    have := h (g * x * g⁻¹) (by rw [SetLike.mem_coe, mem_conjSub]; simpa [mul_assoc] using hx)
    calc x * (g⁻¹ * y * g) = g⁻¹ * ((g * x * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * x * g⁻¹)) * g := by rw [this]
      _ = g⁻¹ * y * g * x := by group

lemma conjSub_inf (g : G) (U V : Subgroup G) : conjSub g (U ⊓ V) = conjSub g U ⊓ conjSub g V :=
  map_inf_eq _ _ _ (MulAut.conj g).injective

lemma conjSub_inv_conjSub (g : G) (U : Subgroup G) : conjSub g⁻¹ (conjSub g U) = U := by
  rw [conjSub_conjSub, inv_mul_cancel]; ext x; simp [mem_conjSub]

lemma isSylowIn_normalizer (T : Sylow p G) {R : Subgroup G} (hR : R ≤ T)
    (hfn : ∀ g : G, conjSub g R ≤ T →
      Nat.card (normalizer (conjSub g R : Set G) ⊓ (T : Subgroup G) : Subgroup G) ≤
        Nat.card (normalizer (R : Set G) ⊓ (T : Subgroup G) : Subgroup G)) :
    IsSylowIn p (normalizer (R : Set G) ⊓ T) (normalizer (R : Set G)) := by
  apply isSylowIn_of_card_le inf_le_left (T.isPGroup'.to_le inf_le_right)
  intro U hUN hU hAU
  obtain ⟨g, hg⟩ := exists_conjSub_le T hU
  have hRU : R ≤ U := fun x hx => hAU (mem_inf.2 ⟨le_normalizer hx, hR hx⟩)
  have hgR : conjSub g R ≤ T := (conjSub_mono hRU).trans hg
  have h1 : conjSub g U ≤ normalizer (conjSub g R : Set G) ⊓ (T : Subgroup G) :=
    le_inf ((conjSub_mono hUN).trans (conjSub_normalizer g R).le) hg
  calc Nat.card U = Nat.card (conjSub g U) := (card_conjSub g U).symm
    _ ≤ _ := Subgroup.card_le_of_le h1
    _ ≤ _ := hfn g hgR

lemma isSylowIn_centralizer (T : Sylow p G) {R : Subgroup G} (hR : R ≤ T)
    (hfc : ∀ g : G, conjSub g R ≤ T →
      Nat.card (centralizer (conjSub g R : Set G) ⊓ (T : Subgroup G) : Subgroup G) ≤
        Nat.card (centralizer (R : Set G) ⊓ (T : Subgroup G) : Subgroup G)) :
    IsSylowIn p (centralizer (R : Set G) ⊓ T) (centralizer (R : Set G)) := by
  apply isSylowIn_of_card_le inf_le_left (T.isPGroup'.to_le inf_le_right)
  intro U hUC hU hAU
  have hRp : IsPGroup p R := T.isPGroup'.to_le hR
  have hRU : IsPGroup p (R ⊔ U : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hRp hU (fun x hx => by
      rw [mem_normalizer_iff]
      intro y
      have key : ∀ w ∈ centralizer (R : Set G), x * w * x⁻¹ = w := fun w hw => by
        have h := mem_centralizer_iff.1 hw x hx
        calc x * w * x⁻¹ = (x * w) * x⁻¹ := rfl
          _ = (w * x) * x⁻¹ := by rw [h]
          _ = w := by group
      constructor
      · intro hy; rw [key y (hUC hy)]; exact hy
      · intro hy
        have h := mem_centralizer_iff.1 (hUC hy) x hx
        have : x * y * x⁻¹ = y := by
          calc x * y * x⁻¹ = x⁻¹ * (x * (x * y * x⁻¹)) := by group
            _ = x⁻¹ * ((x * y * x⁻¹) * x) := by rw [h]
            _ = y := by group
        rwa [this] at hy)
  obtain ⟨g, hg⟩ := exists_conjSub_le T hRU
  have hgR : conjSub g R ≤ T := (conjSub_mono le_sup_left).trans hg
  have h1 : conjSub g U ≤ centralizer (conjSub g R : Set G) ⊓ (T : Subgroup G) :=
    le_inf ((conjSub_mono hUC).trans (conjSub_centralizer g R).le)
      ((conjSub_mono le_sup_right).trans hg)
  calc Nat.card U = Nat.card (conjSub g U) := (card_conjSub g U).symm
    _ ≤ _ := Subgroup.card_le_of_le h1
    _ ≤ _ := hfc g hgR

lemma relIndex_sup_normal_rel {M N Q : Subgroup G} (hNM : N ≤ M) (hQM : Q ≤ M)
    (hN : (N.subgroupOf M).Normal) : Q.relIndex (Q ⊔ N) = Q.relIndex N := by
  have := relIndex_sup_normal (Q.subgroupOf M) (N.subgroupOf M)
  rwa [← subgroupOf_sup hQM hNM, relIndex_subgroupOf (sup_le hQM hNM),
    relIndex_subgroupOf hNM] at this

lemma centralizer_normal_in_normalizer (R : Subgroup G) :
    ((centralizer (R : Set G)).subgroupOf (normalizer (R : Set G))).Normal := ⟨by
  intro c hc n
  rw [mem_subgroupOf] at hc ⊢
  have h1 : (n : G) * c * (n : G)⁻¹ ∈ conjSub (n : G) (centralizer (R : Set G)) :=
    ⟨c, hc, rfl⟩
  rw [conjSub_centralizer] at h1
  have h2 : conjSub (n : G) R = R := by
    ext x
    rw [mem_conjSub]
    have := (mem_normalizer_iff.1 (inv_mem n.2)) x
    simp only [inv_inv] at this
    exact this.symm
  simp only [coe_mul, coe_inv]
  rwa [h2] at h1⟩

lemma isSylowIn_centralizer_of_normalizer (T : Sylow p G) {R : Subgroup G}
    (hN : IsSylowIn p (normalizer (R : Set G) ⊓ T) (normalizer (R : Set G))) :
    IsSylowIn p (centralizer (R : Set G) ⊓ T) (centralizer (R : Set G)) := by
  set A := normalizer (R : Set G) ⊓ (T : Subgroup G)
  set C := centralizer (R : Set G)
  refine ⟨inf_le_left, T.isPGroup'.to_le inf_le_right, ?_⟩
  have hCN : C ≤ normalizer (R : Set G) := centralizer_le_normalizer _
  have e1 : C ⊓ (T : Subgroup G) = A ⊓ C := by
    apply le_antisymm
    · exact le_inf (le_inf (inf_le_left.trans hCN) inf_le_right) inf_le_left
    · exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
  rw [e1, inf_relIndex_right, ← relIndex_sup_normal_rel hCN inf_le_left
    (centralizer_normal_in_normalizer R)]
  intro hd
  apply hN.2.2
  rw [← relIndex_mul_relIndex A (A ⊔ C) _ le_sup_left (sup_le inf_le_left hCN)]
  exact hd.mul_right _

lemma card_centralizer_le_of_isSylowIn (T : Sylow p G) {R : Subgroup G}
    (hC : IsSylowIn p (centralizer (R : Set G) ⊓ T) (centralizer (R : Set G))) (g : G) :
    Nat.card (centralizer (conjSub g R : Set G) ⊓ (T : Subgroup G) : Subgroup G) ≤
      Nat.card (centralizer (R : Set G) ⊓ (T : Subgroup G) : Subgroup G) := by
  set U := conjSub g⁻¹ (centralizer (conjSub g R : Set G) ⊓ (T : Subgroup G))
  have hU : U ≤ centralizer (R : Set G) := by
    have : conjSub g⁻¹ (centralizer (conjSub g R : Set G)) = centralizer (R : Set G) := by
      rw [conjSub_centralizer, conjSub_inv_conjSub]
    rw [← this]; exact conjSub_mono inf_le_left
  have hUp : IsPGroup p U := (T.isPGroup'.to_le inf_le_right).map _
  rw [← card_conjSub g⁻¹]
  exact card_le_of_isSylowIn hC hU hUp

lemma conjSub_le_normalizer {g : G} {R X : Subgroup G} (h : X ≤ normalizer (R : Set G)) :
    conjSub g X ≤ normalizer (conjSub g R : Set G) := by
  rw [← conjSub_normalizer]; exact conjSub_mono h

/-- The extension step of BLO2, Proposition 1.3 (axiom (II)). -/
lemma exists_extension (T : Sylow p G) {R : Subgroup G} (g : G)
    (hC : IsSylowIn p (centralizer (conjSub g R : Set G) ⊓ T) (centralizer (conjSub g R : Set G)))
    {X : Subgroup G} (hXT : X ≤ T) (hXN : X ≤ normalizer (R : Set G))
    (hX : ∀ x ∈ X, ∃ y ∈ normalizer (conjSub g R : Set G) ⊓ (T : Subgroup G),
      ∀ r ∈ R, g * (x * r * x⁻¹) * g⁻¹ = y * (g * r * g⁻¹) * y⁻¹) :
    ∃ c ∈ centralizer (conjSub g R : Set G), ∀ x ∈ X, (c * g) * x * (c * g)⁻¹ ∈ (T : Subgroup G) := by
  set R' := conjSub g R
  set M := normalizer (R' : Set G)
  set N := centralizer (R' : Set G)
  set Q := M ⊓ (T : Subgroup G)
  have hNM : N ≤ M := centralizer_le_normalizer _
  have hR₀ : conjSub g X ≤ M := conjSub_le_normalizer hXN
  have hQ : IsPGroup p Q := T.isPGroup'.to_le inf_le_right
  have hR₀p : IsPGroup p (conjSub g X) := (T.isPGroup'.to_le hXT).map _
  have hidx : ¬ p ∣ Q.relIndex N := by
    rw [← inf_relIndex_right]
    have : Q ⊓ N = N ⊓ (T : Subgroup G) :=
      le_antisymm (le_inf inf_le_right (inf_le_left.trans inf_le_right))
        (le_inf (le_inf (inf_le_left.trans hNM) inf_le_right) inf_le_left)
    rw [this]; exact hC.2.2
  have hle : conjSub g X ≤ Q ⊔ N := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hX x hx
    have hc : y⁻¹ * (g * x * g⁻¹) ∈ N := by
      rw [mem_centralizer_iff]
      rintro _ ⟨r, hr, rfl⟩
      have := hyx r hr
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply] at this ⊢
      calc g * r * g⁻¹ * (y⁻¹ * (g * x * g⁻¹))
          = y⁻¹ * (y * (g * r * g⁻¹) * y⁻¹) * y * (y⁻¹ * (g * x * g⁻¹)) := by group
        _ = y⁻¹ * (g * (x * r * x⁻¹) * g⁻¹) * y * (y⁻¹ * (g * x * g⁻¹)) := by rw [this]
        _ = y⁻¹ * (g * x * g⁻¹) * (g * r * g⁻¹) := by group
    have : (MulAut.conj g).toMonoidHom x = y * (y⁻¹ * (g * x * g⁻¹)) := by simp
    rw [this]
    exact mul_mem_sup hy hc
  obtain ⟨n, hn, hconj⟩ := exists_conj_le_of_le_sup_rel hNM inf_le_left hR₀
    (centralizer_normal_in_normalizer R') hQ hR₀p hidx hle
  refine ⟨n⁻¹, inv_mem hn, fun x hx => ?_⟩
  have := hconj _ ⟨x, hx, rfl⟩
  have e : n⁻¹ * g * x * (n⁻¹ * g)⁻¹ = n⁻¹ * (MulAut.conj g).toMonoidHom x * n := by simp [mul_assoc]
  rw [e]; exact (mem_inf.1 this).2

end AndersenOliverVentura.Tame
